#include <gcs/constraints/logical.hh>
#include <gcs/exception.hh>
#include <gcs/innards/inference_tracker.hh>
#include <gcs/innards/proofs/proof_logger.hh>
#include <gcs/innards/proofs/proof_model.hh>
#include <gcs/innards/propagators.hh>
#include <gcs/innards/state.hh>

#include <util/overloaded.hh>

#include <optional>

using namespace gcs;
using namespace gcs::innards;

using std::optional;
using std::pair;
using std::string;
using std::unique_ptr;
using std::vector;

namespace
{
    auto to_lits(const vector<IntegerVariableID> & vars) -> Literals
    {
        Literals result;
        result.reserve(vars.size());
        for (auto & v : vars)
            result.emplace_back(v != 0_i);
        return result;
    }

    auto install_and_or_or(Propagators & propagators, const State & initial_state,
        ProofModel * const optional_model,
        const Literals & _lits, const Literal & _full_reif,
        const string & name) -> void
    {
        auto reif_state = initial_state.test_literal(_full_reif);

        if (reif_state == LiteralIs::DefinitelyTrue) {
            // definitely true, just force all the literals
            propagators.install_initialiser([full_reif = _full_reif, lits = _lits](
                                                const State &, auto & inference, ProofLogger * const logger) {
                for (auto & l : lits)
                    inference.infer(logger, l, JustifyUsingRUP{}, ExpandedReason{{full_reif}});
            });

            if (optional_model) {
                for (auto & l : _lits)
                    optional_model->add_constraint("Logical", "cnf", Literals{l});
            }
        }
        else {
            Triggers triggers;
            vector<IntegerVariableID> vars;
            bool saw_false = false;
            for (auto & l : _lits)
                overloaded{
                    [&](const IntegerVariableCondition & cond) {
                        switch (cond.op) {
                        case VariableConditionOperator::Equal:
                        case VariableConditionOperator::NotEqual:
                            triggers.on_change.push_back(cond.var);
                            break;
                        case VariableConditionOperator::Less:
                        case VariableConditionOperator::GreaterEqual:
                            triggers.on_bounds.push_back(cond.var);
                            break;
                        }
                        vars.push_back(cond.var);
                    },
                    [&](const TrueLiteral &) {
                    },
                    [&](const FalseLiteral &) {
                        saw_false = true;
                    }}
                    .visit(l);

            if (saw_false) {
                // we saw a false literal, the reif variable must be forced off and
                // then we don't do anything else
                propagators.install_initialiser([full_reif = _full_reif](
                                                    const State &, auto & inference, ProofLogger * const logger) -> void {
                    inference.infer(logger, ! full_reif, JustifyUsingRUP{}, NoReason{});
                });

                if (optional_model) {
                    optional_model->add_constraint("Logical", "saw reif false", Literals{! _full_reif});
                }
            }
            else {
                propagators.install([lits = _lits, full_reif = _full_reif](
                                        const State & state, auto & inference, ProofLogger * const logger) -> PropagatorState {
                    switch (state.test_literal(full_reif)) {
                    case LiteralIs::DefinitelyTrue: {
                        for (auto & l : lits)
                            inference.infer(logger, l, JustifyUsingRUP{}, ExpandedReason{{full_reif}});
                        return PropagatorState::DisableUntilBacktrack;
                    }

                    case LiteralIs::DefinitelyFalse: {
                        bool any_false = false;
                        optional<Literal> undecided1;

                        for (auto & l : lits)
                            switch (state.test_literal(l)) {
                            case LiteralIs::DefinitelyTrue: break;
                            case LiteralIs::DefinitelyFalse: any_false = true; break;
                            case LiteralIs::Undecided:
                                if (undecided1)
                                    return PropagatorState::Enable;
                                else
                                    undecided1 = l;
                            }

                        if (any_false)
                            return PropagatorState::DisableUntilBacktrack;
                        else if (! undecided1) {
                            // literals are all true, but reif is false
                            ExpandedReason why;
                            for (auto & lit : lits)
                                why.push_back(lit);
                            why.push_back(! full_reif);
                            inference.infer(logger, FalseLiteral{}, JustifyUsingRUP{}, why);
                            return PropagatorState::Enable;
                        }
                        else {
                            ExpandedReason why;
                            for (auto & l : lits)
                                if (l != *undecided1)
                                    why.push_back(l);
                            why.push_back(! full_reif);
                            inference.infer(logger, ! *undecided1, JustifyUsingRUP{}, why);
                            return PropagatorState::DisableUntilBacktrack;
                        }
                    }

                    case LiteralIs::Undecided: {
                        optional<Literal> any_false;
                        bool all_true = true;

                        for (auto & l : lits)
                            switch (state.test_literal(l)) {
                            case LiteralIs::DefinitelyTrue: break;
                            case LiteralIs::DefinitelyFalse:
                                any_false = l;
                                all_true = false;
                                break;
                            case LiteralIs::Undecided: all_true = false; break;
                            }

                        if (any_false) {
                            inference.infer(logger, ! full_reif, JustifyUsingRUP{}, ExpandedReason{{! *any_false}});
                            return PropagatorState::DisableUntilBacktrack;
                        }
                        else if (all_true) {
                            auto justf = [&](const ExpandedReason & reason) {
                                for (auto & l : lits)
                                    logger->emit_rup_proof_line_under_reason(reason,
                                        WeightedPseudoBooleanSum{} + 1_i * l >= 1_i, ProofLevel::Temporary);
                            };
                            inference.infer(logger, full_reif, JustifyExplicitly{justf}, ExpandedReason{lits});
                            return PropagatorState::DisableUntilBacktrack;
                        }
                        else
                            return PropagatorState::Enable;
                    }
                    }

                    throw NonExhaustiveSwitch{};
                },
                    {vars}, triggers, name);

                if (optional_model) {
                    if (LiteralIs::DefinitelyFalse != reif_state) {
                        WeightedPseudoBooleanSum forward;
                        for (auto & l : _lits)
                            forward += 1_i * PseudoBooleanTerm{l};
                        optional_model->add_constraint("Logical", "if condition", forward >= Integer(_lits.size()), HalfReifyOnConjunctionOf{_full_reif});
                    }

                    Literals reverse;
                    for (auto & l : _lits)
                        reverse.push_back(! l);
                    reverse.push_back(_full_reif);
                    optional_model->add_constraint("Logical", "if not condition", move(reverse));
                }
            }
        }
    }
}

And::And(const vector<IntegerVariableID> & vars, const IntegerVariableID & full_reif) :
    And(to_lits(vars), full_reif != 0_i)
{
}

And::And(const vector<IntegerVariableID> & vars) :
    And(to_lits(vars), TrueLiteral{})
{
}

And::And(Literals l, const Literal & full_reif) :
    _lits(move(l)),
    _full_reif(full_reif)
{
}

auto And::clone() const -> unique_ptr<Constraint>
{
    return make_unique<And>(_lits, _full_reif);
}

auto And::install(Propagators & propagators, State & initial_state, ProofModel * const optional_model) && -> void
{
    install_and_or_or(propagators, initial_state, optional_model, _lits, _full_reif, "and");
}

Or::Or(const vector<IntegerVariableID> & vars, const IntegerVariableID & full_reif) :
    Or(to_lits(vars), full_reif != 0_i)
{
}

Or::Or(const vector<IntegerVariableID> & vars) :
    Or(to_lits(vars), TrueLiteral{})
{
}

Or::Or(Literals l, const Literal & full_reif) :
    _lits(move(l)),
    _full_reif(full_reif)
{
}

auto Or::clone() const -> unique_ptr<Constraint>
{
    return make_unique<Or>(_lits, _full_reif);
}

auto Or::install(Propagators & propagators, State & initial_state, ProofModel * const optional_model) && -> void
{
    auto lits = _lits;
    for (auto & l : lits)
        l = ! l;

    install_and_or_or(propagators, initial_state, optional_model, lits, ! _full_reif, "or");
}
