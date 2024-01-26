#include <gcs/constraints/logical.hh>
#include <gcs/exception.hh>
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
        const Literals & _lits, const Literal & _full_reif,
        const string & name) -> void
    {
        auto reif_state = initial_state.test_literal(_full_reif);

        if (reif_state == LiteralIs::DefinitelyTrue) {
            // definitely true, just force all the literals
            propagators.install([lits = _lits](State & state) -> pair<Inference, PropagatorState> {
                Inference inf = Inference::NoChange;
                for (auto & l : lits) {
                    increase_inference_to(inf, state.infer(l, JustifyUsingRUP{}));
                    if (inf == Inference::Contradiction)
                        break;
                }
                return pair{inf, PropagatorState::DisableUntilBacktrack};
            },
                Triggers{}, name);

            if (propagators.want_definitions()) {
                for (auto & l : _lits)
                    propagators.define_cnf(initial_state, Literals{l});
            }
        }
        else {
            Triggers triggers;
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
                propagators.install([full_reif = _full_reif](State & state) -> pair<Inference, PropagatorState> {
                    return pair{state.infer(! full_reif, JustifyUsingRUP{}), PropagatorState::DisableUntilBacktrack};
                },
                    Triggers{}, name);

                if (propagators.want_definitions()) {
                    propagators.define_cnf(initial_state, Literals{! _full_reif});
                }
            }
            else {
                propagators.install([lits = _lits, full_reif = _full_reif](State & state) -> pair<Inference, PropagatorState> {
                    switch (state.test_literal(full_reif)) {
                    case LiteralIs::DefinitelyTrue: {
                        Inference inf = Inference::NoChange;
                        for (auto & l : lits) {
                            increase_inference_to(inf, state.infer(l, JustifyUsingRUP{}));
                            if (inf == Inference::Contradiction)
                                break;
                        }
                        return pair{inf, PropagatorState::DisableUntilBacktrack};
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
                                    return pair{Inference::NoChange, PropagatorState::Enable};
                                else
                                    undecided1 = l;
                            }

                        if (any_false)
                            return pair{Inference::NoChange, PropagatorState::DisableUntilBacktrack};
                        else if (! undecided1)
                            return pair{state.infer(FalseLiteral{}, JustifyExplicitly{[&](Proof & proof) {
                                            proof.emit_rup_proof_line_under_trail(state, WeightedPseudoBooleanSum{} + 1_i * ! full_reif >= 1_i, ProofLevel::Temporary);
                                            for (auto & l : lits)
                                                switch (state.test_literal(l)) {
                                                case LiteralIs::DefinitelyTrue:
                                                    proof.emit_rup_proof_line_under_trail(state, WeightedPseudoBooleanSum{} + 1_i * l >= 1_i, ProofLevel::Temporary);
                                                    break;
                                                case LiteralIs::DefinitelyFalse:
                                                    proof.emit_rup_proof_line_under_trail(state, WeightedPseudoBooleanSum{} + 1_i * ! l >= 1_i, ProofLevel::Temporary);
                                                    break;
                                                case LiteralIs::Undecided:
                                                    break;
                                                }
                                        }}),
                                PropagatorState::Enable};
                        else
                            return pair{state.infer(! *undecided1, JustifyExplicitly{[&](Proof & proof) {
                                            for (auto & l : lits)
                                                if (l != undecided1)
                                                    proof.emit_rup_proof_line_under_trail(state, WeightedPseudoBooleanSum{} + 1_i * l >= 1_i, ProofLevel::Temporary);
                                        }}),
                                PropagatorState::DisableUntilBacktrack};
                    }

                    case LiteralIs::Undecided: {
                        bool any_false = false;
                        bool all_true = true;

                        for (auto & l : lits)
                            switch (state.test_literal(l)) {
                            case LiteralIs::DefinitelyTrue: break;
                            case LiteralIs::DefinitelyFalse:
                                any_false = true;
                                all_true = false;
                                break;
                            case LiteralIs::Undecided: all_true = false; break;
                            }

                        if (any_false)
                            return pair{state.infer(! full_reif, JustifyUsingRUP{}), PropagatorState::DisableUntilBacktrack};
                        else if (all_true)
                            return pair{state.infer(full_reif, JustifyExplicitly{[&](Proof & proof) {
                                            for (auto & l : lits)
                                                proof.emit_rup_proof_line_under_trail(state, WeightedPseudoBooleanSum{} + 1_i * l >= 1_i, ProofLevel::Temporary);
                                        }}),
                                PropagatorState::DisableUntilBacktrack};
                        else
                            return pair{Inference::NoChange, PropagatorState::Enable};
                    }
                    }

                    throw NonExhaustiveSwitch{};
                },
                    triggers, name);

                if (propagators.want_definitions()) {
                    if (LiteralIs::DefinitelyFalse != reif_state) {
                        WeightedPseudoBooleanSum forward;
                        for (auto & l : _lits)
                            forward += 1_i * PseudoBooleanTerm{l};
                        propagators.define(initial_state, forward >= Integer(_lits.size()), HalfReifyOnConjunctionOf{_full_reif});
                    }

                    Literals reverse;
                    for (auto & l : _lits)
                        reverse.push_back(! l);
                    reverse.push_back(_full_reif);
                    propagators.define_cnf(initial_state, move(reverse));
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

auto And::describe_for_proof() -> string
{
    return "and";
}

auto And::install(Propagators & propagators, State & initial_state) && -> void
{
    install_and_or_or(propagators, initial_state, _lits, _full_reif, "and");
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

auto Or::describe_for_proof() -> string
{
    return "or";
}

auto Or::install(Propagators & propagators, State & initial_state) && -> void
{
    auto lits = _lits;
    for (auto & l : lits)
        l = ! l;

    install_and_or_or(propagators, initial_state, lits, ! _full_reif, "or");
}
