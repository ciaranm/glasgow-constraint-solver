#include <gcs/constraints/logical.hh>
#include <gcs/exception.hh>
#include <gcs/innards/inference_tracker.hh>
#include <gcs/innards/proofs/names_and_ids_tracker.hh>
#include <gcs/innards/proofs/proof_logger.hh>
#include <gcs/innards/proofs/proof_model.hh>
#include <gcs/innards/propagators.hh>
#include <gcs/innards/state.hh>

#include <util/overloaded.hh>

#include <optional>
#include <sstream>

#include <version>

#if defined(__cpp_lib_print) && defined(__cpp_lib_format)
#include <print>
#else
#include <fmt/core.h>
#include <fmt/ostream.h>
#endif

using namespace gcs;
using namespace gcs::innards;

using std::optional;
using std::string;
using std::stringstream;
using std::unique_ptr;
using std::vector;

#if defined(__cpp_lib_print) && defined(__cpp_lib_format)
using std::print;
#else
using fmt::print;
#endif

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

    auto install_propagators_logical(Propagators & propagators, const Literals & lits,
        const Literal & full_reif, LiteralIs reif_state) -> void
    {
        using enum LiteralIs;

        if (reif_state == DefinitelyTrue) {
            // definitely true, just force all the literals
            propagators.install_initialiser([full_reif = full_reif, lits = lits](
                                                const State &, auto & inference, ProofLogger * const logger) {
                for (auto & l : lits)
                    inference.infer(logger, l, JustifyUsingRUP{}, ReasonFunction{[=]() { return Reason{{full_reif}}; }});
            });
            return;
        }

        Triggers triggers;
        bool saw_false = false;
        for (auto & l : lits)
            overloaded{
                [&](const IntegerVariableCondition & cond) {
                    switch (cond.op) {
                        using enum VariableConditionOperator;
                    case Equal:
                    case NotEqual:
                        triggers.on_change.push_back(cond.var);
                        break;
                    case Less:
                    case GreaterEqual:
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
            propagators.install_initialiser([full_reif = full_reif](
                                                const State &, auto & inference, ProofLogger * const logger) -> void {
                inference.infer(logger, ! full_reif, JustifyUsingRUP{}, ReasonFunction{});
            });
            return;
        }

        propagators.install([lits = lits, full_reif = full_reif](
                                const State & state, auto & inference, ProofLogger * const logger) -> PropagatorState {
            switch (state.test_literal(full_reif)) {
            case DefinitelyTrue: {
                for (auto & l : lits)
                    inference.infer(logger, l, JustifyUsingRUP{}, ReasonFunction{[=]() { return Reason{{full_reif}}; }});
                return PropagatorState::DisableUntilBacktrack;
            }

            case DefinitelyFalse: {
                bool any_false = false;
                optional<Literal> undecided1;

                for (auto & l : lits)
                    switch (state.test_literal(l)) {
                    case DefinitelyTrue: break;
                    case DefinitelyFalse: any_false = true; break;
                    case Undecided:
                        if (undecided1)
                            return PropagatorState::Enable;
                        else
                            undecided1 = l;
                    }

                if (any_false)
                    return PropagatorState::DisableUntilBacktrack;
                else if (! undecided1) {
                    // literals are all true, but reif is false
                    Reason why;
                    for (auto & lit : lits)
                        why.push_back(lit);
                    why.push_back(! full_reif);
                    inference.infer(logger, FalseLiteral{}, JustifyUsingRUP{}, ReasonFunction{[=]() { return why; }});
                    return PropagatorState::Enable;
                }
                else {
                    Reason why;
                    for (auto & l : lits)
                        if (l != *undecided1)
                            why.push_back(l);
                    why.push_back(! full_reif);
                    inference.infer(logger, ! *undecided1, JustifyUsingRUP{}, ReasonFunction{[=]() { return why; }});
                    return PropagatorState::DisableUntilBacktrack;
                }
            }

            case Undecided: {
                optional<Literal> any_false;
                bool all_true = true;

                for (auto & l : lits)
                    switch (state.test_literal(l)) {
                    case DefinitelyTrue: break;
                    case DefinitelyFalse:
                        any_false = l;
                        all_true = false;
                        break;
                    case Undecided: all_true = false; break;
                    }

                if (any_false) {
                    inference.infer(logger, ! full_reif, JustifyUsingRUP{}, ReasonFunction{[=]() { return Reason{{! *any_false}}; }});
                    return PropagatorState::DisableUntilBacktrack;
                }
                else if (all_true) {
                    auto justf = [&](const ReasonFunction & reason) {
                        for (auto & l : lits)
                            logger->emit_rup_proof_line_under_reason(reason,
                                WPBSum{} + 1_i * l >= 1_i, ProofLevel::Temporary);
                    };
                    inference.infer(logger, full_reif, JustifyExplicitlyThenRUP{justf}, ReasonFunction{[=]() {
                        vector<ProofLiteral> reason_lits{};
                        for (auto & l : lits)
                            reason_lits.emplace_back(l);
                        return Reason(reason_lits.begin(), reason_lits.end());
                    }});
                    return PropagatorState::DisableUntilBacktrack;
                }
                else
                    return PropagatorState::Enable;
            }
            }

            throw NonExhaustiveSwitch{};
        },
            triggers);
    }

    auto define_proof_model_logical(ProofModel & model, const Literals & lits,
        const Literal & full_reif, LiteralIs reif_state) -> void
    {
        using enum LiteralIs;

        if (reif_state == DefinitelyTrue) {
            for (auto & l : lits)
                model.add_constraint("Logical", "cnf", Literals{l});
            return;
        }

        bool saw_false = false;
        for (auto & l : lits)
            overloaded{
                [&](const FalseLiteral &) { saw_false = true; },
                [&](const auto &) {}}
                .visit(l);

        if (saw_false) {
            model.add_constraint("Logical", "saw reif false", Literals{! full_reif});
            return;
        }

        if (DefinitelyFalse != reif_state) {
            WPBSum forward;
            for (auto & l : lits)
                forward += 1_i * PseudoBooleanTerm{l};
            model.add_constraint("Logical", "if condition", forward >= Integer(lits.size()), HalfReifyOnConjunctionOf{full_reif});
        }

        Literals reverse;
        for (auto & l : lits)
            reverse.push_back(! l);
        reverse.push_back(full_reif);
        model.add_constraint("Logical", "if not condition", move(reverse));
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
    if (! prepare(propagators, initial_state, optional_model))
        return;

    if (optional_model)
        define_proof_model(*optional_model);

    install_propagators(propagators);
}

auto And::prepare(Propagators &, State & initial_state, ProofModel * const) -> bool
{
    _reif_state = initial_state.test_literal(_full_reif);
    return true;
}

auto And::define_proof_model(ProofModel & model) -> void
{
    define_proof_model_logical(model, _lits, _full_reif, _reif_state);
}

auto And::install_propagators(Propagators & propagators) -> void
{
    install_propagators_logical(propagators, _lits, _full_reif, _reif_state);
}

auto And::s_exprify(const string & name, const innards::ProofModel * const model) const -> string
{
    stringstream s;

    print(s, "{} and (", name);
    for (const auto & lit : _lits) {
        print(s, " {}", model->names_and_ids_tracker().s_expr_name_of(lit));
    }
    print(s, ") {}", model->names_and_ids_tracker().s_expr_name_of(_full_reif));

    return s.str();
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
    if (! prepare(propagators, initial_state, optional_model))
        return;

    if (optional_model)
        define_proof_model(*optional_model);

    install_propagators(propagators);
}

auto Or::prepare(Propagators &, State & initial_state, ProofModel * const) -> bool
{
    _reif_state = initial_state.test_literal(! _full_reif);
    return true;
}

auto Or::define_proof_model(ProofModel & model) -> void
{
    Literals lits = _lits;
    for (auto & l : lits)
        l = ! l;
    define_proof_model_logical(model, move(lits), ! _full_reif, _reif_state);
}

auto Or::install_propagators(Propagators & propagators) -> void
{
    Literals lits = _lits;
    for (auto & l : lits)
        l = ! l;
    install_propagators_logical(propagators, move(lits), ! _full_reif, _reif_state);
}

auto Or::s_exprify(const string & name, const innards::ProofModel * const model) const -> string
{
    stringstream s;

    print(s, "{} or (", name);
    for (const auto & lit : _lits) {
        print(s, " {}", model->names_and_ids_tracker().s_expr_name_of(lit));
    }
    print(s, ") {}", model->names_and_ids_tracker().s_expr_name_of(_full_reif));

    return s.str();
}
