#include <gcs/constraints/innards/cake_truthiness.hh>
#include <gcs/constraints/innards/triggers.hh>
#include <gcs/constraints/logical/hints.hh>
#include <gcs/constraints/logical/logical.hh>
#include <gcs/exception.hh>
#include <gcs/innards/inference_tracker.hh>
#include <gcs/innards/proofs/names_and_ids_tracker.hh>
#include <gcs/innards/proofs/proof_logger.hh>
#include <gcs/innards/proofs/proof_model.hh>
#include <gcs/innards/propagators.hh>
#include <gcs/innards/s_expr.hh>
#include <gcs/innards/state.hh>

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

using std::move;
using std::nullopt;
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

    template <typename Hint_>
    auto install_propagators_logical(
        Propagators & propagators, const ConstraintID & constraint_id, const Literals & lits, const Literal & full_reif, LiteralIs reif_state) -> void
    {
        using enum LiteralIs;

        if (reif_state == DefinitelyTrue) {
            // definitely true, just force all the literals
            propagators.install_initialiser(
                [full_reif = full_reif, lits = lits, owner = constraint_id](const State &, auto & inference, ProofLogger * const logger) {
                    for (auto & l : lits)
                        inference.infer(logger, l, JustifyUsingRUP{Hint_{owner}}, ExplicitReason{ReasonLiterals{{full_reif}}});
                });
            return;
        }

        Triggers triggers;
        bool saw_false = false;
        for (auto & l : lits) {
            add_trigger_for(triggers, l);
            if (holds_alternative<FalseLiteral>(l))
                saw_false = true;
        }
        // Also wake on the reif literal: otherwise fixing full_reif (e.g. by
        // branching) does not re-run the propagator, so full_reif being forced
        // true would fail to push the lits true (the GAC gap from #413).
        add_trigger_for(triggers, full_reif);

        if (saw_false) {
            // we saw a false literal, the reif variable must be forced off and
            // then we don't do anything else
            propagators.install_initialiser(
                [full_reif = full_reif, owner = constraint_id](const State &, auto & inference, ProofLogger * const logger) -> void {
                    inference.infer(logger, ! full_reif, JustifyUsingRUP{Hint_{owner}}, NoReason{});
                });
            return;
        }

        propagators.install(
            constraint_id,
            [lits = lits, full_reif = full_reif, owner = constraint_id](
                const State & state, auto & inference, ProofLogger * const logger) -> PropagatorState {
                switch (state.test_literal(full_reif)) {
                case DefinitelyTrue: {
                    for (auto & l : lits)
                        inference.infer(logger, l, JustifyUsingRUP{Hint_{owner}}, ExplicitReason{ReasonLiterals{{full_reif}}});
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
                        ReasonLiterals why;
                        for (auto & lit : lits)
                            why.push_back(lit);
                        why.push_back(! full_reif);
                        inference.infer(logger, FalseLiteral{}, JustifyUsingRUP{Hint_{owner}}, ExplicitReason{why});
                        return PropagatorState::Enable;
                    }
                    else {
                        ReasonLiterals why;
                        for (auto & l : lits)
                            if (l != *undecided1)
                                why.push_back(l);
                        why.push_back(! full_reif);
                        inference.infer(logger, ! *undecided1, JustifyUsingRUP{Hint_{owner}}, ExplicitReason{why});
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
                        inference.infer(logger, ! full_reif, JustifyUsingRUP{Hint_{owner}}, ExplicitReason{ReasonLiterals{{! *any_false}}});
                        return PropagatorState::DisableUntilBacktrack;
                    }
                    else if (all_true) {
                        auto justf = [&](const ReasonLiterals & reason) {
                            for (auto & l : lits)
                                logger->emit_rup_proof_line_under_reason(reason, WPBSum{} + 1_i * l >= 1_i, ProofLevel::Temporary);
                        };
                        vector<ProofLiteral> reason_lits{};
                        for (auto & l : lits)
                            reason_lits.emplace_back(l);
                        inference.infer(logger, full_reif, JustifyExplicitly{justf, ThenRUP::Yes, Hint_{owner}},
                            ExplicitReason{ReasonLiterals(reason_lits.begin(), reason_lits.end())});
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

    // cake_pb_cp's and/or rows: @c[id][pos] says the reification implies the
    // conjunction (and: all of them; or: at least one), @c[id][neg] the
    // negation implies the negated disjunction. Uniform, with no
    // statically-decided shortcuts (a statically true/false reif or literal
    // just folds into the rows), so the labelled rows' content matches cake's,
    // whatever the literals. cake reads each of `lits` / `full_reif` as a
    // reification tuple and maps it to the same ge / eq atom used here.
    auto define_cake_logical(ProofModel & model, const ConstraintID & id, const Literals & lits, const Literal & full_reif, bool is_and) -> void
    {
        auto n = Integer(static_cast<long long>(lits.size()));
        WPBSum pos, neg;
        pos += (is_and ? -n : -1_i) * PseudoBooleanTerm{full_reif};
        neg += (is_and ? -1_i : -n) * PseudoBooleanTerm{! full_reif};
        for (const auto & l : lits) {
            pos += 1_i * PseudoBooleanTerm{l};
            neg += 1_i * PseudoBooleanTerm{! l};
        }
        model.add_labelled_constraint(id, "pos", move(pos) >= 0_i);
        model.add_labelled_constraint(id, "neg", move(neg) >= 0_i);
    }

    // The `and` / `or` scp term: cake reads `(op ((Z op v) ...) (Y op v))`,
    // one reification tuple per operand plus one for the reification. Every
    // literal maps directly (see reify_tuple_term); a view-conditioned operand
    // is written faithfully as a tuple over its view, which cake's var/const
    // parser rejects so the instance skips the chain, and read_scp round-trips
    // the tuples either way.
    auto s_expr_logical(
        const NamesAndIDsTracker & tracker, const ConstraintID & id, const string & op, const Literals & lits, const Literal & full_reif) -> SExpr
    {
        vector<SExpr> terms;
        for (const auto & lit : lits)
            terms.push_back(reify_tuple_term(lit, tracker));
        return SExpr::list({SExpr::atom(as_string(id)), SExpr::atom(op), SExpr::list(move(terms)), reify_tuple_term(full_reif, tracker)});
    }
}

And::And(const vector<IntegerVariableID> & vars, const IntegerVariableID & full_reif) : And(to_lits(vars), full_reif != 0_i)
{
}

And::And(const vector<IntegerVariableID> & vars) : And(to_lits(vars), TrueLiteral{})
{
}

And::And(Literals l, const Literal & full_reif) : _lits(move(l)), _full_reif(full_reif)
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
    define_cake_logical(model, _constraint_id, _lits, _full_reif, true);
}

auto And::install_propagators(Propagators & propagators) -> void
{
    install_propagators_logical<hints::And>(propagators, constraint_id(), _lits, _full_reif, _reif_state);
}

auto And::constraint_type() const -> std::string
{
    return "and";
}

auto And::s_expr(const innards::ProofModel * const model) const -> SExpr
{
    return s_expr_logical(model->names_and_ids_tracker(), _constraint_id, constraint_type(), _lits, _full_reif);
}

Or::Or(const vector<IntegerVariableID> & vars, const IntegerVariableID & full_reif) : Or(to_lits(vars), full_reif != 0_i)
{
}

Or::Or(const vector<IntegerVariableID> & vars) : Or(to_lits(vars), TrueLiteral{})
{
}

Or::Or(Literals l, const Literal & full_reif) : _lits(move(l)), _full_reif(full_reif)
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
    define_cake_logical(model, _constraint_id, _lits, _full_reif, false);
}

auto Or::install_propagators(Propagators & propagators) -> void
{
    // Or is the And propagator over the negated literals and reification.
    Literals lits = _lits;
    for (auto & l : lits)
        l = ! l;
    install_propagators_logical<hints::Or>(propagators, constraint_id(), move(lits), ! _full_reif, _reif_state);
}

auto Or::constraint_type() const -> std::string
{
    return "or";
}

auto Or::s_expr(const innards::ProofModel * const model) const -> SExpr
{
    return s_expr_logical(model->names_and_ids_tracker(), _constraint_id, constraint_type(), _lits, _full_reif);
}
