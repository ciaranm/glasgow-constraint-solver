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

using std::move;
using std::nullopt;
using std::optional;
using std::pair;
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

    // The cake positive forms of a logical constraint's literals and its
    // reification, as state-equivalent `>= 1` literals -- or empty / nullopt
    // when some literal has no such form (see cake_truthiness.hh).
    auto compute_cake_lits(const Literals & lits, const Literal & full_reif, const State & initial_state) -> pair<Literals, optional<Literal>>
    {
        auto bounds = [&](const SimpleIntegerVariableID & v) { return initial_state.bounds(v); };
        auto reif_form = cake_positive_form(full_reif, bounds);
        if (! reif_form)
            return {};
        Literals cake_lits;
        for (const auto & l : lits) {
            auto form = cake_positive_form(l, bounds);
            if (! form)
                return {};
            cake_lits.push_back(cake_positive_literal(*form));
        }
        return {move(cake_lits), cake_positive_literal(*reif_form)};
    }

    // cake_pb_cp's and/or rows: @c[id][pos] says the reification implies the
    // conjunction (and: all of them; or: at least one), @c[id][neg] the
    // negation implies the negated disjunction. Uniform, with no
    // statically-decided shortcuts, so the labelled rows' content matches
    // cake's whatever the bounds.
    auto define_cake_logical(ProofModel & model, const ConstraintID & id, const Literals & cake_lits, const Literal & cake_reif, bool is_and) -> void
    {
        auto n = Integer(static_cast<long long>(cake_lits.size()));
        WPBSum pos, neg;
        pos += (is_and ? -n : -1_i) * PseudoBooleanTerm{cake_reif};
        neg += (is_and ? -1_i : -n) * PseudoBooleanTerm{! cake_reif};
        for (const auto & l : cake_lits) {
            pos += 1_i * PseudoBooleanTerm{l};
            neg += 1_i * PseudoBooleanTerm{! l};
        }
        model.add_labelled_constraint(id, "pos", move(pos) >= 0_i);
        model.add_labelled_constraint(id, "neg", move(neg) >= 0_i);
    }

    // The bare-operand `and` / `or` scp term when every literal conforms
    // (recomputed from the tracker: this runs on the stored constraint, which
    // never sees prepare()); the faithful `_lits` form otherwise, which cake
    // skips and read_scp round-trips.
    auto s_expr_logical(
        const NamesAndIDsTracker & tracker, const ConstraintID & id, const string & op, const Literals & lits, const Literal & full_reif) -> SExpr
    {
        auto bounds = [&](const SimpleIntegerVariableID & v) { return tracker.tracked_bounds(v); };
        vector<SExpr> terms;
        bool conformable = static_cast<bool>(cake_positive_form(full_reif, bounds));
        if (conformable)
            for (const auto & lit : lits) {
                auto form = cake_positive_form(lit, bounds);
                if (! form) {
                    conformable = false;
                    break;
                }
                terms.push_back(tracker.s_expr_term_of(*form));
            }
        if (conformable) {
            auto reif_form = cake_positive_form(full_reif, bounds);
            return SExpr::list({SExpr::atom(as_string(id)), SExpr::atom(op), SExpr::list(move(terms)), tracker.s_expr_term_of(*reif_form)});
        }

        terms.clear();
        for (const auto & lit : lits)
            terms.push_back(faithful_literal_term(lit, tracker));
        return SExpr::list(
            {SExpr::atom(as_string(id)), SExpr::atom(op + "_lits"), SExpr::list(move(terms)), faithful_literal_term(full_reif, tracker)});
    }

    auto define_proof_model_logical(ProofModel & model, const Literals & lits, const Literal & full_reif, LiteralIs reif_state) -> void
    {
        using enum LiteralIs;

        if (reif_state == DefinitelyTrue) {
            for (auto & l : lits)
                model.add_constraint(Literals{l});
            return;
        }

        bool saw_false = false;
        for (auto & l : lits)
            overloaded{
                [&](const FalseLiteral &) { saw_false = true; }, //
                [&](const auto &) {}                             //
            }
                .visit(l);

        if (saw_false) {
            model.add_constraint(Literals{! full_reif});
            return;
        }

        if (DefinitelyFalse != reif_state) {
            WPBSum forward;
            for (auto & l : lits)
                forward += 1_i * PseudoBooleanTerm{l};
            model.add_constraint(forward >= Integer(lits.size()), HalfReifyOnConjunctionOf{full_reif});
        }

        Literals reverse;
        for (auto & l : lits)
            reverse.push_back(! l);
        reverse.push_back(full_reif);
        model.add_constraint(move(reverse));
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
    std::tie(_cake_lits, _cake_reif) = compute_cake_lits(_lits, _full_reif, initial_state);
    return true;
}

auto And::define_proof_model(ProofModel & model) -> void
{
    if (_cake_reif)
        define_cake_logical(model, _constraint_id, _cake_lits, *_cake_reif, true);
    else
        define_proof_model_logical(model, _lits, _full_reif, _reif_state);
}

auto And::install_propagators(Propagators & propagators) -> void
{
    // In cake terms when prepare() found positive forms, so the inferences'
    // literals are the atoms the (cake-conform) encoding constrains.
    if (_cake_reif)
        install_propagators_logical<hints::And>(propagators, constraint_id(), _cake_lits, *_cake_reif, _reif_state);
    else
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
    std::tie(_cake_lits, _cake_reif) = compute_cake_lits(_lits, _full_reif, initial_state);
    return true;
}

auto Or::define_proof_model(ProofModel & model) -> void
{
    if (_cake_reif) {
        define_cake_logical(model, _constraint_id, _cake_lits, *_cake_reif, false);
        return;
    }
    Literals lits = _lits;
    for (auto & l : lits)
        l = ! l;
    define_proof_model_logical(model, move(lits), ! _full_reif, _reif_state);
}

auto Or::install_propagators(Propagators & propagators) -> void
{
    // As And: the dualised literals come from the cake forms when available.
    Literals lits = _cake_reif ? _cake_lits : _lits;
    for (auto & l : lits)
        l = ! l;
    install_propagators_logical<hints::Or>(propagators, constraint_id(), move(lits), _cake_reif ? ! *_cake_reif : ! _full_reif, _reif_state);
}

auto Or::constraint_type() const -> std::string
{
    return "or";
}

auto Or::s_expr(const innards::ProofModel * const model) const -> SExpr
{
    return s_expr_logical(model->names_and_ids_tracker(), _constraint_id, constraint_type(), _lits, _full_reif);
}
