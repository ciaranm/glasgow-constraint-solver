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

#include <algorithm>
#include <cstddef>
#include <cstdint>
#include <cstdlib>
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
using std::size_t;
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

    // Which halves of full_reif <-> /\ lits the propagator enforces. And and Or
    // want both. AndIf wants only the forward half, full_reif -> /\ lits. OrIf,
    // which like Or is this propagator over the negated literals and condition,
    // wants only the backward half: /\ ~lits -> ~cond is cond -> \/ lits.
    enum class Halves
    {
        Both,
        ReifImpliesConjunction,
        ConjunctionImpliesReif
    };

    // The reason for a last-undecided inference or a conflict: every literal
    // but the one being forced, if there is one, and the reif's negation. Only
    // built when something is going to read it, because it is as long as the
    // constraint, and a clause can be very long (issue #1060).
    template <typename Inference_>
    auto all_but_one_reason(const Inference_ & inference, const Literals & lits, const Literal & full_reif, const optional<Literal> & forced)
        -> Reason
    {
        if (! inference.want_reasons())
            return Reason{};
        ReasonLiterals why;
        for (auto & l : lits)
            if (! forced || l != *forced)
                why.push_back(l);
        why.push_back(! full_reif);
        return Reason{ExplicitReason{move(why)}};
    }

    // From this many literals on, a constraint whose reif is false from the
    // start watches two of its literals instead of scanning them on every
    // wake. See default_clause_watch_threshold() in logical.hh.
    auto clause_watch_threshold(const optional<size_t> & per_constraint) -> size_t
    {
        return per_constraint ? *per_constraint : default_clause_watch_threshold();
    }

    // The clause case, with two watched literals: the reif is false from the
    // start and the backward half is wanted, so the constraint says only that
    // not every literal holds. That is every Or clause (FlatZinc's
    // bool_clause), which is Or over TrueLiteral and so this over its negated
    // literals, and an And whose reif is fixed false.
    //
    // The scan finds the same inferences, but walks every literal decided so
    // far to get to the undecided ones, on every wake of every variable in the
    // constraint. For a long clause whose front the search has fixed that is
    // the whole cost (issue #1060). Here the propagator watches two literals
    // that are not entailed, and wakes only when one of them becomes entailed.
    // It then moves that watch to another literal that is not entailed, or if
    // there is none, forces the other watched literal false, or fails if that
    // is entailed too.
    //
    // The watches only ever move forwards, so the search for a new one starts
    // after both of them and never goes back round. Every literal before the
    // later watch, other than the two watched, is entailed: that holds when
    // the watches are armed, each move passes over only entailed literals,
    // and on backtrack the positions return to the ones that held it at that
    // level, whose literals were entailed and still are, since entailment only
    // grows down a branch. So the literals before are no candidates, and a
    // search that fixes the literals in order finds the next one straight
    // away, rather than walking the prefix it has fixed.
    //
    // This is the two-watched-literal scheme of the Nogoods store and of
    // NegativeTable, for a single clause: the watched positions live in
    // watch_state, restored in lockstep with the watches on backtrack, so a
    // forced literal leaves its consumed watch to be restored rather than
    // keeping it. A literal that is already false counts as not entailed, so
    // a satisfied clause can rest a watch on it, where it never fires. See
    // dev_docs/refined-triggers.md.
    //
    // A named template rather than a lambda for the MSVC-C1001 reason noted in
    // negative_table.cc (a generic-on-inference lambda nesting further
    // lambdas).
    template <typename Hint_, typename Inference_>
    auto propagate_watched_clause(const Literals & lits, const Literal & full_reif, const ConstraintID & owner, const State & state,
        Inference_ & inference, ProofLogger * const logger, const RefinedWatchContext & ctx) -> PropagatorState
    {
        using enum LiteralIs;

        // watch_state holds the two watched positions, and whether they have
        // been armed at all.
        constexpr std::uint32_t positions_key = 0, armed_key = 1;

        auto n = lits.size();
        auto pack = [](size_t a, size_t b) -> std::uint64_t { return (static_cast<std::uint64_t>(a) << 32) | static_cast<std::uint32_t>(b); };

        // The first position from start on whose literal is not entailed.
        auto find_unentailed = [&](size_t start) -> optional<size_t> {
            for (size_t i = start; i < n; ++i)
                if (! state.literal_is_entailed(lits[i]))
                    return i;
            return nullopt;
        };

        // A literal that is false satisfies the clause, which then has nothing
        // to do until backtrack. Disabling it then, as the scan does, is what
        // keeps a satisfied clause quiet: otherwise its watches go on firing,
        // and moving, until one of them happens to land on the false literal.
        // Nothing needs to move first, since backtracking out of this call
        // restores the watches and re-enables the propagator together.
        auto satisfies = [&](size_t i) -> bool { return state.literal_is_entailed(! lits[i]); };

        // Only lits[survivor] is not entailed: it must be false, if it is not
        // already. Either way the clause is then satisfied.
        auto force_false = [&](size_t survivor) -> PropagatorState {
            if (! satisfies(survivor))
                inference.infer(
                    logger, ! lits[survivor], JustifyUsingRUP{Hint_{owner}}, all_but_one_reason(inference, lits, full_reif, lits[survivor]));
            return PropagatorState::DisableUntilBacktrack;
        };

        if (0 == ctx.watch_state(armed_key)) {
            // The first run, at the root. The arming lives in the root epoch,
            // so a restart's root re-propagation finds it still there. The
            // flag saying so is backtrackable, restored with the watches,
            // because a presolver can run every propagator at the root of a
            // search of its own and then backtrack out of it (AutoTable does):
            // a flag that survived that would leave the real root with no
            // watches, and the clause dead.
            auto w1 = find_unentailed(0);
            if (! w1)
                return inference.contradiction_or_stop(
                    logger, JustifyUsingRUP{Hint_{owner}}, all_but_one_reason(inference, lits, full_reif, nullopt));
            auto w2 = find_unentailed(*w1 + 1);
            ctx.set_watch_state(armed_key, 1);
            if (! w2) {
                // Forced at the root, where it stays satisfied, so one
                // watch resting on the survivor is enough.
                ctx.watch(lits[*w1], 0);
                ctx.set_watch_state(positions_key, pack(*w1, *w1));
                return force_false(*w1);
            }
            ctx.watch(lits[*w1], 0);
            ctx.watch(lits[*w2], 0);
            ctx.set_watch_state(positions_key, pack(*w1, *w2));
            return satisfies(*w1) || satisfies(*w2) ? PropagatorState::DisableUntilBacktrack : PropagatorState::Enable;
        }

        // There is only the one clause, so which watch fired says nothing
        // that the two watched positions do not.
        auto packed = ctx.watch_state(positions_key);
        auto p = static_cast<size_t>(packed >> 32), q = static_cast<size_t>(packed & 0xffffffffu);
        auto p_is = state.test_literal(lits[p]), q_is = state.test_literal(lits[q]);
        if (p_is == DefinitelyFalse || q_is == DefinitelyFalse)
            return PropagatorState::DisableUntilBacktrack;
        auto after_both = std::max(p, q) + 1;

        if (p_is == DefinitelyTrue && q_is == DefinitelyTrue) {
            // Both watches fired. Two fresh positions, or a forced literal if
            // there is only one, or a conflict if there are none. Forcing
            // leaves watch_state at (p, q), to match the two consumed watches
            // that backtracking restores.
            auto new1 = find_unentailed(after_both);
            if (! new1)
                return inference.contradiction_or_stop(
                    logger, JustifyUsingRUP{Hint_{owner}}, all_but_one_reason(inference, lits, full_reif, nullopt));
            if (satisfies(*new1))
                return PropagatorState::DisableUntilBacktrack;
            auto new2 = find_unentailed(*new1 + 1);
            if (! new2)
                return force_false(*new1);
            if (satisfies(*new2))
                return PropagatorState::DisableUntilBacktrack;
            ctx.watch(lits[*new1], 0);
            ctx.watch(lits[*new2], 0);
            ctx.set_watch_state(positions_key, pack(*new1, *new2));
        }
        else if (p_is == DefinitelyTrue || q_is == DefinitelyTrue) {
            // One watch fired, and the other's is still armed.
            auto kept = p_is == DefinitelyTrue ? q : p;
            auto moved = find_unentailed(after_both);
            if (! moved)
                return force_false(kept);
            if (satisfies(*moved))
                return PropagatorState::DisableUntilBacktrack;
            ctx.watch(lits[*moved], 0);
            ctx.set_watch_state(positions_key, pack(kept, *moved));
        }

        return PropagatorState::Enable;
    }

    template <typename Hint_>
    auto install_propagators_logical(Propagators & propagators, const ConstraintID & constraint_id, const Literals & lits, const Literal & full_reif,
        LiteralIs reif_state, Halves halves, const optional<size_t> & watch_threshold) -> void
    {
        using enum LiteralIs;

        bool forwards = halves != Halves::ConjunctionImpliesReif;
        bool backwards = halves != Halves::ReifImpliesConjunction;

        if (reif_state == DefinitelyTrue) {
            // definitely true, just force all the literals. The backward half
            // is satisfied by the reif whatever the literals do.
            if (forwards)
                propagators.install_initialiser(
                    [full_reif = full_reif, lits = lits, owner = constraint_id](const State &, auto & inference, ProofLogger * const logger) {
                        const Reason reason = inference.want_reasons() ? Reason{ExplicitReason{ReasonLiterals{{full_reif}}}} : Reason{};
                        for (auto & l : lits)
                            inference.infer(logger, l, JustifyUsingRUP{Hint_{owner}}, reason);
                    });
            return;
        }

        // A reif that is already false makes the forward half vacuous.
        if (reif_state == DefinitelyFalse && ! backwards)
            return;

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
            // we saw a false literal, so the conjunction is false: the reif
            // variable must be forced off, and then we don't do anything else.
            // The backward half is vacuous, so it has nothing to force.
            if (forwards)
                propagators.install_initialiser(
                    [full_reif = full_reif, owner = constraint_id](const State &, auto & inference, ProofLogger * const logger) -> void {
                        inference.infer(logger, ! full_reif, JustifyUsingRUP{Hint_{owner}}, NoReason{});
                    });
            return;
        }

        if (reif_state == DefinitelyFalse && lits.size() >= clause_watch_threshold(watch_threshold)) {
            // Woken only by the watches it arms, so the coarse triggers above
            // become the propagator's scope and wake nothing. That keeps each
            // variable's degree what the scan gives it, so a degree-based
            // brancher searches the same tree either way, and keeps the
            // hole-sensitivity it would derive from them.
            Triggers watched_triggers;
            watched_triggers.scope_only = triggers.on_change;
            watched_triggers.scope_only.insert(watched_triggers.scope_only.end(), triggers.on_bounds.begin(), triggers.on_bounds.end());
            watched_triggers.holes_affect_propagation = move(triggers.on_change);

            propagators.install(
                constraint_id,
                [lits = lits, full_reif = full_reif, owner = constraint_id](
                    const State & state, auto & inference, ProofLogger * const logger, const RefinedWatchContext & ctx) -> PropagatorState {
                    return propagate_watched_clause<Hint_>(lits, full_reif, owner, state, inference, logger, ctx);
                },
                move(watched_triggers));
            return;
        }

        propagators.install(
            constraint_id,
            [lits = lits, full_reif = full_reif, owner = constraint_id, forwards, backwards](
                const State & state, auto & inference, ProofLogger * const logger) -> PropagatorState {
                switch (state.test_literal(full_reif)) {
                case DefinitelyTrue: {
                    if (forwards) {
                        const Reason reason = inference.want_reasons() ? Reason{ExplicitReason{ReasonLiterals{{full_reif}}}} : Reason{};
                        for (auto & l : lits)
                            inference.infer(logger, l, JustifyUsingRUP{Hint_{owner}}, reason);
                    }
                    return PropagatorState::DisableUntilBacktrack;
                }

                case DefinitelyFalse: {
                    if (! backwards)
                        return PropagatorState::DisableUntilBacktrack;

                    optional<Literal> undecided1;

                    for (auto & l : lits)
                        switch (state.test_literal(l)) {
                        case DefinitelyTrue: break;
                        case DefinitelyFalse:
                            // Satisfied, whatever the rest of the literals
                            // do, so there is no need to look at them.
                            return PropagatorState::DisableUntilBacktrack;
                        case Undecided:
                            if (undecided1)
                                return PropagatorState::Enable;
                            else
                                undecided1 = l;
                        }

                    if (! undecided1) {
                        // literals are all true, but reif is false. Stop rather
                        // than throw: for Or -- which is this propagator over
                        // negated literals -- this is the clause conflict, and a
                        // clause is the failure detector at a large share of the
                        // nodes of the models that have any. It is 1.2M unwinds
                        // in twenty seconds of `2014_train`, where the unwinder
                        // is 22% of the run. Inferring FalseLiteral{} and
                        // contradicting are the same proof step and the same
                        // reason; only the way out of the propagator differs.
                        return inference.contradiction_or_stop(
                            logger, JustifyUsingRUP{Hint_{owner}}, all_but_one_reason(inference, lits, full_reif, nullopt));
                    }
                    else {
                        inference.infer(
                            logger, ! *undecided1, JustifyUsingRUP{Hint_{owner}}, all_but_one_reason(inference, lits, full_reif, undecided1));
                        return PropagatorState::DisableUntilBacktrack;
                    }
                }

                case Undecided: {
                    bool all_true = true;

                    for (auto & l : lits)
                        switch (state.test_literal(l)) {
                        case DefinitelyTrue: break;
                        case DefinitelyFalse:
                            // The conjunction is false, which settles the
                            // halves this propagator lacks until backtrack: it
                            // makes the backward half vacuous, and forces the
                            // reif false for the forward half.
                            if (forwards)
                                inference.infer(logger, ! full_reif, JustifyUsingRUP{Hint_{owner}},
                                    inference.want_reasons() ? Reason{ExplicitReason{ReasonLiterals{{! l}}}} : Reason{});
                            return PropagatorState::DisableUntilBacktrack;
                        case Undecided: all_true = false; break;
                        }

                    // With every literal true the forward half has nothing
                    // left to force, which settles it until backtrack too.
                    if (all_true) {
                        if (! backwards)
                            return PropagatorState::DisableUntilBacktrack;
                        auto justf = [&](const ReasonLiterals & reason) {
                            for (auto & l : lits)
                                logger->emit_rup_proof_line_under_reason(reason, WPBSum{} + 1_i * l >= 1_i, ProofLevel::Temporary);
                        };
                        Reason reason;
                        if (inference.want_reasons()) {
                            ReasonLiterals reason_lits;
                            for (auto & l : lits)
                                reason_lits.push_back(l);
                            reason = Reason{ExplicitReason{move(reason_lits)}};
                        }
                        inference.infer(logger, full_reif, JustifyExplicitly{justf, ThenRUP::Yes, Hint_{owner}}, reason);
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
    //
    // The half-reified forms (`and_if` / `or_if`) are the pos row alone,
    // which is exactly the direction they state. cake_pb_cp has no rule for
    // either keyword yet, so they do not chain; the rule to ask it for is this
    // pos row, under the same label.
    auto define_cake_logical(ProofModel & model, const ConstraintID & id, const Literals & lits, const Literal & full_reif, bool is_and, bool half)
        -> void
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
        if (! half)
            model.add_labelled_constraint(id, "neg", move(neg) >= 0_i);
    }

    // The `and` / `or` scp term: cake reads `(op ((Z op v) ...) (Y op v))`,
    // one reification tuple per operand plus one for the reification. The
    // half-reified `and_if` / `or_if` take the same shape, the final tuple
    // being the condition. Every literal maps directly (see reify_tuple_term);
    // a view-conditioned operand is written faithfully as a tuple over its
    // view, which cake's var/const parser rejects so the instance skips the
    // chain, and read_scp round-trips the tuples either way.
    auto s_expr_logical(
        const NamesAndIDsTracker & tracker, const ConstraintID & id, const string & op, const Literals & lits, const Literal & full_reif) -> SExpr
    {
        vector<SExpr> terms;
        for (const auto & lit : lits)
            terms.push_back(reify_tuple_term(lit, tracker));
        return SExpr::list({SExpr::atom(as_string(id)), SExpr::atom(op), SExpr::list(move(terms)), reify_tuple_term(full_reif, tracker)});
    }
}

auto gcs::innards::default_clause_watch_threshold() -> size_t
{
    static const size_t threshold = []() -> size_t {
        if (const char * e = std::getenv("GCS_CLAUSE_WATCH_THRESHOLD"))
            return std::strtoull(e, nullptr, 10);
        // Watching overtook the scan between 64 and 192 literals on the
        // clause_watch_bench set covers, depending on the instance, and 128
        // keeps the worst of them near break-even. See
        // dev_docs/refined-triggers.md.
        return 128;
    }();
    return threshold;
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

auto And::with_watch_threshold(optional<size_t> threshold) -> And &
{
    _watch_threshold = threshold;
    return *this;
}

auto And::clone() const -> unique_ptr<Constraint>
{
    auto result = make_unique<And>(_lits, _full_reif);
    result->with_watch_threshold(_watch_threshold);
    return result;
}

auto And::prepare(Propagators &, State & initial_state, ProofModel * const) -> bool
{
    _reif_state = initial_state.test_literal(_full_reif);
    return true;
}

auto And::define_proof_model(ProofModel & model, const State &) -> void
{
    define_cake_logical(model, _constraint_id, _lits, _full_reif, true, false);
}

auto And::install_propagators(Propagators & propagators) -> void
{
    install_propagators_logical<hints::And>(propagators, constraint_id(), _lits, _full_reif, _reif_state, Halves::Both, _watch_threshold);
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

auto Or::with_watch_threshold(optional<size_t> threshold) -> Or &
{
    _watch_threshold = threshold;
    return *this;
}

auto Or::clone() const -> unique_ptr<Constraint>
{
    auto result = make_unique<Or>(_lits, _full_reif);
    result->with_watch_threshold(_watch_threshold);
    return result;
}

auto Or::prepare(Propagators &, State & initial_state, ProofModel * const) -> bool
{
    _reif_state = initial_state.test_literal(! _full_reif);
    return true;
}

auto Or::define_proof_model(ProofModel & model, const State &) -> void
{
    define_cake_logical(model, _constraint_id, _lits, _full_reif, false, false);
}

auto Or::install_propagators(Propagators & propagators) -> void
{
    // Or is the And propagator over the negated literals and reification.
    Literals lits = _lits;
    for (auto & l : lits)
        l = ! l;
    install_propagators_logical<hints::Or>(propagators, constraint_id(), move(lits), ! _full_reif, _reif_state, Halves::Both, _watch_threshold);
}

auto Or::constraint_type() const -> std::string
{
    return "or";
}

auto Or::s_expr(const innards::ProofModel * const model) const -> SExpr
{
    return s_expr_logical(model->names_and_ids_tracker(), _constraint_id, constraint_type(), _lits, _full_reif);
}

AndIf::AndIf(const vector<IntegerVariableID> & vars, const IntegerVariableID & cond) : AndIf(to_lits(vars), cond != 0_i)
{
}

AndIf::AndIf(Literals l, const Literal & cond) : _lits(move(l)), _cond(cond)
{
}

auto AndIf::clone() const -> unique_ptr<Constraint>
{
    return make_unique<AndIf>(_lits, _cond);
}

auto AndIf::prepare(Propagators &, State & initial_state, ProofModel * const) -> bool
{
    _cond_state = initial_state.test_literal(_cond);
    return true;
}

auto AndIf::define_proof_model(ProofModel & model, const State &) -> void
{
    define_cake_logical(model, _constraint_id, _lits, _cond, true, true);
}

auto AndIf::install_propagators(Propagators & propagators) -> void
{
    install_propagators_logical<hints::And>(propagators, constraint_id(), _lits, _cond, _cond_state, Halves::ReifImpliesConjunction, nullopt);
}

auto AndIf::constraint_type() const -> std::string
{
    return "and_if";
}

auto AndIf::s_expr(const innards::ProofModel * const model) const -> SExpr
{
    return s_expr_logical(model->names_and_ids_tracker(), _constraint_id, constraint_type(), _lits, _cond);
}

OrIf::OrIf(const vector<IntegerVariableID> & vars, const IntegerVariableID & cond) : OrIf(to_lits(vars), cond != 0_i)
{
}

OrIf::OrIf(Literals l, const Literal & cond) : _lits(move(l)), _cond(cond)
{
}

auto OrIf::with_watch_threshold(optional<size_t> threshold) -> OrIf &
{
    _watch_threshold = threshold;
    return *this;
}

auto OrIf::clone() const -> unique_ptr<Constraint>
{
    auto result = make_unique<OrIf>(_lits, _cond);
    result->with_watch_threshold(_watch_threshold);
    return result;
}

auto OrIf::prepare(Propagators &, State & initial_state, ProofModel * const) -> bool
{
    _cond_state = initial_state.test_literal(! _cond);
    return true;
}

auto OrIf::define_proof_model(ProofModel & model, const State &) -> void
{
    define_cake_logical(model, _constraint_id, _lits, _cond, false, true);
}

auto OrIf::install_propagators(Propagators & propagators) -> void
{
    // As for Or, over the negated literals and condition, keeping only the
    // half that says all the literals being false forces the condition false.
    Literals lits = _lits;
    for (auto & l : lits)
        l = ! l;
    install_propagators_logical<hints::Or>(
        propagators, constraint_id(), move(lits), ! _cond, _cond_state, Halves::ConjunctionImpliesReif, _watch_threshold);
}

auto OrIf::constraint_type() const -> std::string
{
    return "or_if";
}

auto OrIf::s_expr(const innards::ProofModel * const model) const -> SExpr
{
    return s_expr_logical(model->names_and_ids_tracker(), _constraint_id, constraint_type(), _lits, _cond);
}
