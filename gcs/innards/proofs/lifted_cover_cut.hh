#ifndef GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_INNARDS_PROOFS_LIFTED_COVER_CUT_HH
#define GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_INNARDS_PROOFS_LIFTED_COVER_CUT_HH

#include <gcs/innards/proofs/proof_line.hh>
#include <gcs/innards/proofs/proof_logger-fwd.hh>
#include <gcs/innards/proofs/proof_only_variables.hh>
#include <gcs/integer.hh>

#include <compare>
#include <cstddef>
#include <optional>
#include <vector>

namespace gcs::innards
{
    /**
     * \brief One state of the knapsack dynamic programme that says a lifted
     * cover cut holds.
     *
     * Every 0/1 point reaching this state puts **at least** `weights[r]` on the
     * `r`th capacity row's left-hand side and **at most** `profit` on the cut's.
     * Both halves are one-sided on purpose: it is what lets one state stand for
     * a whole family of points, and what lets a state that uses less of every
     * resource while allowing more on the cut absorb another outright.
     *
     * There is one weight per row the cut is derived from, because Sidorov's
     * lifting subproblem (his Equation 4) constrains over every resource at
     * once, and a cut lifted that way is a consequence of those rows together
     * rather than of any one of them. Nothing about that needs the rows scaled
     * against each other or added together: each is used only to say that a
     * particular transition cannot happen, which is exactly the use the single
     * row got.
     *
     * \ingroup Innards
     */
    struct LiftedCoverCutState
    {
        std::vector<Integer> weights;
        Integer profit;

        [[nodiscard]] auto operator<=>(const LiftedCoverCutState &) const = default;
    };

    /**
     * \brief The states some prefix of a cut's members can reach, with none of
     * them covering another.
     *
     * What is left after states another state already covers are dropped is an
     * antichain: no member of it uses no more of every resource while allowing
     * no less on the cut than another does. Over a single row that is a
     * staircase, so a layer holds at most one state per achievable profit and
     * cannot be wider than the right-hand side plus one. Over several it is a
     * Pareto frontier and no such bound holds a priori, which is why
     * \ref validate_lifted_cover_cut takes a budget.
     *
     * \ingroup Innards
     */
    using LiftedCoverCutLayer = std::vector<LiftedCoverCutState>;

    /**
     * \brief A lifted cover inequality `sum_i coefficients[i] a_i <= rhs`, and
     * the dynamic programme that says it follows from the capacity rows
     * `sum_i demands[r][i] a_i <= capacities[r]`.
     *
     * \ingroup Innards
     */
    struct LiftedCoverCut
    {
        /// One row per entry, each with one demand per member. Only the rows
        /// that can actually rule a transition out are kept; \ref row_indices
        /// says which of the caller's rows these are.
        std::vector<std::vector<Integer>> demands;
        std::vector<Integer> capacities;
        std::vector<std::size_t> row_indices;

        std::vector<Integer> coefficients;
        Integer rhs;

        /// One entry per prefix of the members, from the empty one to all of
        /// them, so `layers.size()` is `coefficients.size() + 1`.
        std::vector<LiftedCoverCutLayer> layers;
    };

    /**
     * \brief Why there is no cut, when there is no cut: because it is false, or
     * because its programme would have been too large to emit.
     *
     * Worth telling apart even though a caller does the same thing with both,
     * because they say opposite things about the inference. A false cut is a
     * caller that asked for something untrue; a programme over budget is a cut
     * that may well be true and that this cannot certify, which is the number
     * the design of this file exists to keep at zero.
     *
     * \ingroup Innards
     */
    struct LiftedCoverCutValidity
    {
        std::optional<LiftedCoverCut> cut;
        bool over_state_budget = false;
    };

    /**
     * \brief Decide whether a lifted cover cut follows from some capacity rows,
     * by running the knapsack dynamic programme that will later be its
     * certificate.
     *
     * Returns no cut exactly when the cut is *false* --- when some 0/1 point
     * the rows jointly allow breaks it --- or when its programme would build
     * more than `state_budget` states. Barring that budget there is no third answer:
     * every valid cut gets a dynamic programme and every dynamic programme
     * becomes a proof, which is the whole point of doing it this way. The
     * earlier design searched for a short cutting-planes derivation and refused
     * about one valid cut in twenty-five, and a refusal there meant a constraint
     * the published inference procedure would have posted was dropped.
     *
     * The programme is the textbook one. A state after the first `i` members is
     * a (weights, profit) tuple some assignment to those members reaches; a
     * successor either leaves the next member out, or takes it and pays its
     * demand on every row. A successor that would overrun *some* capacity is not
     * created at all, because that row forbids it --- which is the only place a
     * row is used, and is why the cut is a consequence of the rows. States
     * another state covers are then dropped, so a layer holds only the frontier.
     *
     * Rows that cannot rule anything out --- those whose members' demands sum to
     * no more than the capacity --- are dropped before any of that, since a
     * weight bound against one would be a flag per state saying nothing. That is
     * a simplification rather than a restriction: such a row admits every subset
     * of the members, so no derivation could have used it.
     *
     * A cover is a set of members whose demands overshoot a capacity, and
     * lifting is what brings the others in with coefficients large enough to
     * keep the inequality valid --- which is what produces the non-unit
     * coefficients that make such a cut say something the rows do not. None of
     * that appears here: which cut to aim for is the caller's business (see
     * InferredCumulative, which reproduces a published procedure's choice), and
     * this decides only whether the answer is true and assembles the reason.
     *
     * \ingroup Innards
     */
    [[nodiscard]] auto validate_lifted_cover_cut(const std::vector<std::vector<Integer>> & demands, const std::vector<Integer> & coefficients,
        const std::vector<Integer> & capacities, Integer rhs, std::size_t state_budget) -> LiftedCoverCutValidity;

    /**
     * \brief The answer to a lifting subproblem: what the left-hand side can
     * reach, unless that is at least the ceiling it was asked about, or the
     * programme was over budget.
     *
     * \ingroup Innards
     */
    struct LiftedCoverCutOptimum
    {
        std::optional<Integer> value;
        bool over_state_budget = false;
    };

    /**
     * \brief The largest the cut's left-hand side can be at any 0/1 point the
     * rows jointly allow, or nothing if that reaches `profit_ceiling`.
     *
     * This is Sidorov's lifting subproblem: the answer decides the coefficient a
     * task is lifted in with, as `rhs - v*`, and a `v*` at or above the
     * right-hand side means there is no positive coefficient to give it. So a
     * caller only ever needs the answer up to `rhs`, and capping it is what
     * keeps the frontier narrow enough to index by profit --- the same reason
     * the programme certifying the finished cut is affordable.
     *
     * The answer is exact, not an over-estimate, which matters because a `v*`
     * one too large is a coefficient one too small: a weaker cut than the
     * published procedure's, and so a different constraint. Dropping a covered
     * state cannot inflate it, because every state kept is a tuple some 0/1
     * point reaches exactly, and a state only ever covers one whose profit is no
     * larger.
     *
     * Shares the dynamic programme with \ref validate_lifted_cover_cut, which is
     * not an economy but the point: the inference and the certificate are then
     * the same computation, so a cut the procedure produces cannot be one the
     * proof fails to reach.
     *
     * \ingroup Innards
     */
    [[nodiscard]] auto lifted_cover_cut_optimum(const std::vector<std::vector<Integer>> & demands, const std::vector<Integer> & coefficients,
        const std::vector<Integer> & capacities, Integer profit_ceiling, std::size_t state_budget) -> LiftedCoverCutOptimum;

    /**
     * \brief Derive a validated lifted cover cut from its capacity rows, by
     * replaying its dynamic programme in the proof.
     *
     * The shape is Demirović et al.'s (CP 2024), in its one-sided form: an
     * extension variable per row per state reifying "at least this much weight",
     * one reifying "at most this much profit", and one for their conjunction; an
     * implication per transition; an at-least-one per layer, saying the frontier
     * is complete; and, at the last layer, one flag reifying the cut itself,
     * which every final state contradicts. Nothing here is a search, so nothing
     * here can fail on a cut \ref validate_lifted_cover_cut accepted.
     *
     * `capacity_rows` and `weaken_out` are parallel to the rows the cut
     * *retained*, so a caller with a row that could not bind reads
     * `LiftedCoverCut::row_indices` to find out it does not need to produce a
     * line for it at all. **Every row must be expressed in the same `flags`**,
     * which for rows belonging to different constraints means bridging them
     * first --- recover_bridged_row does that, and is the only thing standing
     * between this and a cut spanning several resources.
     *
     * `flags` are the members' activity flags, parallel to the cut's
     * coefficients; `weaken_out[r]` names every *other* task with a term in row
     * `r`. Getting that list wrong costs proof size rather than soundness: the
     * one step it feeds is the `pol` ruling a member out, and saturation forces
     * the member out whatever else is left in the row. What the list buys is
     * that the step lands on a two-literal clause rather than on something as
     * wide as the donor.
     *
     * The scaffolding is emitted one proof level deeper than the caller's, and
     * forgotten on the way out --- the extension variables along with it, since
     * deleting a variable's two defining constraints deletes the variable. Only
     * the pinned result survives, so a derived constraint over a long horizon
     * leaves one live line per time point rather than one per state.
     *
     * The pin is an `ia` against the derived cut, and it normalises: whatever
     * shape the last `pol` left behind, the caller gets the literal-exact
     * inequality it asked for, which is what a derived Cumulative's propagator
     * will go on to cite. `claimed_coefficients` and `claimed_rhs` are what it
     * says; they are the cut's own for every real caller, and a test passes
     * something one better to check that veripb refuses to pin it.
     *
     * \ingroup Innards
     */
    [[nodiscard]] auto derive_lifted_cover_cut(ProofLogger &, const std::vector<ProofLine> & capacity_rows, const LiftedCoverCut &,
        const std::vector<ProofFlag> & flags, const std::vector<Integer> & claimed_coefficients,
        const std::vector<std::vector<ProofFlag>> & weaken_out, Integer claimed_rhs, ProofLevel) -> ProofLine;
}

#endif
