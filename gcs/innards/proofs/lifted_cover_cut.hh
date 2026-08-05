#ifndef GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_INNARDS_PROOFS_LIFTED_COVER_CUT_HH
#define GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_INNARDS_PROOFS_LIFTED_COVER_CUT_HH

#include <gcs/innards/proofs/proof_line.hh>
#include <gcs/innards/proofs/proof_logger-fwd.hh>
#include <gcs/innards/proofs/proof_only_variables.hh>
#include <gcs/integer.hh>

#include <compare>
#include <optional>
#include <vector>

namespace gcs::innards
{
    /**
     * \brief One state of the knapsack dynamic programme that says a lifted
     * cover cut holds.
     *
     * Every 0/1 point reaching this state puts **at least** `weight` on the
     * capacity row's left-hand side and **at most** `profit` on the cut's. Both
     * halves are one-sided on purpose: it is what lets one state stand for a
     * whole family of points, and what lets a state that uses less of the
     * resource while allowing more on the cut absorb another outright.
     *
     * \ingroup Innards
     */
    struct LiftedCoverCutState
    {
        Integer weight, profit;

        [[nodiscard]] auto operator<=>(const LiftedCoverCutState &) const = default;
    };

    /**
     * \brief The states some prefix of a cut's members can reach, in increasing
     * order of both weight and profit.
     *
     * That ordering is not incidental: it is what is left after states another
     * state already covers are dropped, and the last entry is therefore the
     * most the prefix can put on the cut's left-hand side.
     *
     * \ingroup Innards
     */
    using LiftedCoverCutLayer = std::vector<LiftedCoverCutState>;

    /**
     * \brief A lifted cover inequality `sum_i coefficients[i] a_i <= rhs`, and
     * the dynamic programme that says it follows from the capacity row
     * `sum_i demands[i] a_i <= capacity`.
     *
     * \ingroup Innards
     */
    struct LiftedCoverCut
    {
        std::vector<Integer> demands, coefficients;
        Integer capacity, rhs;

        /// One entry per prefix of the members, from the empty one to all of
        /// them, so `layers.size()` is `demands.size() + 1`.
        std::vector<LiftedCoverCutLayer> layers;
    };

    /**
     * \brief Decide whether a lifted cover cut follows from a capacity row, by
     * running the knapsack dynamic programme that will later be its
     * certificate.
     *
     * Returns nothing exactly when the cut is *false* --- when some 0/1 point
     * the row allows breaks it. There is no third answer: every valid cut gets
     * a dynamic programme and every dynamic programme becomes a proof, which is
     * the whole point of doing it this way. The earlier design searched for a
     * short cutting-planes derivation and refused about one valid cut in
     * twenty-five, and a refusal there meant a constraint the published
     * inference procedure would have posted was dropped.
     *
     * The programme is the textbook one. A state after the first `i` members is
     * a (weight, profit) pair some assignment to those members reaches; a
     * successor either leaves the next member out, or takes it and pays its
     * demand. A successor that would overrun the capacity is not created at
     * all, because the row forbids it --- which is the only place the row is
     * used, and is why the cut is a consequence of it. States another state
     * covers are then dropped, so a layer holds only the frontier: strictly
     * increasing weight against strictly increasing profit, at most one state
     * per achievable profit, and so at most `rhs + 1` of them.
     *
     * A cover is a set of members whose demands overshoot the capacity, and
     * lifting is what brings the others in with coefficients large enough to
     * keep the inequality valid --- which is what produces the non-unit
     * coefficients that make such a cut say something the row does not. None of
     * that appears here: which cut to aim for is the caller's business (see
     * InferredCumulative, which reproduces a published procedure's choice), and
     * this decides only whether the answer is true and assembles the reason.
     *
     * \ingroup Innards
     */
    [[nodiscard]] auto validate_lifted_cover_cut(const std::vector<Integer> & demands, const std::vector<Integer> & coefficients, Integer capacity,
        Integer rhs) -> std::optional<LiftedCoverCut>;

    /**
     * \brief Derive a validated lifted cover cut from a capacity row, by
     * replaying its dynamic programme in the proof.
     *
     * The shape is Demirović et al.'s (CP 2024), in its one-sided form: an
     * extension variable per state, reifying "at least this much weight" and
     * "at most this much profit" and their conjunction; an implication per
     * transition; an at-least-one per layer, saying the frontier is complete;
     * and, at the last layer, one flag reifying the cut itself, which every
     * final state contradicts. Nothing here is a search, so nothing here can
     * fail on a cut \ref validate_lifted_cover_cut accepted.
     *
     * `flags` are the members' activity flags, parallel to the cut's `demands`
     * and `coefficients`; `weaken_out` names every *other* task with a term in
     * the row, which a caller sweeping a donor's positions must give in full
     * rather than stopping at the first task that has no flags.
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
    [[nodiscard]] auto derive_lifted_cover_cut(ProofLogger &, ProofLine capacity_row, const LiftedCoverCut &, const std::vector<ProofFlag> & flags,
        const std::vector<Integer> & claimed_coefficients, const std::vector<ProofFlag> & weaken_out, Integer claimed_rhs, ProofLevel) -> ProofLine;
}

#endif
