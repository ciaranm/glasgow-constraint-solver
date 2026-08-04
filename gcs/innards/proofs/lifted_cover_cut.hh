#ifndef GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_INNARDS_PROOFS_LIFTED_COVER_CUT_HH
#define GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_INNARDS_PROOFS_LIFTED_COVER_CUT_HH

#include <gcs/innards/proofs/proof_line.hh>
#include <gcs/innards/proofs/proof_logger-fwd.hh>
#include <gcs/innards/proofs/proof_only_variables.hh>
#include <gcs/integer.hh>

#include <cstddef>
#include <optional>
#include <vector>

namespace gcs::innards
{
    /**
     * \brief One `pol` of a lifted cover cut's derivation.
     *
     * Each step weakens the capacity row down to `support`, takes `row_copies`
     * of it and `cut_copies` of the step before, optionally saturates, and
     * divides. The first step has no step before it and so no `cut_copies`; it
     * is the plain cover cut, and on most inputs it is also the only step.
     *
     * \ingroup Innards
     */
    struct LiftedCoverCutStep
    {
        /// Which members, by index into the caller's parallel vectors, are left
        /// in the row. Everything else is weakened away, which drops its term
        /// and takes its demand off the degree.
        std::vector<std::size_t> support;

        Integer row_copies;

        /// Zero on the first step.
        Integer cut_copies;

        bool saturate;

        Integer divisor;
    };

    /**
     * \brief How to get from a capacity row to a lifted cover cut.
     *
     * Empty means the cut is true of every 0/1 point --- which happens at the
     * edges of a derived constraint's window, where so few of its tasks have
     * flags that their coefficients cannot reach the right-hand side --- so one
     * RUP establishes it and no arithmetic is needed.
     *
     * \ingroup Innards
     */
    using LiftedCoverCutPlan = std::vector<LiftedCoverCutStep>;

    /**
     * \brief Find a cutting-planes derivation of `sum pi_i a_i <= rhs` from a
     * capacity row `sum c_i a_i <= C`, or say there is none to be had.
     *
     * **Provisional.** This searches for a short derivation and fails on about
     * one candidate in twenty-five. The agreed replacement is issue #675:
     * proof-log the knapsack dynamic programme that produced the coefficient in
     * the first place, which is complete by construction and would delete this
     * function, the normalised-form model behind it and the `ia` pin that
     * guards that model. Do not widen the search here to close the gap --- take
     * the DP, and look for something shorter only once proof size or checking
     * time is demonstrably a problem.
     *
     * The cut is *given* and not up for negotiation. That is the position
     * every caller is in: InferredCumulative reproduces a published inference
     * procedure, so the constraint to be posted is decided before any of this
     * runs, and a constraint no derivation reaches is dropped rather than
     * traded for one that happens to be easier.
     *
     * A *cover* is a set of tasks whose demands overshoot the capacity, and its
     * cover inequality says they cannot all run. *Lifting* then brings the
     * remaining tasks in with coefficients large enough to stay valid, which is
     * what produces a cut with non-unit coefficients --- a statement about the
     * resource that its own row does not make, and the whole point of the
     * exercise. Which cut to aim for is the caller's business (see
     * InferredCumulative, which searches for the one carrying the most energy);
     * this is the part that has to convince a proof checker, and it takes the
     * cut as given.
     *
     * Validity of a lifted inequality is coNP-hard to decide in general, so
     * nothing here trusts the caller's claim: the search is over *derivations*,
     * and it succeeds only when the arithmetic lands on the claimed
     * coefficients and right-hand side exactly. A cut that is valid but that
     * this cannot derive is refused rather than asserted --- an uncertified
     * constraint would be a change to the statement being verified rather than
     * a consequence of it.
     *
     * Three shapes are tried, cheapest first.
     *
     *  1. Nothing at all, when `sum pi_i - rhs <= 0` leaves a degree no 0/1
     *     point can miss.
     *  2. One `pol`: weaken the row down to the members, saturate or not, and
     *     divide. This is \ref build_am1_from_row's program with the divisor
     *     free rather than fixed at the one giving unit coefficients, and it is
     *     what the overwhelming majority of inputs need --- including most
     *     restrictions of a cut to the members present at one time point.
     *  3. A cover, and then one `pol` per lifted member: `row_copies` of the
     *     row weakened to the support so far plus the new member, and
     *     `cut_copies` of the cut so far, divided. This is where the non-unit
     *     coefficients reachable today come from --- `2a + b + c + d <= 2` from
     *     `5a + 2b + 2c + 2d <= 5` is one copy of each, over three.
     *
     * Missing from that vocabulary, and worth knowing about before extending
     * it: `pol` can also push a **literal axiom**, which cancels against that
     * literal's complement and so shaves *part* of a coefficient where `w` can
     * only remove all of it. With one copy of `a >= 0` the example above is a
     * single `pol` --- `pol 1 aa + 2 d`, checked exact against veripb --- so
     * "non-unit needs a chain" is not true, only "non-unit needs more than
     * weaken/saturate/divide". The two families are incomparable, so the chain
     * stays either way; see issue #674.
     *
     * `demands` and `coefficients` are parallel and describe the same members
     * in the same order. `max_covers` caps the third shape's search, which is
     * over subsets; every drop it causes is a refusal rather than a wrong
     * answer.
     *
     * \ingroup Innards
     */
    [[nodiscard]] auto plan_lifted_cover_cut(const std::vector<Integer> & demands, const std::vector<Integer> & coefficients, Integer capacity,
        Integer rhs, std::size_t max_covers) -> std::optional<LiftedCoverCutPlan>;

    /**
     * \brief Emit a plan from \ref plan_lifted_cover_cut, and pin what it
     * arrived at.
     *
     * `flags` are the members' activity flags, parallel to the `coefficients`
     * and to the `demands` the plan was made from; `weaken_out` names every
     * other task with a term in the row, which a caller sweeping a donor's
     * positions must give in full rather than stopping at the first task that
     * has no flags.
     *
     * The intermediate steps are emitted one proof level deeper than the
     * caller's, and forgotten on the way out: only the pinned result survives,
     * so a derived constraint over a long horizon leaves one live line per time
     * point rather than one per lifting step per time point. The result is
     * emitted at the level the caller asked for, while the scaffolding is still
     * alive for VeriPB to resolve the references against.
     *
     * The pin is an `ia` against the last step, and it is the only thing that
     * says the derivation arrived where the plan predicted. Its check is
     * syntactic, so it also *normalises*: whatever shape the last `pol` left
     * behind, the caller gets the literal-exact inequality it asked for, which
     * is what a derived Cumulative's propagator will go on to cite.
     *
     * `claimed_coefficients` and `claimed_rhs` are what the pin says. They are
     * the honest ones for every real caller; a test passes something else to
     * check that VeriPB rejects a cut claiming one better than was derived.
     *
     * \ingroup Innards
     */
    [[nodiscard]] auto derive_lifted_cover_cut(ProofLogger &, ProofLine capacity_row, const LiftedCoverCutPlan &,
        const std::vector<ProofFlag> & flags, const std::vector<Integer> & claimed_coefficients, const std::vector<ProofFlag> & weaken_out,
        Integer claimed_rhs, ProofLevel) -> ProofLine;
}

#endif
