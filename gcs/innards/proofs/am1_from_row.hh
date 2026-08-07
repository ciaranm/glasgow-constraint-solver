#ifndef GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_INNARDS_PROOFS_AM1_FROM_ROW_HH
#define GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_INNARDS_PROOFS_AM1_FROM_ROW_HH

#include <gcs/innards/proofs/names_and_ids_tracker-fwd.hh>
#include <gcs/innards/proofs/pol_builder.hh>
#include <gcs/innards/proofs/proof_line.hh>
#include <gcs/innards/proofs/proof_logger-fwd.hh>
#include <gcs/innards/proofs/proof_only_variables.hh>
#include <gcs/integer.hh>

#include <vector>

namespace gcs::innards
{
    /**
     * \brief What recover_am1_from_row() got out of the row.
     *
     * \ingroup Innards
     */
    struct Am1FromRow
    {
        ProofLine line;

        /// How many of the members the line says can be active at once. One is
        /// the at-most-one the callers usually want; more is a *cardinality*
        /// bound, which is still a real cut and is what a set with no
        /// conflicting pair in it yields. Callers that need the at-most-one
        /// must check this rather than assume it.
        Integer at_most;
    };

    /**
     * \brief Push, onto a `pol` under construction, the recovery of a
     * cardinality bound over some of a capacity row's tasks: given
     * `sum c_k a_k <= C` and a set `K` of its tasks that together overshoot
     * `C`, recover `sum_{K} a_i <= |K| - ceil(Delta / d)`.
     *
     * Nothing clever happens here. The bound is obvious --- tasks that do not
     * fit together cannot all run --- and every step exists only because a
     * proof checker cannot see that for itself. Weaken every task outside `K`
     * out of the row, which drops its term and takes its coefficient off the
     * degree, leaving `sum_{K} c_i ~a_i >= Delta` with `Delta = sum_{K} c_i -
     * C`. Saturate, capping each coefficient at `Delta`. Then divide by
     * `d = min(max_{K} c_i, Delta)`, which is the smallest divisor that brings
     * every capped coefficient down to one and therefore the one giving the
     * strongest bound.
     *
     * The **pairwise at-most-one is this at `|K| = 2`**, and not a separate
     * program: two demands that overshoot give `Delta = c_u + c_v - C`, which
     * is at most `max(c_u, c_v)` exactly when the smaller of them fits under
     * the capacity, so `d` is that margin and the bound is always one. Callers
     * wanting the pairwise case pass two members and need not special-case
     * anything.
     *
     * From three members up the bound is `|K| - 1` --- a clique inequality ---
     * when `Delta > d * (|K| - 2)`, and weaker otherwise. Both outcomes are
     * useful and the caller is told which it got. In particular a set with *no*
     * conflicting pair at all still yields a cardinality cut, which nothing
     * assembled out of pairwise at-most-ones could ever produce.
     *
     * Whenever the members share a row, this is what to use, rather than
     * recovering `|K|(|K|-1)/2` pairwise at-most-ones and folding them with
     * recover_am1_from_pairs(): one `pol` against `O(|K|^2)` of them, and a
     * stronger result. The fold is for members that have no row in common,
     * which is what an inference spanning several resources produces.
     *
     * `weaken_out` must name *every* task with a term in the row that is not in
     * `K`. A task that demands nothing has no term and no flag, so a caller
     * sweeping a donor's positions should skip the ones without flags and carry
     * on rather than stopping at the first --- stopping there would leave the
     * later tasks' terms in, and the degree would then exceed `Delta` and the
     * division would land somewhere weaker.
     *
     * Nothing is emitted: the caller decides whether this is a line of its own
     * (\ref recover_am1_from_row) or the opening of a longer `pol` that goes on
     * to carry the bound somewhere else, which is what an inferred constraint
     * over several resources needs. Nor is the result pinned with an `ia` step.
     * Every step here is sound whatever it is fed, so wrong demands land on a
     * weaker line and nothing objects until something says what the line is
     * meant to be --- that pin belongs to whatever the caller finally claims,
     * and both in-tree callers have one.
     *
     * Returns the bound the line will carry. Throws if the members do not
     * overshoot the capacity: a set that fits has no bound to recover, and
     * dividing by zero is not a proof step.
     *
     * \ingroup Innards
     */
    auto build_am1_from_row(PolBuilder & into, ProofLine capacity_row, const std::vector<Integer> & member_demands,
        const std::vector<ProofFlag> & weaken_out, Integer capacity, const NamesAndIDsTracker &) -> Integer;

    /**
     * \brief \ref build_am1_from_row, emitted as a line of its own.
     *
     * \ingroup Innards
     */
    [[nodiscard]] auto recover_am1_from_row(ProofLogger &, ProofLine capacity_row, const std::vector<Integer> & member_demands,
        const std::vector<ProofFlag> & weaken_out, Integer capacity, ProofLevel) -> Am1FromRow;
}

#endif
