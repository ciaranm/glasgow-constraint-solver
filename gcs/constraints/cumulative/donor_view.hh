#ifndef GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_CONSTRAINTS_CUMULATIVE_DONOR_VIEW_HH
#define GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_CONSTRAINTS_CUMULATIVE_DONOR_VIEW_HH

#include <gcs/constraint_id.hh>
#include <gcs/constraints/cumulative/cumulative.hh>
#include <gcs/innards/proofs/proof_line.hh>
#include <gcs/innards/proofs/proof_logger-fwd.hh>
#include <gcs/innards/state-fwd.hh>
#include <gcs/integer.hh>
#include <gcs/variable_id.hh>

#include <cstddef>
#include <optional>
#include <vector>

namespace gcs::innards
{
    /**
     * \brief A posted Cumulative as a would-be deriver can speak about it: its
     * arguments reduced to constants, and the tasks that reduction had to set
     * aside.
     *
     * Everything a derived Cumulative does is an argument about the donor's
     * per-time capacity rows, and those rows are only over `height x active`
     * with a constant right hand side when every argument is a constant. This
     * is what a presolver builds to find out how much of a donor it can work
     * with, and every presolver in the tree builds the same one rather than a
     * fourth copy of the same three tests.
     *
     * The restrictions are made per *task* rather than per donor, which is the
     * whole point: one task with a variable length no longer costs a donor its
     * strengthening. A set-aside task is weakened out of every row derived from
     * this donor and given a zero length in the derived constraint, so it has
     * no flags to pin and no term to argue over --- see
     * recover_constant_argument_row.
     *
     * \ingroup Innards
     */
    struct CumulativeDonorView
    {
        /// Per task, in the donor's own order, and **zero for a set-aside
        /// task**: a length or height that is not a constant is not a number
        /// this constraint may quote. Pass these straight to
        /// derived_cumulative_tasks_from, whose zero-length tasks are excluded
        /// exactly as a posted Cumulative excludes its own.
        std::vector<Integer> lengths, heights;

        /// Per task, the presence argument as posted, for
        /// derived_cumulative_tasks_from.
        std::vector<IntegerVariableID> presences;

        /// The task positions a derived constraint may speak about: a constant
        /// non-zero length and height, and not constantly absent.
        std::vector<std::size_t> usable;

        /// The task positions set aside for a variable length or height, whose
        /// terms every derived row has to be weakened over. Not an error and
        /// not a decline: what is lost is those tasks' contribution to the
        /// argument, which makes it weaker rather than wrong.
        std::vector<std::size_t> set_aside;

        /// The capacity to argue against: the posted constant, or a variable
        /// capacity's upper bound as it stands now.
        Integer capacity = 0_i;

        /// Set when \ref capacity came from a variable rather than being
        /// posted, in which case every derived row has to buy it. See
        /// recover_constant_argument_row.
        std::optional<IntegerVariableID> capacity_bounded_by;
    };

    /**
     * \brief Build the view of a donor, or nullopt if its capacity cannot be
     * reduced to a number at all --- which today means a view capacity, whose
     * bits are not the ones the row mentions.
     *
     * `state` supplies a variable capacity's current upper bound, which is the
     * number the rows will be derived against. A view with an empty \ref usable
     * is not an error: it says the donor has nothing a derived constraint could
     * speak about, which is the caller's own "nothing to gain" answer.
     *
     * \ingroup Innards
     */
    [[nodiscard]] auto cumulative_donor_view(const Cumulative & donor, const State & state) -> std::optional<CumulativeDonorView>;

    /**
     * \brief Reduce one of a donor's capacity rows to the form a recipe argues
     * over: constant coefficients on activity flags, and a constant right hand
     * side.
     *
     * Two things happen, and both are the same one `pol`. A set-aside task's
     * terms are weakened away --- `w` on its activity flag, or on each bit of
     * its linearised contribution where its height is a variable, which is what
     * ConstraintProofModelData<Cumulative>::contribution_flag_key is published
     * for. And a variable capacity is replaced by a number, by resolving the
     * order literal for the bound it currently has and letting the capacity's
     * bits cancel against the row's.
     *
     * Working from the bound the capacity has *now* rather than from its
     * declared one is the point of going through the order literal: a
     * presolver reads a live State, and the root bound row would be a
     * different, weaker number the moment anything had tightened it. The
     * literal's definition brings the bits, and what is left over is the
     * literal itself, paid off in the same `pol` by the unit line saying it is
     * false --- which holds permanently, the bound having been reached before
     * the search started, so the row that comes back is unconditional and
     * exact. It has to be exact: a recipe pins what it returns with an `ia`,
     * and every `pol` the propagator later builds on it cancels term by term.
     *
     * Returns the row unchanged when there is nothing to do, which is the
     * all-constant case and so the common one: no `pol`, no line, and a proof
     * byte-identical to the one written before any of this existed.
     *
     * \ingroup Innards
     */
    [[nodiscard]] auto recover_constant_argument_row(
        ProofLogger &, const CumulativeDonorView &, const ConstraintID & donor, ProofLine row, Integer t, ProofLevel) -> std::optional<ProofLine>;
}

#endif
