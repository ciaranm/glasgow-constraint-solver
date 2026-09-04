#ifndef GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_PRESOLVERS_INNARDS_MAKESPAN_LINKS_HH
#define GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_PRESOLVERS_INNARDS_MAKESPAN_LINKS_HH

#include <gcs/constraints/innards/makespan_energy.hh>
#include <gcs/innards/proofs/proof_logger-fwd.hh>
#include <gcs/problem-fwd.hh>
#include <gcs/variable_id.hh>

#include <map>
#include <optional>

namespace gcs::innards
{
    /**
     * \brief Find, for each start variable the model says must finish by
     * `makespan`, the posted row that says so.
     *
     * A makespan is not a kind of variable, it is a variable a model has put
     * rows around: `makespan - start >= length` for every task. Those rows are
     * what confine the tasks to a window once the makespan is bounded, so an
     * energy argument about the makespan is a `pol` over them and cannot be had
     * without them --- reverse unit propagation will not cross from one
     * variable's bits to another's through a linear row, whatever the bounds
     * say.
     *
     * So this looks for them rather than taking them on trust: a caller naming
     * a variable that is not a makespan gets a task with no link, which costs
     * that task's energy, instead of a rejected proof.
     *
     * Both families, unconditionally-held rows only. From the linear family,
     * two-term rows over plain variables with coefficients `+1` and `-1` ---
     * which is what a scheduling model's makespan rows are, and what MiniZinc's
     * `int_lin_le` flattens them to. From the comparison family, `start + length
     * <= makespan` and `start <= makespan - length`, which say the same thing
     * over an offset view: a view has its own `BinEnc` in the proof, so those
     * rows are not stated in the underlying variables' bits, and
     * makespan_energy cites the row in *deview mode* to put it back in them
     * before the cancellation. A negated view is not this shape at all and is
     * declined.
     *
     * The strongest row wins where a variable has several. With proofs off the
     * links are still found --- which is the point, since the bound they let
     * through has to be the same number either way --- and only
     * MakespanLink::row is left empty.
     *
     * \ingroup Innards
     */
    [[nodiscard]] auto find_makespan_links(const Problem &, const ProofLogger * const, IntegerVariableID makespan)
        -> std::map<IntegerVariableID, makespan_energy::MakespanLink>;
}

#endif
