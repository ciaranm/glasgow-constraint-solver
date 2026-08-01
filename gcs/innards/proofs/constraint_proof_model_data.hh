#ifndef GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_INNARDS_PROOFS_CONSTRAINT_PROOF_MODEL_DATA_HH
#define GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_INNARDS_PROOFS_CONSTRAINT_PROOF_MODEL_DATA_HH

#include <gcs/constraint_id.hh>
#include <gcs/innards/proofs/proof_line.hh>
#include <gcs/innards/proofs/proof_logger-fwd.hh>

#include <optional>
#include <string>

namespace gcs::innards
{
    /**
     * \brief How a constraint publishes the parts of its OPB output that other
     * code is allowed to build proof steps on.
     *
     * Every labelled row a define_proof_model emits is, today, implicitly public
     * API: anything can construct the label `c[id][role]` and cite it. That is
     * how the difference-logic presolver started out, and it is a bad contract
     * in both directions --- the citer is guessing at another constraint's
     * naming scheme, and the constraint's author has no way of knowing that
     * renaming a role breaks somebody.
     *
     * Specialising this turns that into a declaration. The specialisation lives
     * in the constraint's own header, beside its posted-argument accessors,
     * which is the place where the dependency is visible to the person most
     * likely to break it. What it publishes is the *role name*, not a line
     * number or a label: a role is stable across solves, clones and threads,
     * whereas a line number is a position in one particular file.
     *
     * The primary template is deliberately left undefined, so asking a
     * constraint that publishes nothing is a compile error naming the type,
     * rather than a nullopt to be handled at runtime. A constraint that has no
     * stable rows should stay unspecialised.
     *
     * A published role answers "which row do you mean", not "does that row
     * exist": a role whose reification kind was never emitted has no row.
     * NamesAndIDsTracker::constraint_row_label is the other half, and returns
     * nullopt in exactly that case.
     *
     * \ingroup Innards
     * \sa NamesAndIDsTracker::constraint_row_label
     * \sa Problem::each_constraint_of_type_with_proof_data
     */
    template <typename Constraint_>
    struct ConstraintProofModelData;

    /**
     * \brief NamesAndIDsTracker::constraint_row_label, reached through a
     * ProofLogger.
     *
     * Exists so that Problem::each_constraint_of_type_with_proof_data, which is
     * a template in the public gcs/problem.hh, can resolve a label without
     * problem.hh having to include the whole of proof_logger.hh and
     * names_and_ids_tracker.hh. The logger and the model share one tracker, so
     * this reaches the same set the model claimed into.
     *
     * \ingroup Innards
     */
    [[nodiscard]] auto constraint_row_label_from(const ProofLogger &, const ConstraintID &, const std::string & role)
        -> std::optional<ProofLineLabel>;
}

#endif
