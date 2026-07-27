#ifndef GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_INNARDS_PROOFS_SCP_WRITER_HH
#define GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_INNARDS_PROOFS_SCP_WRITER_HH

#include <gcs/innards/proofs/proof_model-fwd.hh>
#include <gcs/problem-fwd.hh>

#include <string>

namespace gcs
{
    namespace innards
    {
        /**
         * \brief Write the `.scp` (s-expression CP) description of `problem` to
         * `file_name`.
         *
         * The file is the version-1 s-expression `( (version 1) (variables
         * var-decls...) (constraints constraint...) (prob_type spec) )`, where
         * each variable is `(name lb ub)`, each constraint is the term from
         * Constraint::s_expr(), and `spec` is `(minimize var)` / `(maximize
         * var)` for an objective and the bare atom `enumerate` otherwise.
         * Throws ProofError on an I/O failure. This is the single place the
         * `.scp` is serialised; constraints contribute only their own term.
         */
        auto write_scp(const std::string & file_name, const Problem & problem, const ProofModel * model) -> void;
    }
}

#endif
