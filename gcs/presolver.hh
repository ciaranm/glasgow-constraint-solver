#ifndef GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_PRESOLVER_HH
#define GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_PRESOLVER_HH

#include <gcs/innards/proofs/proof_logger-fwd.hh>
#include <gcs/innards/propagators-fwd.hh>
#include <gcs/innards/state-fwd.hh>
#include <gcs/problem-fwd.hh>

#include <memory>
#include <optional>
#include <string>

namespace gcs
{
    /**
     * \defgroup Presolvers Presolvers
     */

    /**
     * \brief Presolvers influence the solving process, for example by creating
     * new implied constraints or simplifying existing constraints.
     *
     * \ingroup Core
     */
    class [[nodiscard]] Presolver
    {
    public:
        virtual ~Presolver() = 0;

        /**
         * Called internally to execute the presolving process. Returns false if
         * unsatisfiability was detected.
         */
        [[nodiscard]] virtual auto run(Problem &, innards::Propagators &, innards::State &,
            innards::ProofLogger * const) -> bool = 0;

        /**
         * Create a copy of the presolver. To be used internally.
         */
        [[nodiscard]] virtual auto clone() const -> std::unique_ptr<Presolver> = 0;
    };
}

#endif
