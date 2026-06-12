#ifndef GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_INNARDS_PROOF_PROOF_ERROR_HH
#define GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_INNARDS_PROOF_PROOF_ERROR_HH

#include <gcs/exception.hh>

#include <string>

namespace gcs::innards
{
    /**
     * \brief Thrown if something Proof related goes wrong.
     *
     * \ingroup Innards
     */
    class ProofError : public MessageException
    {
    public:
        explicit ProofError(const std::string &);
    };
}

#endif
