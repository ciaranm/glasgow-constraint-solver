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
    class ProofError : public std::exception
    {
    private:
        std::string _wat;

    public:
        explicit ProofError(const std::string &);

        virtual auto what() const noexcept -> const char * override;
    };
}

#endif
