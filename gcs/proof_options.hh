#ifndef GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_PROOF_OPTIONS_HH
#define GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_PROOF_OPTIONS_HH

#include <string>

namespace gcs
{
    /**
     * \brief Options for a Problem telling it how to produce a proof.
     *
     * \sa Problem
     * \ingroup Core
     */
    struct ProofOptions
    {
        explicit ProofOptions(const std::string &, const std::string &);
        explicit ProofOptions(const std::string &, const std::string &, bool);
        ProofOptions(const ProofOptions &) = default;

        std::string opb_file;           ///< Filename for the OPB model
        std::string proof_file;         ///< Filename for the proof file
        bool use_friendly_names = true; ///< Use verbose names, rather than just x1, x2, etc.
    };
}

#endif
