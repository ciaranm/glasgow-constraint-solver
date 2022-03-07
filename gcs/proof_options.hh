/* vim: set sw=4 sts=4 et foldmethod=syntax : */

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
        std::string opb_file;           ///< Filename for the OPB model
        std::string proof_file;         ///< Filename for the proof file
        bool use_friendly_names = true; ///< Use verbose names, rather than just x1, x2, etc.
    };
}

#endif
