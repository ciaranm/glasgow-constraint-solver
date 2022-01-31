/* vim: set sw=4 sts=4 et foldmethod=syntax : */

#ifndef GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_PROOF_OPTIONS_HH
#define GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_PROOF_OPTIONS_HH 1

#include <string>

namespace gcs
{
    struct ProofOptions
    {
        std::string opb_file;
        std::string proof_file;
        bool use_friendly_names = true;
    };
}

#endif
