#include <gcs/innards/proofs/names_and_ids_tracker.hh>
#include <gcs/innards/proofs/proof_logger.hh>
#include <gcs/innards/proofs/proof_model.hh>
#include <gcs/proof.hh>

#include <cstdlib>
#include <optional>
#include <string>

#include <version>
#if defined(__cpp_lib_print) && defined(__cpp_lib_format)
#include <print>
using std::print;
#else
#include <fmt/core.h>
using fmt::print;
#endif

using namespace gcs;
using namespace gcs::innards;

using std::make_unique;
using std::nullopt;
using std::optional;
using std::string;

namespace
{
    /**
     * Read an AssertionLevel from the GCS_ASSERTION_LEVEL environment variable, if set.
     * Accepts either the enum names (case-insensitive) or their numeric values; an
     * unrecognised value is ignored with a warning.
     */
    [[nodiscard]] auto assertion_level_from_env() -> optional<AssertionLevel>
    {
        const auto * const env = std::getenv("GCS_ASSERTION_LEVEL");
        if (! env || ! *env)
            return nullopt;

        string value{env};
        if (value == "Off" || value == "off" || value == "0")
            return AssertionLevel::Off;
        else if (value == "Definitions" || value == "definitions" || value == "1")
            return AssertionLevel::Definitions;
        else if (value == "Links" || value == "links" || value == "2")
            return AssertionLevel::Links;
        else if (value == "Inferences" || value == "inferences" || value == "3")
            return AssertionLevel::Inferences;
        else if (value == "Backtracking" || value == "backtracking" || value == "4")
            return AssertionLevel::Backtracking;

        print(stderr, "Ignoring unrecognised GCS_ASSERTION_LEVEL value '{}'\n", value);
        return nullopt;
    }

    /**
     * Apply any environment-variable overrides to a copy of the given ProofOptions.
     * Environment variables act as defaults only: an option set explicitly in code
     * takes precedence.
     */
    [[nodiscard]] auto with_env_overrides(ProofOptions options) -> ProofOptions
    {
        if (! options.assertion_level_set_explicitly)
            if (auto level = assertion_level_from_env())
                options.assertion_level = *level;
        return options;
    }
}

ProofFileNames::ProofFileNames(const std::string & s) :
    opb_file(s + ".opb"), proof_file(s + ".pbp"), variables_map_file(s + ".varmap"), s_expr_file(s + ".scp")
{
}

ProofOptions::ProofOptions(const std::string & f) : proof_file_names(f)
{
}

ProofOptions::ProofOptions(const ProofFileNames & f) : proof_file_names(f)
{
}

struct Proof::Imp
{
    NamesAndIDsTracker tracker;
    ProofLogger logger;
    ProofModel model;

    Imp(const ProofOptions & o) : tracker(o), logger(o, tracker), model(o, tracker)
    {
    }
};

Proof::Proof(const ProofOptions & o) : _imp(make_unique<Imp>(with_env_overrides(o)))
{
    _imp->tracker.start_writing_model(model());
}

Proof::~Proof() = default;

auto Proof::logger() -> innards::ProofLogger *
{
    return &_imp->logger;
}

auto Proof::model() -> innards::ProofModel *
{
    return &_imp->model;
}
