#include <gcs/innards/proofs/names_and_ids_tracker.hh>
#include <gcs/innards/proofs/proof_logger.hh>
#include <gcs/innards/proofs/proof_model.hh>
#include <gcs/proof.hh>

#include <cstdlib>
#include <exception>
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
     * Recognise an explicit "off" word used by both order-encoding-deletion
     * environment variables.
     */
    [[nodiscard]] auto is_off_word(const string & value) -> bool
    {
        return value == "0" || value == "off" || value == "Off" || value == "none" || value == "None";
    }

    /**
     * Read an OrderEncodingDeletion from the environment, if set:
     * GCS_DELETE_ORDER_ENCODING=literals|none (case-insensitive on the first letter),
     * picking the mode by name. An unrecognised value falls through to the default.
     */
    [[nodiscard]] auto order_encoding_deletion_from_env() -> optional<OrderEncodingDeletion>
    {
        if (const auto * const env = std::getenv("GCS_DELETE_ORDER_ENCODING"); env && *env) {
            string value{env};
            if (value == "literals" || value == "Literals")
                return OrderEncodingDeletion::Literals;
            if (is_off_word(value))
                return OrderEncodingDeletion::None;
        }

        return nullopt;
    }

    /**
     * Read the OrderEncodingDeletion::Literals chain-length gate from the
     * GCS_DELETE_ORDER_ENCODING_MIN_CHAIN environment variable, if set. Accepts a
     * non-negative integer; an unparseable or negative value is ignored (fall through
     * to the code/default) with a warning.
     */
    [[nodiscard]] auto order_encoding_deletion_min_chain_from_env() -> optional<int>
    {
        const auto * const env = std::getenv("GCS_DELETE_ORDER_ENCODING_MIN_CHAIN");
        if (! env || ! *env)
            return nullopt;

        string value{env};
        try {
            std::size_t consumed = 0;
            int parsed = std::stoi(value, &consumed);
            if (consumed == value.size() && parsed >= 0)
                return parsed;
        }
        catch (const std::exception &) {
            // Fall through to the warning below.
        }

        print(stderr, "Ignoring unrecognised GCS_DELETE_ORDER_ENCODING_MIN_CHAIN value '{}'\n", value);
        return nullopt;
    }

    /**
     * Read the eq-atom window switch from the GCS_DELETE_ORDER_ENCODING_EQ_WINDOW
     * environment variable, if set. Any non-empty value turns it on except the off-words
     * (0 / off / none), which turn it off explicitly.
     */
    [[nodiscard]] auto order_encoding_deletion_eq_window_from_env() -> optional<bool>
    {
        const auto * const env = std::getenv("GCS_DELETE_ORDER_ENCODING_EQ_WINDOW");
        if (! env || ! *env)
            return nullopt;
        return ! is_off_word(string{env});
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
        if (! options.order_encoding_deletion_set_explicitly)
            if (auto mode = order_encoding_deletion_from_env())
                options.order_encoding_deletion = *mode;
        if (! options.order_encoding_deletion_min_chain_set_explicitly)
            if (auto min_chain = order_encoding_deletion_min_chain_from_env())
                options.order_encoding_deletion_min_chain = *min_chain;
        if (! options.order_encoding_deletion_eq_window_set_explicitly)
            if (auto eq_window = order_encoding_deletion_eq_window_from_env())
                options.order_encoding_deletion_eq_window = *eq_window;
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
