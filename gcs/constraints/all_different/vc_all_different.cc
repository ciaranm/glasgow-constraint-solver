#include <gcs/constraints/all_different/encoding.hh>
#include <gcs/constraints/all_different/hints.hh>
#include <gcs/constraints/all_different/vc_all_different.hh>
#include <gcs/innards/inference_tracker.hh>
#include <gcs/innards/proofs/names_and_ids_tracker.hh>
#include <gcs/innards/proofs/proof_logger.hh>
#include <gcs/innards/proofs/proof_model.hh>
#include <gcs/innards/propagators.hh>
#include <gcs/innards/s_expr.hh>
#include <util/enumerate.hh>

#include <version>

#if defined(__cpp_lib_print) && defined(__cpp_lib_format)
#include <format>
#include <print>
#else
#include <fmt/ostream.h>
#endif

#include <algorithm>
#include <functional>
#include <optional>
#include <type_traits>
#include <utility>
#include <variant>

using namespace gcs;
using namespace gcs::innards;

using std::decay_t;
using std::function;
using std::is_same_v;
using std::pair;
using std::string;
using std::unique_ptr;
using std::variant;
using std::vector;
using std::ranges::adjacent_find;
using std::ranges::sort;

#if defined(__cpp_lib_print) && defined(__cpp_lib_format)
using std::format;
using std::print;
#else
using fmt::format;
using fmt::print;
#endif

// Returns false if an inference contradicted (the caller must stop and not read
// state again until backtrack); true if propagation completed. Uses the
// non-throwing infer_not_equal_or_stop path so a contradiction does not unwind via
// an exception -- this propagator fails roughly once per node in circuit-style
// models, so the throw was a large per-node cost.
auto gcs::innards::propagate_non_gac_alldifferent(const ConstraintStateHandle & unassigned_handle, const State & state, auto & inference,
    ProofLogger * const logger, const ConstraintID & owner, const std::vector<Reason> * single_value_reasons, unsigned long long reason_base) -> bool
{
    auto & unassigned = any_cast<NonGacAllDifferentUnassigned &>(state.get_constraint_state(unassigned_handle));

    // The reason every removal cites is "v == val", where v is a variable already
    // fixed to val. When the caller hands us a prebuilt table, look it up by v's own
    // index and return a reference -- no per-inference construction. A view/constant,
    // or a variable outside the table, falls back to building the reason inline (the
    // want_reasons() guard still applies there, since that construction is not free).
    auto reason_for = [&](const IntegerVariableID & v, Integer val, Reason & inline_storage) -> const Reason & {
        if (single_value_reasons)
            if (auto s = std::get_if<SimpleIntegerVariableID>(&v))
                if (auto idx = s->index - reason_base; idx < single_value_reasons->size())
                    return (*single_value_reasons)[idx];
        inline_storage = inference.want_reasons() ? Reason{ExplicitReason{ReasonLiterals{{v == val}}}} : Reason{};
        return inline_storage;
    };

    vector<pair<IntegerVariableID, Integer>> to_propagate;
    {
        // Collect any newly assigned values. Erasing by swap-and-pop (order of
        // unassigned is irrelevant) keeps this O(1) per removal on a flat container.
        for (std::size_t k = 0; k < unassigned.size();) {
            auto s = unassigned[k];
            if (auto val = state.optional_single_value(s)) {
                to_propagate.emplace_back(s, *val);
                unassigned[k] = unassigned.back();
                unassigned.pop_back();
            }
            else
                ++k;
        }
    }

    while (! to_propagate.empty()) {
        auto [var, val] = to_propagate.back();
        to_propagate.pop_back();

        // The same "var == val" reason justifies every removal this popped variable
        // triggers, so resolve it once here and reuse the reference in the inner loop.
        Reason var_inline_storage;
        const Reason & var_assigned_reason = reason_for(var, val, var_inline_storage);

        for (auto other : to_propagate) {
            if (other.second == val) {
                // we're already in a contradicting state
                Reason other_inline_storage;
                if (! inference.infer_not_equal_or_stop(
                        logger, var, val, JustifyUsingRUP{hints::AllDifferent{owner}}, reason_for(other.first, val, other_inline_storage)))
                    return false;
            }
        }

        for (std::size_t k = 0; k < unassigned.size();) {
            auto other = unassigned[k];
            // var is no longer in unassigned (it was popped into to_propagate), so the
            // other != var guard from the list version always held; kept for safety.
            if (other != var) {
                if (! inference.infer_not_equal_or_stop(logger, other, val, JustifyUsingRUP{hints::AllDifferent{owner}}, var_assigned_reason))
                    return false;
                if (auto other_val = state.optional_single_value(other)) {
                    to_propagate.emplace_back(other, *other_val);
                    unassigned[k] = unassigned.back();
                    unassigned.pop_back();
                    continue;
                }
            }
            ++k;
        }
    }

    return true;
}

template auto gcs::innards::propagate_non_gac_alldifferent(const ConstraintStateHandle & unassigned_handle, const State & state,
    SimpleInferenceTracker & inference_tracker, ProofLogger * const logger, const ConstraintID & owner,
    const std::vector<Reason> * single_value_reasons, unsigned long long reason_base) -> bool;

template auto gcs::innards::propagate_non_gac_alldifferent(const ConstraintStateHandle & unassigned_handle, const State & state,
    EagerProofLoggingInferenceTracker & inference_tracker, ProofLogger * const logger, const ConstraintID & owner,
    const std::vector<Reason> * single_value_reasons, unsigned long long reason_base) -> bool;
