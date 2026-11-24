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
#include <unordered_map>
#include <utility>
#include <variant>

using namespace gcs;
using namespace gcs::innards;

using std::decay_t;
using std::function;
using std::is_same_v;
using std::pair;
using std::size_t;
using std::string;
using std::unique_ptr;
using std::unordered_map;
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

auto gcs::innards::NonGacAllDifferentSingleValueReasons::build(const vector<IntegerVariableID> & vars) -> NonGacAllDifferentSingleValueReasons
{
    vector<pair<unsigned long long, IntegerVariableID>> simple;
    for (const auto & v : vars)
        if (auto s = std::get_if<SimpleIntegerVariableID>(&v))
            simple.emplace_back(s->index, v);
    sort(simple, {}, &pair<unsigned long long, IntegerVariableID>::first);

    NonGacAllDifferentSingleValueReasons result;
    result.indices.reserve(simple.size());
    result.reasons.reserve(simple.size());
    for (const auto & [index, v] : simple) {
        result.indices.push_back(index);
        result.reasons.emplace_back(ExactSingleValue{ReasonVars{vector<IntegerVariableID>{v}}});
    }
    return result;
}

auto gcs::innards::NonGacAllDifferentSingleValueReasons::find(const IntegerVariableID & v) const -> const Reason *
{
    auto s = std::get_if<SimpleIntegerVariableID>(&v);
    if (! s)
        return nullptr;
    auto it = std::ranges::lower_bound(indices, s->index);
    if (it == indices.end() || *it != s->index)
        return nullptr;
    return &reasons[it - indices.begin()];
}

// Returns false if an inference contradicted (the caller must stop and not read
// state again until backtrack); true if propagation completed. Uses the
// non-throwing infer_not_equal_or_stop path so a contradiction does not unwind via
// an exception -- this propagator fails roughly once per node in circuit-style
// models, so the throw was a large per-node cost.
auto gcs::innards::propagate_non_gac_alldifferent(const ConstraintStateHandle & unassigned_handle, const State & state, auto & inference,
    ProofLogger * const logger, const ConstraintID & owner, const NonGacAllDifferentSingleValueReasons * single_value_reasons) -> bool
{
    auto & unassigned = any_cast<NonGacAllDifferentUnassigned &>(state.get_constraint_state(unassigned_handle));

    // The reason every removal cites is "v == val", where v is a variable already
    // fixed to val. When the caller hands us prebuilt reasons, look v's up and return
    // a reference -- no per-inference construction. A view/constant, or a variable
    // with no prebuilt reason, falls back to building the reason inline (the
    // want_reasons() guard still applies there, since that construction is not free).
    auto reason_for = [&](const IntegerVariableID & v, Integer val, Reason & inline_storage) -> const Reason & {
        if (single_value_reasons)
            if (auto prebuilt = single_value_reasons->find(v))
                return *prebuilt;
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

    // Each popped variable has to be checked against the fixed values still
    // waiting in to_propagate. Scanning them is quadratic when many variables
    // become fixed in one call, as a whole ring does under Circuit (#1453), so
    // past a short stack an index from each waiting value to its positions takes
    // over. The scan's first match is the earliest waiting entry with the same
    // value, which is the front of that value's position list: entries are only
    // ever pushed and popped at the back, so each list is in increasing order and
    // the popped entry is always the last of its own. The clash found, and so the
    // reason given, is the same either way.
    constexpr size_t index_from = 16;
    std::optional<unordered_map<long long, vector<size_t>>> positions_of;
    auto push = [&](const IntegerVariableID & v, Integer value) {
        to_propagate.emplace_back(v, value);
        if (positions_of)
            (*positions_of)[value.raw_value].push_back(to_propagate.size() - 1);
    };

    while (! to_propagate.empty()) {
        if (! positions_of && to_propagate.size() > index_from) {
            positions_of.emplace();
            for (const auto & [p, entry] : enumerate(to_propagate))
                (*positions_of)[entry.second.raw_value].push_back(p);
        }

        auto [var, val] = to_propagate.back();
        to_propagate.pop_back();

        // The same "var == val" reason justifies every removal this popped variable
        // triggers, so resolve it once here and reuse the reference in the inner loop.
        Reason var_inline_storage;
        const Reason & var_assigned_reason = reason_for(var, val, var_inline_storage);

        // The earliest waiting variable already fixed to val, if any: we're then
        // already in a contradicting state.
        std::optional<size_t> clash;
        if (positions_of) {
            auto & positions = positions_of->at(val.raw_value);
            positions.pop_back();
            if (! positions.empty())
                clash = positions.front();
        }
        else
            for (const auto & [p, other] : enumerate(to_propagate))
                if (other.second == val) {
                    clash = p;
                    break;
                }
        if (clash) {
            Reason other_inline_storage;
            if (! inference.infer_not_equal_or_stop(
                    logger, var, val, JustifyUsingRUP{hints::AllDifferent{owner}}, reason_for(to_propagate[*clash].first, val, other_inline_storage)))
                return false;
        }

        for (std::size_t k = 0; k < unassigned.size();) {
            auto other = unassigned[k];
            // var is no longer in unassigned (it was popped into to_propagate), so the
            // other != var guard from the list version always held; kept for safety.
            if (other != var) {
                if (! inference.infer_not_equal_or_stop(logger, other, val, JustifyUsingRUP{hints::AllDifferent{owner}}, var_assigned_reason))
                    return false;
                if (auto other_val = state.optional_single_value(other)) {
                    push(other, *other_val);
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
    const NonGacAllDifferentSingleValueReasons * single_value_reasons) -> bool;

template auto gcs::innards::propagate_non_gac_alldifferent(const ConstraintStateHandle & unassigned_handle, const State & state,
    EagerProofLoggingInferenceTracker & inference_tracker, ProofLogger * const logger, const ConstraintID & owner,
    const NonGacAllDifferentSingleValueReasons * single_value_reasons) -> bool;
