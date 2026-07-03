#include <gcs/constraints/all_different/vc_all_different.hh>
#include <gcs/constraints/circuit/circuit_base.hh>
#include <gcs/constraints/circuit/hints.hh>
#include <gcs/exception.hh>
#include <gcs/innards/inference_tracker.hh>
#include <gcs/innards/proofs/pol_builder.hh>
#include <gcs/innards/propagators.hh>

#include <util/enumerate.hh>
#include <utility>

#include <version>

#if defined(__cpp_lib_print) && defined(__cpp_lib_format)
#include <format>
#else
#include <fmt/core.h>
#endif

using namespace gcs;
using namespace gcs::innards;

using std::cmp_less;
using std::cmp_not_equal;
using std::nullopt;
using std::optional;
using std::vector;

#if defined(__cpp_lib_print) && defined(__cpp_lib_format)
using std::format;
#else
using fmt::format;
#endif

using namespace gcs::innards::circuit;

auto gcs::innards::circuit::output_cycle_to_proof(const vector<IntegerVariableID> & succ, const long & start, const long & length,
    const PosVarDataMap & pos_var_data, const State & state, ProofLogger & logger, const optional<Integer> & prevent_idx,
    const optional<Integer> & prevent_value) -> void
{
    auto current_val = state.optional_single_value(succ[start]);
    if (current_val == nullopt)
        throw UnexpectedException("Circuit propagator tried to output a cycle that doesn't exist");

    if (*current_val < 0_i)
        throw UnimplementedException("Successor encoding for circuit can't have negative values");

    PolBuilder pol;
    pol.add(pos_var_data.at(start).plus_one_lines.at(current_val->as_index()).geq_line);
    long cycle_length = 1;
    while (cmp_not_equal(current_val->raw_value, start)) {
        auto last_val = current_val;
        auto next_var = succ[last_val->as_index()];
        current_val = state.optional_single_value(next_var);

        if (current_val == nullopt || cycle_length == length)
            break;

        pol.add(pos_var_data.at(last_val->as_index()).plus_one_lines.at(current_val->as_index()).geq_line);
        cycle_length++;
    }

    if (prevent_idx.has_value()) {
        logger.emit_proof_comment(format("Preventing sub-cycle for succ[{}] = {}", *prevent_idx, *prevent_value));
        pol.add(pos_var_data.at(prevent_idx->as_index()).plus_one_lines.at(prevent_value->as_index()).geq_line);
    }
    else {
        logger.emit_proof_comment("Contradicting sub-cycle");
    }

    pol.emit(logger, ProofLevel::Current);
}

auto gcs::innards::circuit::prevent_small_cycles(const vector<IntegerVariableID> & succ, const ConstraintID & owner,
    const PosVarDataMap & pos_var_data, const ConstraintStateHandle & unassigned_handle, const State & state, auto & inference,
    ProofLogger * const logger) -> void
{
    auto & unassigned = any_cast<NonGacAllDifferentUnassigned &>(state.get_constraint_state(unassigned_handle));
    auto n = succ.size();
    auto end = vector<long>(n, -1);
    auto known_ends = vector<long>{};
    auto chain_lengths = vector<long>{};

    for (auto var : unassigned) {
        for (const auto & val : state.each_value_immutable(var)) {
            auto j0 = val.raw_value;
            auto length = 0;
            if (state.has_single_value(succ[j0]) && (end[j0] < 0)) {
                auto j = j0;
                do {
                    j = state.optional_single_value(succ[j])->raw_value;
                    length++;
                    // Need to check this in case alldiff hasn't been fully propagated.
                    if (j == j0) {
                        if (logger && logger->get_assertion_level() == AssertionLevel::Off)
                            output_cycle_to_proof(succ, j0, length, pos_var_data, state, *logger);
                        inference.contradiction(logger, JustifyUsingRUP{hints::Circuit{owner}}, generic_reason(succ));
                    }
                } while (state.has_single_value(succ[j]));
                end[j0] = j;
                known_ends.emplace_back(j0);
                chain_lengths.emplace_back(length);
            }
        }
    }

    while (! known_ends.empty()) {
        auto i = known_ends.back();
        known_ends.pop_back();
        auto length = chain_lengths.back();
        chain_lengths.pop_back();
        if (cmp_less(length, succ.size() - 1)) {
            auto justf = [&](const ReasonLiterals &) {
                output_cycle_to_proof(succ, i, length, pos_var_data, state, *logger, Integer{end[i]}, Integer{i});
            };
            inference.infer(logger, succ[end[i]] != Integer{i}, JustifyExplicitly{justf, ThenRUP::Yes, hints::Circuit{owner}}, generic_reason(succ));
        }
        else {
            inference.infer(logger, succ[end[i]] == Integer{i}, JustifyUsingRUP{hints::Circuit{owner}}, generic_reason(succ));
        }
    }
}

template auto gcs::innards::circuit::prevent_small_cycles(const std::vector<IntegerVariableID> & succ, const ConstraintID & owner,
    const PosVarDataMap & pos_var_data, const ConstraintStateHandle & unassigned_handle, const State & state,
    SimpleInferenceTracker & inference_tracker, ProofLogger * const logger) -> void;

template auto gcs::innards::circuit::prevent_small_cycles(const std::vector<IntegerVariableID> & succ, const ConstraintID & owner,
    const PosVarDataMap & pos_var_data, const ConstraintStateHandle & unassigned_handle, const State & state,
    EagerProofLoggingInferenceTracker & inference_tracker, ProofLogger * const logger) -> void;
