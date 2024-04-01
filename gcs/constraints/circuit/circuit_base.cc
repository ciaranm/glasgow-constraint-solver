#include <gcs/constraints/all_different.hh>
#include <gcs/constraints/all_different/vc_all_different.hh>
#include <gcs/constraints/circuit/circuit_base.hh>
#include <gcs/innards/proofs/proof_model.hh>
#include <gcs/innards/propagators.hh>

#include <list>
#include <map>
#include <sstream>
#include <string>
#include <util/enumerate.hh>
#include <utility>

using namespace gcs;
using namespace gcs::innards;

using std::cmp_equal;
using std::cmp_less;
using std::cmp_not_equal;
using std::list;
using std::make_optional;
using std::make_pair;
using std::map;
using std::move;
using std::nullopt;
using std::optional;
using std::pair;
using std::size_t;
using std::string;
using std::stringstream;
using std::to_string;
using std::tuple;
using std::unique_ptr;
using std::vector;

using namespace gcs::innards::circuit;

CircuitBase::CircuitBase(vector<IntegerVariableID> v, const bool g) :
    _gac_all_different(g),
    _succ(std::move(v))
{
}

auto gcs::innards::circuit::output_cycle_to_proof(const vector<IntegerVariableID> & succ,
    const long & start,
    const long & length,
    const PosVarDataMap & pos_var_data,
    State & state,
    ProofLogger & logger,
    const optional<Integer> & prevent_idx,
    const optional<Integer> & prevent_value) -> void
{
    auto current_val = state.optional_single_value(succ[start]);
    if (current_val == nullopt)
        throw UnexpectedException("Circuit propagator tried to output a cycle that doesn't exist");

    if (current_val->raw_value < 0)
        throw UnimplementedException("Successor encoding for circuit can't have negative values");

    stringstream proof_step;

    proof_step << "p ";
    proof_step << pos_var_data.at(start).plus_one_lines.at(current_val->raw_value).geq_line << " ";
    long cycle_length = 1;
    while (cmp_not_equal(current_val->raw_value, start)) {
        auto last_val = current_val;
        auto next_var = succ[last_val->raw_value];
        current_val = state.optional_single_value(next_var);

        if (current_val == nullopt || cycle_length == length) break;

        proof_step << pos_var_data.at(last_val->raw_value).plus_one_lines.at(current_val->raw_value).geq_line
                   << " + ";
        cycle_length++;
    }

    if (prevent_idx.has_value()) {
        logger.emit_proof_comment("Preventing sub-cycle for succ[" + to_string(prevent_idx->raw_value) + "] = " + to_string(prevent_value->raw_value));
        proof_step << pos_var_data.at(prevent_idx->raw_value).plus_one_lines.at(prevent_value->raw_value).geq_line
                   << " + ";
    }
    else {
        logger.emit_proof_comment("Contradicting sub-cycle");
    }

    logger.emit_proof_line(proof_step.str(), ProofLevel::Current);
}

auto gcs::innards::circuit::prevent_small_cycles(
    const vector<IntegerVariableID> & succ,
    const PosVarDataMap & pos_var_data,
    const ConstraintStateHandle & unassigned_handle,
    State & state,
    ProofLogger * const logger) -> Inference
{
    auto result = Inference::NoChange;
    auto & unassigned = any_cast<list<IntegerVariableID> &>(state.get_constraint_state(unassigned_handle));
    auto n = succ.size();
    auto end = vector<long>(n, -1);
    auto known_ends = vector<long>{};
    auto chain_lengths = vector<long>{};

    for (auto var : unassigned) {
        state.for_each_value_while(var, [&](Integer val) -> bool {
            auto j0 = val.raw_value;
            auto length = 0;
            if (state.has_single_value(succ[j0]) && (end[j0] < 0)) {
                auto j = j0;
                do {
                    j = state.optional_single_value(succ[j])->raw_value;
                    length++;
                    // Need to check this in case alldiff hasn't been fully propagated.
                    if (j == j0) {
                        if (logger)
                            output_cycle_to_proof(succ, j0, length, pos_var_data, state, *logger);
                        increase_inference_to(result, Inference::Contradiction);
                        return false;
                    }
                } while (state.has_single_value(succ[j]));
                end[j0] = j;
                known_ends.emplace_back(j0);
                chain_lengths.emplace_back(length);
            }

            return true;
        });

        if (result == Inference::Contradiction)
            return result;
    }

    while (! known_ends.empty()) {
        auto i = known_ends.back();
        known_ends.pop_back();
        auto length = chain_lengths.back();
        chain_lengths.pop_back();
        if (cmp_less(length, succ.size() - 1)) {
            auto justf = [&](const Reason &) {
                output_cycle_to_proof(succ, i, length, pos_var_data, state, *logger, Integer{end[i]}, Integer{i});
            };
            increase_inference_to(result,
                state.infer(logger, succ[end[i]] != Integer{i}, JustifyExplicitly{justf}, generic_reason(state, succ)));
            if (result == Inference::Contradiction)
                return result;
        }
        else {
            increase_inference_to(result, state.infer(logger, succ[end[i]] == Integer{i}, JustifyUsingRUP{}, generic_reason(state, succ)));
            if (result == Inference::Contradiction)
                return result;
        }
    }
    return result;
}

auto CircuitBase::set_up(Propagators & propagators, State & initial_state, ProofModel * const model) -> PosVarDataMap
{
    // Can't have negative values
    for (const auto & s : _succ)
        propagators.trim_lower_bound(initial_state, model, s, 0_i, "Circuit");

    // Can't have too-large values
    for (const auto & s : _succ)
        propagators.trim_upper_bound(initial_state, model, s, Integer(static_cast<long long>(_succ.size() - 1)), "Circuit");

    // Define all different, either gac or non-gac
    if (_gac_all_different) {
        GACAllDifferent all_diff{_succ};
        std::move(all_diff).install(propagators, initial_state, model);
    }
    else {
        // Still need to define the all different encoding.
        if (model)
            define_clique_not_equals_encoding(*model, _succ);
    }

    // Define encoding to eliminate sub-cycles
    PosVarDataMap pos_var_data{};

    if (model) {
        auto n = static_cast<long long>(_succ.size());
        // Define encoding to eliminate sub-cycles
        // Need extra proof variable: pos[i] = j means "the ith node visited in the circuit is the jth var"
        // WLOG start at node 0, so pos[0] = 0
        pos_var_data.emplace(0,
            PosVarData{"p[0]", model->create_proof_only_integer_variable(0_i, Integer{n - 1}, "pos" + to_string(0), IntegerVariableProofRepresentation::Bits), map<long, PosVarLineData>{}});
        model->add_constraint(WeightedPseudoBooleanSum{} + 1_i * pos_var_data.at(0).var <= 0_i);
        // Hence we can only have succ[0] = 0 (self cycle) if there is only one node i.e. n - 1 = 0
        auto [leq_line, geq_line] = model->add_constraint(
            WeightedPseudoBooleanSum{} == Integer{n - 1},
            HalfReifyOnConjunctionOf{{_succ[0] == 0_i}});

        pos_var_data.at(0).plus_one_lines.emplace(0, PosVarLineData{leq_line.value(), geq_line.value()});

        for (unsigned int idx = 1; idx < _succ.size(); ++idx) {
            pos_var_data.emplace(idx,
                PosVarData{"p[" + to_string(idx) + "]",
                    model->create_proof_only_integer_variable(0_i, Integer{n - 1}, "pos" + to_string(0),
                        IntegerVariableProofRepresentation::Bits),
                    map<long, PosVarLineData>{}});
        }

        for (unsigned int idx = 1; idx < _succ.size(); ++idx) {
            // (succ[0] = i) -> pos[i] - pos[0] = 1
            tie(leq_line, geq_line) = model->add_constraint(
                WeightedPseudoBooleanSum{} + 1_i * pos_var_data.at(idx).var + -1_i * 1_c == 0_i,
                HalfReifyOnConjunctionOf{{_succ[0] == Integer{idx}}});
            pos_var_data.at(0).plus_one_lines.emplace(idx, PosVarLineData{leq_line.value(), geq_line.value()});

            // (succ[i] = 0) -> pos[0] - pos[i] = 1-n
            tie(leq_line, geq_line) = model->add_constraint(
                WeightedPseudoBooleanSum{} + 1_i * pos_var_data.at(0).var + -1_i * pos_var_data.at(idx).var == Integer{1 - n},
                HalfReifyOnConjunctionOf{{_succ[idx] == 0_i}});
            pos_var_data.at(idx).plus_one_lines.emplace(0, PosVarLineData{leq_line.value(), geq_line.value()});

            // (succ[i] = j) -> pos[j] = pos[i] + 1
            for (unsigned int jdx = 1; jdx < _succ.size(); ++jdx) {
                tie(leq_line, geq_line) = model->add_constraint(
                    WeightedPseudoBooleanSum{} + 1_i * pos_var_data.at(jdx).var + -1_i * pos_var_data.at(idx).var == 1_i,
                    HalfReifyOnConjunctionOf{{_succ[idx] == Integer{jdx}}});
                pos_var_data.at(idx).plus_one_lines.emplace(jdx, PosVarLineData{leq_line.value(), geq_line.value()});
            }
        }
    }

    // Infer succ[i] != i at top of search, but no other propagation defined here: use CircuitPrevent or CircuitSCC
    if (_succ.size() > 1) {
        propagators.install([succ = _succ](State & state, ProofLogger * const logger) -> pair<Inference, PropagatorState> {
            auto result = Inference::NoChange;
            for (auto [idx, s] : enumerate(succ)) {
                increase_inference_to(result, state.infer_not_equal(logger, s, Integer(static_cast<long long>(idx)), JustifyUsingRUP{}, generic_reason(state, succ)));
                if (result == Inference::Contradiction)
                    break;
            }
            return pair{result, PropagatorState::DisableUntilBacktrack};
        },
            Triggers{}, "circuit init");
    }

    return pos_var_data;
}

auto CircuitBase::describe_for_proof() -> std::string
{
    return "circuit (all different + no sub-cycles)";
}
