#include <gcs/constraints/all_different.hh>
#include <gcs/constraints/circuit/circuit.hh>
#include <gcs/exception.hh>
#include <gcs/innards/propagators.hh>

#include <util/enumerate.hh>

#include <list>
#include <map>
#include <utility>

using namespace gcs;
using namespace gcs::innards;

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
using std::stringstream;
using std::to_string;
using std::tuple;
using std::unique_ptr;
using std::vector;

CircuitBase::CircuitBase(vector<IntegerVariableID> v, const bool g) :
    _succ(move(v)),
    _gac_all_different(g)
{
}

auto CircuitBase::set_up(Propagators & propagators, State & initial_state) -> tuple<vector<PseudoBooleanTerm>, ProofLine2DMap, ConstraintStateHandle>
{
    // Can't have negative values
    for (const auto & s : _succ)
        propagators.trim_lower_bound(initial_state, s, 0_i, "Circuit");

    // Can't have too-large values
    for (const auto & s : _succ)
        propagators.trim_upper_bound(initial_state, s, Integer(_succ.size() - 1), "Circuit");

    // Define all different, either gac or non-gac
    if (_gac_all_different) {
        AllDifferent all_diff{_succ};
        move(all_diff).install(propagators, initial_state);
    }
    else if (propagators.want_definitions()) {
        // Still need to define all-different
        for (unsigned i = 0; i < _succ.size(); ++i)
            for (unsigned j = i + 1; j < _succ.size(); ++j) {
                auto selector = propagators.create_proof_flag("circuit_notequals");
                propagators.define(initial_state, WeightedPseudoBooleanSum{} + 1_i * _succ[i] + -1_i * _succ[j] <= -1_i, selector);
                propagators.define(initial_state, WeightedPseudoBooleanSum{} + -1_i * _succ[i] + 1_i * _succ[j] <= -1_i, ! selector);
            }
    }

    // Keep track of unassigned vars
    list<IntegerVariableID> unassigned{};
    for (auto v : _succ) {
        unassigned.emplace_back(v);
    }
    auto unassigned_handle = initial_state.add_constraint_state(unassigned);

    ProofLine2DMap lines_for_setting_pos{};
    // Define encoding to eliminate sub-cycles
    vector<PseudoBooleanTerm> position;
    if (propagators.want_definitions()) {

        auto n_minus_1 = ConstantIntegerVariableID{Integer{static_cast<long long>(_succ.size() - 1)}};

        // Need extra proof variable: pos[i] = j means "the ith node visited in the circuit is the jth var"
        // WLOG start at node 0, so pos[0] = 0
        position.emplace_back(0_c);
        // Hence we can only have succ[0] = 0 (self cycle) if there is only one node i.e. n - 1 = 0
        auto cv = WeightedPseudoBooleanSum{} + 1_i * position[0] + -1_i * n_minus_1;
        auto proof_line = propagators.define(initial_state, move(cv) == 0_i, _succ[0] == 0_i);
        lines_for_setting_pos.insert({{Integer{0_i}, Integer{0_i}}, proof_line.first.value()});

        for (unsigned int idx = 1; idx < _succ.size(); ++idx) {
            position.emplace_back(propagators.create_proof_only_integer_variable(0_i, Integer(_succ.size() - 1),
                "pos" + to_string(idx), IntegerVariableProofRepresentation::Bits));
        }

        for (unsigned int idx = 1; idx < _succ.size(); ++idx) {
            // (succ[0] = i) -> pos[i] = 1
            auto cv1 = WeightedPseudoBooleanSum{} + 1_i * position[idx] + -1_i * 1_c;
            proof_line = propagators.define(initial_state, move(cv1) == 0_i, _succ[0] == Integer{idx});
            lines_for_setting_pos.insert({{Integer{idx}, Integer{0_i}}, proof_line.first.value()});

            // (succ[i] = 0) -> pos[i] = n-1
            auto cv2 = WeightedPseudoBooleanSum{} + 1_i * position[idx] + -1_i * n_minus_1;

            proof_line = propagators.define(initial_state, move(cv2) == 0_i, _succ[idx] == 0_i);
            lines_for_setting_pos.insert({{Integer{0_i}, Integer{idx}}, proof_line.first.value()});

            // (succ[i] = j) -> pos[j] = pos[i] + 1
            for (unsigned int jdx = 1; jdx < _succ.size(); ++jdx) {
                // if (idx == jdx) continue;
                auto cv3 = WeightedPseudoBooleanSum{} + 1_i * position[jdx] + -1_i * position[idx] + -1_i * 1_c;

                proof_line = propagators.define(initial_state, move(cv3) == 0_i, _succ[idx] == Integer{jdx});
                lines_for_setting_pos.insert({{Integer{jdx}, Integer{idx}}, proof_line.first.value()});
            }
        }
    }

    // Infer succ[i] != i at top of search, but no other propagation defined here: use CircuitPrevent or CircuitSCC
    if (_succ.size() > 1) {
        propagators.install([succ = _succ](State & state) -> pair<Inference, PropagatorState> {
            auto result = Inference::NoChange;
            for (auto [idx, s] : enumerate(succ)) {
                increase_inference_to(result, state.infer_not_equal(s, Integer(idx), JustifyUsingRUP{}));
                if (result == Inference::Contradiction)
                    break;
            }
            return pair{result, PropagatorState::DisableUntilBacktrack};
        },
            Triggers{}, "circuit init");
    }

    return tuple{position, lines_for_setting_pos, unassigned_handle};
}

auto CircuitBase::describe_for_proof() -> std::string
{
    return "circuit (all different + no sub-cycles)";
}

auto gcs::prevent_small_cycles(
    const vector<IntegerVariableID> & succ,
    const ProofLine2DMap & lines_for_setting_pos,
    const ConstraintStateHandle & unassigned_handle,
    State & state) -> Inference
{
    auto result = Inference::NoChange;
    auto & unassigned = any_cast<list<IntegerVariableID> &>(state.get_constraint_state(unassigned_handle));
    auto k = unassigned.size();
    auto n = succ.size();
    auto end = vector<long>(n, -1);
    auto known_ends = vector<long>{};

    for (auto var : unassigned) {
        state.for_each_value(var, [&](Integer val) {
            auto j0 = val.raw_value;
            if (state.has_single_value(succ[j0]) && (end[j0] < 0)) {
                auto j = j0;
                do {
                    j = state.optional_single_value(succ[j])->raw_value;
                } while (state.has_single_value(succ[j]));
                end[j0] = j;
                known_ends.emplace_back(j0);
            }
        });
    }

    while (! known_ends.empty()) {
        auto i = known_ends.back();
        known_ends.pop_back();
        increase_inference_to(result, state.infer(succ[end[i]] != Integer{i}, NoJustificationNeeded{}));
    }
    return result;
}

auto gcs::propagate_non_gac_alldifferent(const ConstraintStateHandle & unassigned_handle, State & state) -> innards::Inference
{
    auto & unassigned = any_cast<list<IntegerVariableID> &>(state.get_constraint_state(unassigned_handle));

    auto result = Inference::NoChange;
    vector<pair<IntegerVariableID, Integer>> to_propagate;
    {
        // Collect any newly assigned values
        auto i = unassigned.begin();
        while (i != unassigned.end()) {
            auto s = *i;
            if (auto val = state.optional_single_value(s)) {
                to_propagate.emplace_back(s, *val);
                unassigned.erase(i++);
            }
            else
                ++i;
        }
    }

    while (! to_propagate.empty()) {
        auto [var, val] = to_propagate.back();
        to_propagate.pop_back();
        auto i = unassigned.begin();

        for (auto other : to_propagate) {
            if (other.second == val) return Inference::Contradiction;
        }

        while (i != unassigned.end()) {
            auto other = *i;
            if (other != var) {
                increase_inference_to(result, state.infer_not_equal(other, val, JustifyUsingRUP{}));
                if (result == Inference::Contradiction) return Inference::Contradiction;
                if (auto other_val = state.optional_single_value(other)) {
                    to_propagate.emplace_back(other, *other_val);
                    unassigned.erase(i++);
                }
                else
                    ++i;
            }
        }
    }
    return result;
}
