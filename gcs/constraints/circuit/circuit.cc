#include <gcs/constraints/all_different.hh>
#include <gcs/constraints/circuit/circuit.hh>
#include <gcs/innards/propagators.hh>

#include <iostream>
#include <list>
#include <map>
#include <string>
#include <util/enumerate.hh>
#include <utility>

using namespace gcs;
using namespace gcs::innards;

using std::cmp_less;
using std::cmp_not_equal;
using std::cout;
using std::endl;
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

CircuitBase::CircuitBase(vector<IntegerVariableID> v, const bool g) :
    _succ(move(v)),
    _gac_all_different(g)
{
}

auto CircuitBase::set_up(Propagators & propagators, State & initial_state) -> tuple<vector<ProofOnlySimpleIntegerVariableID>, ConstraintStateHandle, ConstraintStateHandle>

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
                propagators.define(initial_state, WeightedPseudoBooleanSum{} + 1_i * _succ[i] + -1_i * _succ[j] <= -1_i, HalfReifyOnConjunctionOf{selector});
                propagators.define(initial_state, WeightedPseudoBooleanSum{} + -1_i * _succ[i] + 1_i * _succ[j] <= -1_i, HalfReifyOnConjunctionOf{! selector});
            }
    }

    // Keep track of unassigned vars
    list<IntegerVariableID> unassigned{};
    for (auto v : _succ) {
        unassigned.emplace_back(v);
    }
    auto unassigned_handle = initial_state.add_constraint_state(unassigned);
    long dummy = -1; // Not sure why this is necessary but I get a bad_any_cast otherwise

    // Another workaround: persistent constraint state as I don't want this to restore on backtrack
    auto prev_wlog_line_handle = initial_state.add_persistent_constraint_state(dummy);

    // Define encoding to eliminate sub-cycles
    vector<ProofOnlySimpleIntegerVariableID> position;
    if (propagators.want_definitions()) {
        auto n = _succ.size();
        for (unsigned int idx = 0; idx < n; ++idx) {
            position.emplace_back(propagators.create_proof_only_integer_variable(0_i, Integer(n - 1),
                "pos" + to_string(idx), IntegerVariableProofRepresentation::DirectOnly));
        }

        for (unsigned int idx = 0; idx < n; ++idx) {
            // (succ[i] = j) -> pos[j] = pos[i] + 1
            for (unsigned int jdx = 0; jdx < n; ++jdx) {
                // if (idx == jdx) continue;
                // --- Old encoding using bit variables ---
                //                auto cv3 = WeightedPseudoBooleanSum{} + 1_i * position[jdx] + -1_i * position[idx] + -1_i * 1_c;
                //                propagators.define(initial_state, move(cv3) == 0_i, HalfReifyOnConjunctionOf{_succ[idx] == Integer{jdx}, position[jdx] != 0_i},
                //                    "succ[" + to_string(idx) + "] = " + to_string(jdx) + " /\\ pos[" + to_string(jdx) +
                //                        "] != 0 => pos[" + to_string(jdx) + "] = " + "pos[" + to_string(idx) + "] + 1");
                //                auto cv4 = WeightedPseudoBooleanSum{} + 1_i * position[idx];
                //                propagators.define(initial_state, move(cv4) == Integer{static_cast<long long>(n - 1)}, HalfReifyOnConjunctionOf{_succ[idx] == Integer{jdx}, position[jdx] == 0_i},
                //                    "succ[" + to_string(idx) + "] = " + to_string(jdx) + " /\\ pos[" + to_string(jdx) +
                //                        "] == 0 => pos[" + to_string(idx) + "] = n-1");

                // New encoding using direct variables
                for (unsigned int k = 0; k < n; ++k) {
                    auto x_i_neq_j = 1_i * (_succ[idx] != Integer{jdx});
                    auto p_i_neq_k = 1_i * (position[idx] != Integer{k});
                    if (k == n - 1) {
                        propagators.define(initial_state,
                            WeightedPseudoBooleanSum{} + x_i_neq_j + p_i_neq_k + 1_i * (position[jdx] == 0_i) >= 1_i);
                    }
                    else {
                        propagators.define(initial_state,
                            WeightedPseudoBooleanSum{} + x_i_neq_j + p_i_neq_k + 1_i * (position[jdx] == Integer{k + 1}) >= 1_i);
                    }
                }
            }
        }
    }

    // Infer succ[i] != i at top of search, but no other propagation defined here: use CircuitPrevent or CircuitSCC
    if (_succ.size() > 1) {
        propagators.install([succ = _succ, pos = position](State & state) -> pair<Inference, PropagatorState> {
            // For experimentation only
            //            state.infer_true(JustifyExplicitly{[&](Proof & proof, vector<ProofLine> &) {
            //                for (int i = 0; i < succ.size(); i++) {
            //                    WeightedPseudoBooleanSum wsum = WeightedPseudoBooleanSum{} + 1_i * (succ[0] != Integer{i}) + 1_i * (pos[i] == 1_i);
            //                    proof.emit_rup_proof_line_under_trail(state, wsum >= 1_i);
            //                }
            //            }});

            auto result = Inference::NoChange;
            // TODO: Bring this back!
            //            for (auto [idx, s] : enumerate(succ)) {
            //                increase_inference_to(result, state.infer_not_equal(s, Integer(idx), JustifyUsingRUP{}));
            //                if (result == Inference::Contradiction)
            //                    break;
            //            }
            return pair{result, PropagatorState::DisableUntilBacktrack};
        },
            Triggers{}, "circuit init");
    }

    return tuple{position, prev_wlog_line_handle, unassigned_handle};
}

auto CircuitBase::describe_for_proof() -> std::string
{
    return "circuit (all different + no sub-cycles)";
}

auto gcs::prevent_small_cycles(
    const vector<IntegerVariableID> & succ,
    const ConstraintStateHandle & prev_wlog_line_handle,
    const ConstraintStateHandle & unassigned_handle,
    const vector<ProofOnlySimpleIntegerVariableID> & pos_vars,
    State & state) -> Inference
{

    auto result = Inference::NoChange;
    auto & unassigned = any_cast<list<IntegerVariableID> &>(state.get_constraint_state(unassigned_handle));
    auto & prev_wlog_line = any_cast<long &>(state.get_persistent_constraint_state(prev_wlog_line_handle));
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
        increase_inference_to(result,
            state.infer(succ[end[i]] != Integer{i}, JustifyExplicitly{[&](Proof & proof, vector<ProofLine> & to_delete) {
                wlog_choose_vertex_as_position_0(i, succ, prev_wlog_line_handle, pos_vars, state);
                proof.emit_rup_proof_line_under_trail(state, WeightedPseudoBooleanSum{} + 1_i * (succ[end[i]] != Integer{i}) >= 1_i);
            }}));
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

auto gcs::wlog_choose_vertex_as_position_0(const long & v, const vector<IntegerVariableID> & succ, const ConstraintStateHandle & prev_wlog_line_handle, const vector<ProofOnlySimpleIntegerVariableID> & pos_vars, State & state) -> ProofLine
{
    // Uses the dominance rule to argue that, without loss of generality, we can choose the position of vertex v to be 0
    auto & prev_wlog_line = any_cast<long &>(state.get_persistent_constraint_state(prev_wlog_line_handle));
    string pveq = "p" + to_string(v) + "eq";
    auto n = static_cast<long long>(succ.size());
    auto dom_line = 0;
    state.infer_true(JustifyExplicitly{[&](Proof & proof, vector<ProofLine> & to_delete) {
        vector<pair<ProofLiteral, ProofLiteral>> witness{};
        vector<PseudoBooleanTerm> preorder_vars = {};

        for (unsigned int i = 0; i < n; i++) {
            for (unsigned j = 0; j < n - 1; j++) {
                witness.emplace_back(pos_vars[i] == Integer{j}, pos_vars[i] == Integer{j + 1});
            }
            witness.emplace_back(pos_vars[i] == Integer{n - 1}, pos_vars[i] == 0_i);
            preorder_vars.emplace_back(pos_vars[v] == Integer{i});
        }

        proof.emit_proof_comment(" WLOG choose pos[" + to_string(v) + "] = 0");

        // Introduce a new dummy pre_order to allow us to argue by symmetry
        const string preorder_name = "dummy_p" + to_string(v) + "eq0";
        WeightedPseudoBooleanSum potential_function{};
        for (unsigned int i = 0; i < n; i++) {
            potential_function += Integer{1ll << i} * preorder_vars[i];
        }

        // Then argue by dominance
        // Delete the previous wlog derivation, if there was one
        if (prev_wlog_line != -1)
            proof.delete_proof_lines({prev_wlog_line});

        proof.define_obviously_transitive_preorder(preorder_name, preorder_vars, potential_function);

        // TODO: Do we need to move all constraints to core set before changing the preorder
        proof.load_preorder(preorder_name, preorder_vars);

        // Go to root proof level (so we don't try to delete things multiple times)
        auto previous_proof_level = proof.get_proof_level();
        proof.enter_proof_level(0);

        // Then finally:
        prev_wlog_line = proof.emit_dom_proof_line(WeightedPseudoBooleanSum{} + 1_i * (pos_vars[v] == 0_i) >= 1_i, witness);
        // And return to where we were
        proof.enter_proof_level(previous_proof_level);

        // Reload the default order (empty)
        vector<PseudoBooleanTerm> empty_vars{};
        proof.load_preorder("", empty_vars);

    }});

    return dom_line;
}
