/* vim: set sw=4 sts=4 et foldmethod=syntax : */

#include <gcs/constraints/comparison.hh>
#include <gcs/constraints/element.hh>
#include <gcs/constraints/equals.hh>
#include <gcs/detail/proof.hh>
#include <gcs/detail/propagators.hh>
#include <gcs/detail/state.hh>
#include <gcs/exception.hh>
#include <gcs/integer.hh>

#include <util/for_each.hh>

#include <algorithm>
#include <optional>
#include <set>
#include <sstream>
#include <utility>
#include <vector>

using namespace gcs;

using std::make_optional;
using std::max;
using std::min;
using std::optional;
using std::pair;
using std::stringstream;
using std::vector;
using std::visit;

Element::Element(IntegerVariableID var, IntegerVariableID idx_var, const vector<IntegerVariableID> & vals) :
    _var(var),
    _idx_var(idx_var),
    _vals(vals)
{
}

auto Element::install(Propagators & propagators, const State & initial_state) && -> void
{
    if (_vals.empty()) {
        propagators.cnf(initial_state, {}, true);
        return;
    }

    // _idx_var >= 0, _idx_var < _vals.size()
    propagators.trim_lower_bound(initial_state, _idx_var, 0_i);
    propagators.trim_upper_bound(initial_state, _idx_var, Integer(_vals.size()) - 1_i);

    // _var <= max(upper(_vals)), _var >= min(lower(_vals))
    // ...and this should really be just over _vals that _idx_var might cover
    auto max_upper = initial_state.upper_bound(*max_element(_vals.begin(), _vals.end(), [&](const IntegerVariableID & v, const IntegerVariableID & w) {
        return initial_state.upper_bound(v) < initial_state.upper_bound(w);
    }));
    auto min_lower = initial_state.lower_bound(*min_element(_vals.begin(), _vals.end(), [&](const IntegerVariableID & v, const IntegerVariableID & w) {
        return initial_state.lower_bound(v) < initial_state.lower_bound(w);
    }));

    propagators.trim_lower_bound(initial_state, _var, min_lower);
    propagators.trim_upper_bound(initial_state, _var, max_upper);

    for_each_with_index(_vals, [&](auto & v, auto idx) {
        // _idx_var == i -> _var == _vals[idx]
        if (initial_state.in_domain(_idx_var, Integer(idx)))
            EqualsIf{_var, v, _idx_var == Integer(idx)}.install(propagators, initial_state);
    });

    initial_state.for_each_value(_var, [&](Integer val) {
        // _var == val -> exists i . _vals[idx] == val
        Literals options;
        options.emplace_back(_var != val);
        for_each_with_index(_vals, [&](auto & v, auto idx) {
            if (initial_state.in_domain(_idx_var, Integer(idx)) && initial_state.in_domain(v, val))
                options.emplace_back(v == val);
        });
        propagators.cnf(initial_state, move(options), true);
    });
}

auto Element::describe_for_proof() -> std::string
{
    return "element";
}

Element2DConstantArray::Element2DConstantArray(IntegerVariableID var, IntegerVariableID idx1,
    IntegerVariableID idx2, const vector<vector<Integer>> & vals) :
    _var(var),
    _idx1(idx1),
    _idx2(idx2),
    _vals(vals)
{
    if (! _vals.empty())
        for (const auto & v : _vals)
            if (v.size() != _vals.begin()->size())
                throw UnexpectedException{"didn't get a rectangular 2d array, not sure what to do"};
}

auto Element2DConstantArray::install(Propagators & propagators, const State & initial_state) && -> void
{
    if (_vals.empty() || _vals.begin()->empty()) {
        propagators.cnf(initial_state, {}, true);
        return;
    }

    propagators.trim_lower_bound(initial_state, _idx1, 0_i);
    propagators.trim_upper_bound(initial_state, _idx1, Integer(_vals.size()) - 1_i);

    propagators.trim_lower_bound(initial_state, _idx2, 0_i);
    propagators.trim_upper_bound(initial_state, _idx2, Integer(_vals.begin()->size()) - 1_i);

    if (propagators.want_nonpropagating()) {
        for_each_with_index(_vals, [&](auto & vv, auto idx1) {
            if (initial_state.in_domain(_idx1, Integer(idx1)))
                for_each_with_index(vv, [&](auto & v, auto idx2) {
                    if (initial_state.in_domain(_idx2, Integer(idx2)))
                        propagators.cnf(initial_state, {_idx1 != Integer(idx1), _idx2 != Integer(idx2), _var == v}, false);
                });
        });
    }

    Triggers index_triggers{
        .on_change = {_idx1, _idx2}};

    optional<SimpleIntegerVariableID> idxsel;
    propagators.propagator(
        initial_state, [idx1 = _idx1, idx2 = _idx2, var = _var, vals = _vals, idxsel = move(idxsel)](State & state) mutable -> pair<Inference, PropagatorState> {
            if (state.want_proofs() && ! idxsel) {
                idxsel = make_optional(state.create_pseudovariable(0_i, Integer(vals.size() * vals.begin()->size()), "element2didx"));

                state.add_proof_steps(JustifyExplicitly{[&](Proof & proof, vector<ProofLine> & to_delete) {
                    state.for_each_value(idx1, [&](Integer i1) {
                        state.for_each_value(idx2, [&](Integer i2) {
                            Integer idx = i1 * Integer(vals.size()) + i2;
                            stringstream line;
                            line << "red 2 ~" << proof.proof_variable(*idxsel == idx)
                                 << " 1 " << proof.proof_variable(idx1 == i1)
                                 << " 1 " << proof.proof_variable(idx2 == i2)
                                 << " >= 2 ; " << proof.proof_variable(*idxsel == idx) << " 0";
                            proof.emit_proof_line(line.str());

                            line = stringstream{};
                            line << "red 1 " << proof.proof_variable(*idxsel == idx)
                                 << " 1 ~" << proof.proof_variable(idx1 == i1)
                                 << " 1 ~" << proof.proof_variable(idx2 == i2)
                                 << " >= 1 ; " << proof.proof_variable(*idxsel == idx) << " 1";
                            proof.emit_proof_line(line.str());
                        });
                    });

                    stringstream trail;
                    for (Integer v = 0_i, v_end = Integer(vals.size() * vals.begin()->size()); v != v_end; ++v)
                        trail << " 1 " << proof.proof_variable(*idxsel == v);

                    state.for_each_value(idx1, [&](Integer i1) {
                        state.for_each_value(idx2, [&](Integer i2) {
                            stringstream line;
                            line << "u" << trail.str() << " 1 ~" << proof.proof_variable(idx1 == i1)
                                 << " 1 ~" << proof.proof_variable(idx2 == i2) << " >= 1 ;";
                            to_delete.push_back(proof.emit_proof_line(line.str()));
                        });
                        stringstream line;
                        line << "u" << trail.str() << " 1 ~" << proof.proof_variable(idx1 == i1) << " >= 1 ;";
                        to_delete.push_back(proof.emit_proof_line(line.str()));
                    });

                    stringstream line;
                    line << "u";
                    for (Integer v = 0_i, v_end = Integer(vals.size() * vals.begin()->size()); v != v_end; ++v)
                        line << " 1 " << proof.proof_variable(*idxsel == v);
                    line << " >= 1 ;";
                    proof.emit_proof_line(line.str());
                }});
            }

            optional<Integer> smallest_seen, largest_seen;
            state.for_each_value(idx1, [&](Integer i1) {
                state.for_each_value(idx2, [&](Integer i2) {
                    auto this_val = vals.at(i1.raw_value).at(i2.raw_value);
                    if (! smallest_seen)
                        smallest_seen = this_val;
                    else
                        smallest_seen = min(*smallest_seen, this_val);

                    if (! largest_seen)
                        largest_seen = this_val;
                    else
                        largest_seen = max(*largest_seen, this_val);
                });
            });

            auto inference = Inference::NoChange;
            auto just = JustifyExplicitly{[&](Proof & proof, vector<ProofLine> & to_delete) {
                stringstream trail;
                state.for_each_value(idx1, [&](Integer i1) {
                    state.for_each_value(idx2, [&](Integer i2) {
                        trail << " 1 " << proof.proof_variable(var == vals[i1.raw_value][i2.raw_value]);
                    });
                });
                trail << proof.trail_variables(state, 1_i);

                state.for_each_value(idx1, [&](Integer i1) {
                    state.for_each_value(idx2, [&](Integer i2) {
                        stringstream line;
                        line << "u" << trail.str() << " 1 ~" << proof.proof_variable(idx1 == i1)
                             << " 1 ~" << proof.proof_variable(idx2 == i2) << " >= 1 ;";
                        to_delete.push_back(proof.emit_proof_line(line.str()));
                    });
                    stringstream line;
                    line << "u" << trail.str() << " 1 ~" << proof.proof_variable(idx1 == i1) << " >= 1 ;";
                    to_delete.push_back(proof.emit_proof_line(line.str()));
                });

                stringstream line;
                line << "u" << trail.str() << " >= 1 ;";
                to_delete.push_back(proof.emit_proof_line(line.str()));
            }};

            increase_inference_to(inference, state.infer(var >= *smallest_seen, just));
            if (Inference::Contradiction != inference)
                increase_inference_to(inference, state.infer(var < *largest_seen + 1_i, just));

            return pair{inference, PropagatorState::Enable};
        },
        index_triggers, "element 2d const array indices");

    Triggers bounds_triggers{
        .on_bounds = {_var}};

    visit([&](auto & _idx1, auto & _idx2) {
        propagators.propagator(
            initial_state, [idx1 = _idx1, idx2 = _idx2, var = _var, vals = _vals](State & state) -> pair<Inference, PropagatorState> {
                auto bounds = state.bounds(var);
                auto inference = Inference::NoChange;

                state.for_each_value_while(idx1, [&](Integer i1) -> bool {
                    bool suitable_idx2_found = false;
                    state.for_each_value_while_immutable(idx2, [&](Integer i2) -> bool {
                        auto this_val = vals.at(i1.raw_value).at(i2.raw_value);
                        if (this_val >= bounds.first && this_val <= bounds.second) {
                            suitable_idx2_found = true;
                            return false;
                        }
                        return true;
                    });
                    if (! suitable_idx2_found)
                        increase_inference_to(inference, state.infer(idx1 != i1, JustifyUsingRUP{}));

                    return inference != Inference::Contradiction;
                });

                state.for_each_value_while(idx2, [&](Integer i2) -> bool {
                    bool suitable_idx1_found = false;
                    state.for_each_value_while_immutable(idx1, [&](Integer i1) -> bool {
                        auto this_val = vals.at(i1.raw_value).at(i2.raw_value);
                        if (this_val >= bounds.first && this_val <= bounds.second) {
                            suitable_idx1_found = true;
                            return false;
                        }
                        return true;
                    });
                    if (! suitable_idx1_found)
                        increase_inference_to(inference, state.infer(idx2 != i2, JustifyUsingRUP{}));

                    return inference != Inference::Contradiction;
                });

                return pair{inference, PropagatorState::Enable};
            },
            index_triggers, "element 2d const array var bounds");
    },
        _idx1, _idx2);
}

auto Element2DConstantArray::describe_for_proof() -> std::string
{
    return "element 2d const array";
}
