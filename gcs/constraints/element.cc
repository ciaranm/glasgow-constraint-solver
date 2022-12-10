/* vim: set sw=4 sts=4 et foldmethod=syntax : */

#include <gcs/constraints/comparison.hh>
#include <gcs/constraints/element.hh>
#include <gcs/constraints/equals.hh>
#include <gcs/exception.hh>
#include <gcs/innards/proof.hh>
#include <gcs/innards/propagators.hh>
#include <gcs/innards/state.hh>
#include <gcs/integer.hh>

#include <util/enumerate.hh>

#include <algorithm>
#include <optional>
#include <set>
#include <sstream>
#include <utility>
#include <vector>

using namespace gcs;
using namespace gcs::innards;

using std::make_optional;
using std::max;
using std::min;
using std::optional;
using std::pair;
using std::stringstream;
using std::unique_ptr;
using std::vector;
using std::visit;

Element::Element(IntegerVariableID var, IntegerVariableID idx, const vector<IntegerVariableID> & vals) :
    _var(var),
    _idx(idx),
    _vals(vals)
{
}

auto Element::clone() const -> unique_ptr<Constraint>
{
    return make_unique<Element>(_var, _idx, _vals);
}

auto Element::install(Propagators & propagators, const State & initial_state) && -> void
{
    if (_vals.empty()) {
        propagators.model_contradiction(initial_state, "Element constraint with no values");
        return;
    }

    propagators.trim_lower_bound(initial_state, _idx, 0_i, "Element");
    propagators.trim_upper_bound(initial_state, _idx, Integer(_vals.size()) - 1_i, "Element");

    if (propagators.want_definitions()) {
        for (const auto & [val_idx, val] : enumerate(_vals))
            if (initial_state.in_domain(_idx, Integer(val_idx))) {
                // idx == val_idx -> var == vals[val_idx]
                auto cv = Linear{{1_i, _var}, {-1_i, val}};
                propagators.define_linear_eq(initial_state, cv, 0_i, _idx == Integer(val_idx));
            }
    }

    Triggers triggers{.on_change = {_idx, _var}};
    triggers.on_change.insert(triggers.on_change.end(), _vals.begin(), _vals.end());

    propagators.install(
        initial_state, [idx = _idx, var = _var, vals = _vals](State & state) mutable -> pair<Inference, PropagatorState> {
            Inference inf = Inference::NoChange;

            // update idx to only contain possible indices
            state.for_each_value_while(idx, [&](Integer ival) {
                bool supported = false;
                state.for_each_value_while(vals[ival.raw_value], [&](Integer vval) {
                    if (state.in_domain(var, vval))
                        supported = true;
                    return ! supported;
                });
                if (! supported)
                    increase_inference_to(inf, state.infer_not_equal(idx, ival, JustifyUsingRUP{}));
                return inf != Inference::Contradiction;
            });

            if (Inference::Contradiction == inf)
                return pair{inf, PropagatorState::Enable};

            // update var to only contain supported values
            state.for_each_value_while(var, [&](Integer val) {
                bool supported = false;
                state.for_each_value_while(idx, [&](Integer v) {
                    if (state.in_domain(vals[v.raw_value], val))
                        supported = true;
                    return ! supported;
                });
                if (! supported) {
                    increase_inference_to(inf, state.infer_not_equal(var, val, JustifyExplicitly{[&](Proof & proof, vector<ProofLine> & to_delete) {
                        state.for_each_value(idx, [&](Integer i) {
                            proof.need_proof_variable(var != val);
                            stringstream trail;
                            trail << "u ";
                            trail << proof.trail_variables(state, 1_i) << " 1 " << proof.proof_variable(var != val)
                                  << " 1 " << proof.proof_variable(idx != i);
                            trail << " >= 1 ;";
                            to_delete.push_back(proof.emit_proof_line(trail.str()));
                        });
                    }}));

                    if (Inference::Contradiction == inf)
                        return false;
                }
                return true;
            });

            if (Inference::Contradiction == inf)
                return pair{inf, PropagatorState::Enable};

            // if idx has only one value, force that val
            auto idx_is = state.optional_single_value(idx);
            if (idx_is) {
                state.for_each_value_while(vals[idx_is->raw_value], [&](Integer val) {
                    if (! state.in_domain(var, val))
                        increase_inference_to(inf, state.infer_not_equal(vals[idx_is->raw_value], val, JustifyUsingRUP{}));
                    return inf != Inference::Contradiction;
                });
            }

            return pair{inf, PropagatorState::Enable};
        },
        triggers, "element index");
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

auto Element2DConstantArray::clone() const -> unique_ptr<Constraint>
{
    return make_unique<Element2DConstantArray>(_var, _idx1, _idx2, _vals);
}

auto Element2DConstantArray::install(Propagators & propagators, const State & initial_state) && -> void
{
    if (_vals.empty() || _vals.begin()->empty()) {
        propagators.model_contradiction(initial_state, "Element2DConstantArray constraint with no values");
        return;
    }

    propagators.trim_lower_bound(initial_state, _idx1, 0_i, "Element2DConstantArray");
    propagators.trim_upper_bound(initial_state, _idx1, Integer(_vals.size()) - 1_i, "Element2DConstantArray");

    propagators.trim_lower_bound(initial_state, _idx2, 0_i, "Element2DConstantArray");
    propagators.trim_upper_bound(initial_state, _idx2, Integer(_vals.begin()->size()) - 1_i, "Element2DConstantArray");

    if (propagators.want_definitions()) {
        for (const auto & [idx1, vv] : enumerate(_vals))
            if (initial_state.in_domain(_idx1, Integer(idx1)))
                for (const auto & [idx2, v] : enumerate(vv))
                    if (initial_state.in_domain(_idx2, Integer(idx2)))
                        propagators.define_cnf(initial_state, {_idx1 != Integer(idx1), _idx2 != Integer(idx2), _var == v});
    }

    Triggers index_triggers{
        .on_change = {_idx1, _idx2}};

    optional<SimpleIntegerVariableID> idxsel;
    propagators.install(
        initial_state, [idx1 = _idx1, idx2 = _idx2, var = _var, vals = _vals, idxsel = move(idxsel)](State & state) mutable -> pair<Inference, PropagatorState> {
            if (state.maybe_proof() && ! idxsel) [[unlikely]] {
                idxsel = state.what_variable_id_will_be_created_next();
                for (auto i = 0_i, i_end = Integer(vals.size() * vals.begin()->size()); i != i_end; ++i)
                    state.maybe_proof()->create_literals_for_introduced_variable_value(*idxsel, i, "element2didx");
                if (*idxsel != state.allocate_integer_variable_with_state(0_i, Integer(vals.size() * vals.begin()->size())))
                    throw UnexpectedException{"something went horribly wrong with variable IDs"};

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

            increase_inference_to(inference, state.infer_greater_than_or_equal(var, *smallest_seen, just));
            if (Inference::Contradiction != inference)
                increase_inference_to(inference, state.infer_less_than(var, *largest_seen + 1_i, just));

            return pair{inference, PropagatorState::Enable};
        },
        index_triggers, "element 2d const array indices");

    Triggers bounds_triggers{
        .on_bounds = {_var}};

    visit([&](auto & _idx1, auto & _idx2) {
        propagators.install(
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
            bounds_triggers, "element 2d const array var bounds");
    },
        _idx1, _idx2);
}

auto Element2DConstantArray::describe_for_proof() -> std::string
{
    return "element 2d const array";
}
