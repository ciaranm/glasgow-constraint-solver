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
#include <utility>
#include <vector>

using namespace gcs;
using namespace gcs::innards;

using std::max;
using std::min;
using std::optional;
using std::pair;
using std::unique_ptr;
using std::vector;
using std::visit;

Element::Element(IntegerVariableID var, IntegerVariableID idx, vector<IntegerVariableID> vals) :
    _var(var),
    _idx(idx),
    _vals(move(vals))
{
}

auto Element::clone() const -> unique_ptr<Constraint>
{
    return make_unique<Element>(_var, _idx, _vals);
}

auto Element::install(Propagators & propagators, State & initial_state) && -> void
{
    if (_vals.empty()) {
        propagators.model_contradiction("Element constraint with no values");
        return;
    }

    propagators.trim_lower_bound(initial_state, _idx, 0_i, "Element");
    propagators.trim_upper_bound(initial_state, _idx, Integer(_vals.size()) - 1_i, "Element");

    if (propagators.want_definitions()) {
        for (const auto & [val_idx, val] : enumerate(_vals))
            if (initial_state.in_domain(_idx, Integer(val_idx))) {
                // idx == val_idx -> var == vals[val_idx]
                propagators.define(initial_state, WeightedPseudoBooleanSum{} + 1_i * _var + -1_i * val == 0_i,
                    HalfReifyOnConjunctionOf{_idx == Integer(val_idx)});
            }
    }

    Triggers triggers{.on_change = {_idx, _var}};
    triggers.on_change.insert(triggers.on_change.end(), _vals.begin(), _vals.end());

    propagators.install([idx = _idx, var = _var, vals = _vals](State & state) mutable -> pair<Inference, PropagatorState> {
        Inference inf = Inference::NoChange;

        // update idx to only contain possible indices
        state.for_each_value_while(idx, [&](Integer ival) {
            bool supported = false;
            state.for_each_value_while_immutable(vals[ival.raw_value], [&](Integer vval) {
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
            state.for_each_value_while_immutable(idx, [&](Integer v) {
                if (state.in_domain(vals[v.raw_value], val))
                    supported = true;
                return ! supported;
            });
            if (! supported) {
                increase_inference_to(inf, state.infer_not_equal(var, val, JustifyExplicitly{[&](Proof & proof) {
                    state.for_each_value_immutable(idx, [&](Integer i) {
                        proof.emit_rup_proof_line_under_trail(state,
                            WeightedPseudoBooleanSum{} + 1_i * (var != val) + 1_i * (idx != i) >= 1_i, ProofLevel::Temporary);
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

ElementConstantArray::ElementConstantArray(IntegerVariableID var, IntegerVariableID idx, vector<Integer> * vals) :
    _var(var),
    _idx(idx),
    _vals(vals)
{
}

auto ElementConstantArray::clone() const -> unique_ptr<Constraint>
{
    return make_unique<ElementConstantArray>(_var, _idx, _vals);
}

auto ElementConstantArray::install(Propagators & propagators, State & initial_state) && -> void
{
    if (_vals->empty()) {
        propagators.model_contradiction("ElementConstantArray constraint with no values");
        return;
    }

    propagators.trim_lower_bound(initial_state, _idx, 0_i, "ElementConstantArray");
    propagators.trim_upper_bound(initial_state, _idx, Integer(_vals->size()) - 1_i, "ElementConstantArray");

    if (propagators.want_definitions()) {
        for (const auto & [idx, v] : enumerate(*_vals))
            if (initial_state.in_domain(_idx, Integer(idx)))
                propagators.define_cnf(initial_state, {_idx != Integer(idx), _var == v});
    }

    Triggers triggers{
        .on_change = {_idx},
        .on_bounds = {_var}};

    visit([&](auto & _idx) {
        propagators.install([idx = _idx, var = _var, vals = _vals](State & state) -> pair<Inference, PropagatorState> {
            optional<Integer> smallest_seen, largest_seen;
            state.for_each_value_immutable(idx, [&](Integer i) {
                auto this_val = vals->at(i.raw_value);
                if (! smallest_seen)
                    smallest_seen = this_val;
                else
                    smallest_seen = min(*smallest_seen, this_val);

                if (! largest_seen)
                    largest_seen = this_val;
                else
                    largest_seen = max(*largest_seen, this_val);
            });

            auto inference = Inference::NoChange;
            auto just = JustifyExplicitly{[&](Proof & proof) {
                WeightedPseudoBooleanSum trail = proof.trail_variables_as_sum(state, 1_i);
                state.for_each_value_immutable(idx, [&](Integer i) {
                    trail += 1_i * (var == (*vals)[i.raw_value]);
                });

                state.for_each_value_immutable(idx, [&](Integer i) {
                    proof.emit_rup_proof_line(trail + 1_i * (idx == i) >= 1_i, ProofLevel::Temporary);
                });

                proof.emit_rup_proof_line(trail >= 1_i, ProofLevel::Temporary);
            }};

            increase_inference_to(inference, state.infer_greater_than_or_equal(var, *smallest_seen, just));
            if (Inference::Contradiction == inference)
                return pair{inference, PropagatorState::Enable};
            increase_inference_to(inference, state.infer_less_than(var, *largest_seen + 1_i, just));
            if (Inference::Contradiction == inference)
                return pair{inference, PropagatorState::Enable};

            auto bounds = state.bounds(var);

            state.for_each_value_while(idx, [&](Integer i) -> bool {
                auto this_val = vals->at(i.raw_value);
                if (this_val < bounds.first || this_val > bounds.second)
                    increase_inference_to(inference, state.infer(idx != i, JustifyUsingRUP{}));
                return inference != Inference::Contradiction;
            });

            return pair{inference, PropagatorState::Enable};
        },
            triggers, "element const array var bounds");
    },
        _idx);
}

auto ElementConstantArray::describe_for_proof() -> std::string
{
    return "element const array";
}

Element2DConstantArray::Element2DConstantArray(IntegerVariableID var, IntegerVariableID idx1,
    IntegerVariableID idx2, vector<vector<Integer>> * vals) :
    _var(var),
    _idx1(idx1),
    _idx2(idx2),
    _vals(vals)
{
    if (! _vals->empty())
        for (const auto & v : *_vals)
            if (v.size() != _vals->begin()->size())
                throw UnexpectedException{"didn't get a rectangular 2d array, not sure what to do"};
}

auto Element2DConstantArray::clone() const -> unique_ptr<Constraint>
{
    return make_unique<Element2DConstantArray>(_var, _idx1, _idx2, _vals);
}

auto Element2DConstantArray::install(Propagators & propagators, State & initial_state) && -> void
{
    if (_vals->empty() || _vals->begin()->empty()) {
        propagators.model_contradiction("Element2DConstantArray constraint with no values");
        return;
    }

    propagators.trim_lower_bound(initial_state, _idx1, 0_i, "Element2DConstantArray");
    propagators.trim_upper_bound(initial_state, _idx1, Integer(_vals->size()) - 1_i, "Element2DConstantArray");

    propagators.trim_lower_bound(initial_state, _idx2, 0_i, "Element2DConstantArray");
    propagators.trim_upper_bound(initial_state, _idx2, Integer(_vals->begin()->size()) - 1_i, "Element2DConstantArray");

    if (propagators.want_definitions()) {
        for (const auto & [idx1, vv] : enumerate(*_vals))
            if (initial_state.in_domain(_idx1, Integer(idx1)))
                for (const auto & [idx2, v] : enumerate(vv))
                    if (initial_state.in_domain(_idx2, Integer(idx2)))
                        propagators.define_cnf(initial_state, {_idx1 != Integer(idx1), _idx2 != Integer(idx2), _var == v});
    }

    Triggers triggers{
        .on_change = {_idx1, _idx2},
        .on_bounds = {_var}};

    optional<SimpleIntegerVariableID> idxsel;
    visit([&](auto & _idx1, auto & _idx2) {
        propagators.install([idx1 = _idx1, idx2 = _idx2, var = _var, vals = _vals, idxsel = move(idxsel)](State & state) mutable -> pair<Inference, PropagatorState> {
            // turn 2d index into 1d index in proof
            if (state.maybe_proof() && ! idxsel) [[unlikely]] {
                idxsel = state.what_variable_id_will_be_created_next();
                for (auto i = 0_i, i_end = Integer(vals->size() * vals->begin()->size()); i != i_end; ++i)
                    state.maybe_proof()->create_literals_for_introduced_variable_value(*idxsel, i, "element2didx");
                if (*idxsel != state.allocate_integer_variable_with_state(0_i, Integer(vals->size() * vals->begin()->size())))
                    throw UnexpectedException{"something went horribly wrong with variable IDs"};

                state.infer_true(JustifyExplicitly{[&](Proof & proof) {
                    state.for_each_value_immutable(idx1, [&](Integer i1) {
                        state.for_each_value_immutable(idx2, [&](Integer i2) {
                            Integer idx = i1 * Integer(vals->size()) + i2;
                            proof.emit_red_proof_line(WeightedPseudoBooleanSum{} +
                                        2_i * ! (*idxsel == idx) + 1_i * (idx1 == i1) + 1_i * (idx2 == i2) >=
                                    2_i,
                                {{*idxsel == idx, FalseLiteral{}}}, ProofLevel::Top);
                            proof.emit_red_proof_line(WeightedPseudoBooleanSum{} +
                                        1_i * (*idxsel == idx) + 1_i * (idx1 != i1) + 1_i * (idx2 != i2) >=
                                    1_i,
                                {{*idxsel == idx, TrueLiteral{}}}, ProofLevel::Top);
                        });
                    });

                    WeightedPseudoBooleanSum trail;
                    for (Integer v = 0_i, v_end = Integer(vals->size() * vals->begin()->size()); v != v_end; ++v)
                        trail += 1_i * (*idxsel == v);

                    state.for_each_value_immutable(idx1, [&](Integer i1) {
                        state.for_each_value_immutable(idx2, [&](Integer i2) {
                            WeightedPseudoBooleanSum expr = trail;
                            expr += 1_i * (idx1 != i1);
                            expr += 1_i * (idx2 != i2);
                            proof.emit_rup_proof_line(expr >= 1_i, ProofLevel::Temporary);
                        });
                        WeightedPseudoBooleanSum expr = trail;
                        expr += 1_i * (idx1 != i1);
                        proof.emit_rup_proof_line(expr >= 1_i, ProofLevel::Temporary);
                    });

                    WeightedPseudoBooleanSum expr;
                    for (Integer v = 0_i, v_end = Integer(vals->size() * vals->begin()->size()); v != v_end; ++v)
                        expr += 1_i * (*idxsel == v);
                    proof.emit_rup_proof_line(expr >= 1_i, ProofLevel::Top);
                }});
            }

            // find smallest and largest possible values, for bounds on the var
            optional<Integer> smallest_seen, largest_seen;
            state.for_each_value_immutable(idx1, [&](Integer i1) {
                state.for_each_value_immutable(idx2, [&](Integer i2) {
                    auto this_val = vals->at(i1.raw_value).at(i2.raw_value);
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

            auto just = JustifyExplicitly{[&](Proof & proof) {
                WeightedPseudoBooleanSum trail = proof.trail_variables_as_sum(state, 1_i);
                state.for_each_value_immutable(idx1, [&](Integer i1) {
                    state.for_each_value_immutable(idx2, [&](Integer i2) {
                        trail += 1_i * (var == (*vals)[i1.raw_value][i2.raw_value]);
                    });
                });

                state.for_each_value_immutable(idx1, [&](Integer i1) {
                    state.for_each_value_immutable(idx2, [&](Integer i2) {
                        WeightedPseudoBooleanSum expr = trail;
                        expr += 1_i * (idx1 != i1);
                        expr += 1_i * (idx2 != i2);
                        proof.emit_rup_proof_line(expr >= 1_i, ProofLevel::Temporary);
                    });
                    WeightedPseudoBooleanSum expr = trail;
                    expr += 1_i * (idx1 != i1);
                    proof.emit_rup_proof_line(expr >= 1_i, ProofLevel::Temporary);
                });

                proof.emit_rup_proof_line(trail >= 1_i, ProofLevel::Temporary);
            }};

            auto inference = state.infer_greater_than_or_equal(var, *smallest_seen, just);
            if (Inference::Contradiction == inference)
                return pair{inference, PropagatorState::Enable};

            increase_inference_to(inference, state.infer_less_than(var, *largest_seen + 1_i, just));
            if (Inference::Contradiction == inference)
                return pair{inference, PropagatorState::Enable};

            auto bounds = state.bounds(var);

            // check each idx1 has a suitable element
            state.for_each_value_while(idx1, [&](Integer i1) -> bool {
                bool suitable_idx2_found = false;
                state.for_each_value_while_immutable(idx2, [&](Integer i2) -> bool {
                    auto this_val = vals->at(i1.raw_value).at(i2.raw_value);
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

            if (Inference::Contradiction == inference)
                return pair{inference, PropagatorState::Enable};

            // check each idx2 has a suitable element
            state.for_each_value_while(idx2, [&](Integer i2) -> bool {
                bool suitable_idx1_found = false;
                state.for_each_value_while_immutable(idx1, [&](Integer i1) -> bool {
                    auto this_val = vals->at(i1.raw_value).at(i2.raw_value);
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
            triggers, "element 2d const array var bounds");
    },
        _idx1, _idx2);
}

auto Element2DConstantArray::describe_for_proof() -> std::string
{
    return "element 2d const array";
}
