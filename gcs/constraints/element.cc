#include <gcs/constraints/comparison.hh>
#include <gcs/constraints/element.hh>
#include <gcs/constraints/equals.hh>
#include <gcs/exception.hh>
#include <gcs/innards/inference_tracker.hh>
#include <gcs/innards/proofs/names_and_ids_tracker.hh>
#include <gcs/innards/proofs/proof_logger.hh>
#include <gcs/innards/proofs/proof_model.hh>
#include <gcs/innards/propagators.hh>
#include <gcs/innards/state.hh>
#include <gcs/integer.hh>

#include <util/enumerate.hh>

#include <algorithm>
#include <functional>
#include <memory>
#include <optional>
#include <set>
#include <utility>
#include <vector>

using namespace gcs;
using namespace gcs::innards;

using std::array;
using std::function;
using std::make_shared;
using std::max;
using std::min;
using std::optional;
using std::pair;
using std::set;
using std::shared_ptr;
using std::unique_ptr;
using std::vector;
using std::visit;

namespace
{
    template <typename T_>
    auto check_array_dimensions(const vector<vector<T_>> & v, size_t expected) -> void;

    template <typename T_>
    auto check_array_dimensions(const vector<T_> & v, size_t expected) -> void
    {
        if (v.size() != expected)
            throw UnexpectedException{"didn't get a regularly sized array for element constraint"};
    }

    template <typename T_>
    auto check_array_dimensions(const vector<vector<T_>> & v, size_t expected) -> void
    {
        if (v.size() != expected)
            throw UnexpectedException{"didn't get a regularly sized array for element constraint"};

        for (const auto & vv : v) {
            check_array_dimensions(vv, v.at(0).size());
        }
    }
}

template <typename EntryType_, unsigned dimensions_>
NDimensionalElement<EntryType_, dimensions_>::NDimensionalElement(IntegerVariableID var, IndexVariables i, IndexStarts s, Array * a, bool b) :
    _result_var(var),
    _index_vars(move(i)),
    _index_starts(move(s)),
    _array(a),
    _bounds_only(b)
{
    check_array_dimensions(*_array, _array->size());
}

namespace
{
    template <unsigned dims_remaining_, typename T_>
    auto get_dimension_size(unsigned desired_dim, const T_ & vec) -> size_t
    {
        if (0 == desired_dim)
            return vec.size();
        else {
            if constexpr (dims_remaining_ < 2)
                throw UnexpectedException{"NDimensionalElement dimension fetching code is broken"};
            else
                return get_dimension_size<dims_remaining_ - 1>(desired_dim - 1, vec.at(0));
        }
    }

    auto as_integer_variable(const IntegerVariableID & var) -> IntegerVariableID
    {
        return var;
    }

    auto as_integer_variable(const Integer & i) -> IntegerVariableID
    {
        return ConstantIntegerVariableID{i};
    }

    template <unsigned dims_remaining_, typename T_>
    auto get_array_var(const vector<size_t> & indices, const T_ & vec, size_t current_index = 0) -> IntegerVariableID
    {
        if constexpr (1 == dims_remaining_) {
            return as_integer_variable(vec.at(indices.at(current_index)));
        }
        else if constexpr (0 == dims_remaining_) {
            throw UnexpectedException{"NDimensionalElement element fetching code is broken"};
        }
        else {
            return get_array_var<dims_remaining_ - 1>(indices, vec.at(indices.at(current_index)), current_index + 1);
        }
    }

    template <typename T_>
    auto any_array_variable_is_nonconstant(const State & initial_state, const vector<vector<T_>> & vec) -> bool;

    template <typename T_>
    auto any_array_variable_is_nonconstant(const State & initial_state, const vector<T_> & vec) -> bool
    {
        return any_of(vec.begin(), vec.end(), [&](const auto & v) { return ! initial_state.has_single_value(as_integer_variable(v)); });
    }

    template <typename T_>
    auto any_array_variable_is_nonconstant(const State & initial_state, const vector<vector<T_>> & vec) -> bool
    {
        for (const auto & v : vec)
            if (any_array_variable_is_nonconstant(initial_state, v))
                return true;
        return false;
    }
}

template <typename EntryType_, unsigned dimensions_>
auto NDimensionalElement<EntryType_, dimensions_>::install(innards::Propagators & propagators, innards::State & initial_state, innards::ProofModel * const optional_model) && -> void
{
    for (const auto & [i, var] : enumerate(_index_vars)) {
        auto s = Integer(get_dimension_size<dimensions_>(i, *_array));
        if (0_i == s) {
            propagators.model_contradiction(initial_state, optional_model, "NDimensionalElement constraint with no values");
            return;
        }

        propagators.trim_lower_bound(initial_state, optional_model, var, _index_starts.at(i), "NDimensionalElement");
        propagators.trim_upper_bound(initial_state, optional_model, var, _index_starts.at(i) + s - 1_i, "NDimensionalElement");
    }

    if (optional_model) {
        HalfReifyOnConjunctionOf reif;
        vector<size_t> elem;

        function<auto(unsigned)->void> build_implication_constraints = [&](unsigned d) {
            auto s = get_dimension_size<dimensions_>(d, *_array);
            for (size_t x = 0; x != s; ++x) {
                reif.push_back(_index_vars.at(d) == Integer(x) + _index_starts.at(d));
                elem.push_back(x);
                if (elem.size() == dimensions_) {
                    // this still works out fine if the variable is actually a constant
                    auto array_var = get_array_var<dimensions_>(elem, *_array);
                    optional_model->add_constraint("NDimensionalElement", "equality",
                        WeightedPseudoBooleanSum{} + (1_i * _result_var) + (-1_i * array_var) == 0_i, reif);
                }
                else {
                    build_implication_constraints(d + 1);
                }
                elem.pop_back();
                reif.pop_back();
            }
        };
        build_implication_constraints(0);
    }

    auto array_has_nonconstants = any_array_variable_is_nonconstant(initial_state, *_array);

    vector<IntegerVariableID> all_array_vars;
    {
        vector<size_t> elem;
        function<auto(unsigned)->void> collect_array_variables = [&](unsigned d) {
            auto s = get_dimension_size<dimensions_>(d, *_array);
            for (size_t x = 0; x != s; ++x) {
                elem.push_back(x);
                if (elem.size() == dimensions_) {
                    auto array_var = get_array_var<dimensions_>(elem, *_array);
                    all_array_vars.emplace_back(array_var);
                }
                else {
                    collect_array_variables(d + 1);
                }
                elem.pop_back();
            }
        };
        if (array_has_nonconstants)
            collect_array_variables(0);
    }

    for (unsigned fixed_dim = 0; fixed_dim != _index_vars.size(); ++fixed_dim) {
        Triggers index_triggers;
        if (array_has_nonconstants) {
            if (_bounds_only)
                index_triggers.on_bounds.insert(index_triggers.on_change.end(), all_array_vars.begin(), all_array_vars.end());
            else
                index_triggers.on_change.insert(index_triggers.on_change.end(), all_array_vars.begin(), all_array_vars.end());
        }

        if (_bounds_only)
            index_triggers.on_bounds.emplace_back(_result_var);
        else
            index_triggers.on_change.emplace_back(_result_var);

        for (const auto & [idx, var] : enumerate(_index_vars))
            if (idx != fixed_dim)
                index_triggers.on_change.emplace_back(var);

        propagators.install([array = _array, index_vars = _index_vars, index_starts = _index_starts, result_var = _result_var, fixed_dim = fixed_dim,
                                array_has_nonconstants = array_has_nonconstants, bounds_only = _bounds_only](
                                const State & state, auto & inference, ProofLogger * const logger) -> PropagatorState {
            // for each index variable, update it to only contain values where
            // there's at least one supporting option
            for (const auto & test_val : state.each_value_mutable(index_vars.at(fixed_dim))) {
                auto looking_for = state.copy_of_values(result_var);
                auto looking_for_bounds = state.bounds(result_var);

                vector<size_t> elem;
                vector<IntegerVariableID> explored_vars;
                explored_vars.push_back(result_var);
                function<auto(unsigned)->bool> look_for_support = [&](unsigned d) -> bool {
                    // we're iterating over every dimension recursively, except for the one where
                    // we're checking support for the fixed test_val.
                    auto do_it_with = [&](Integer x) {
                        elem.push_back(x.raw_value - index_starts.at(d).raw_value);
                        if (elem.size() == dimensions_) {
                            auto array_var = get_array_var<dimensions_>(elem, *array);
                            if (array_has_nonconstants)
                                explored_vars.push_back(array_var);

                            if (bounds_only) {
                                if (state.lower_bound(array_var) >= looking_for_bounds.first && state.upper_bound(array_var) <= looking_for_bounds.second)
                                    return true;
                            }
                            else {
                                if (looking_for.contains_any_of(state.copy_of_values(array_var)))
                                    return true;
                            }
                        }
                        else {
                            if (look_for_support(d + 1))
                                return true;
                        }
                        elem.pop_back();
                        return false;
                    };

                    if (d == fixed_dim)
                        return do_it_with(test_val);
                    else {
                        explored_vars.push_back(index_vars.at(d));
                        for (const auto & x : state.each_value_immutable(index_vars.at(d)))
                            if (do_it_with(x))
                                return true;

                        return false;
                    }
                };

                if (! look_for_support(0)) {
                    inference.infer_not_equal(logger, index_vars.at(fixed_dim), test_val, JustifyExplicitly{[&](const ExpandedReason & reason) {
                        // show there's no overlap between array_var and result, for any way the other
                        // index vars are assigned
                        vector<size_t> elem;
                        WeightedPseudoBooleanSum sum_so_far;
                        function<auto(unsigned)->void> show_no_support = [&](unsigned d) -> void {
                            // again, we're iterating over every dimension recursively, except for the one where
                            // we're checking support for the fixed test_val.
                            auto do_it_with = [&](Integer x) {
                                elem.push_back(x.raw_value - index_starts.at(d).raw_value);

                                if (elem.size() == dimensions_) {
                                    auto array_var = get_array_var<dimensions_>(elem, *array);
                                    if (bounds_only && array_has_nonconstants) {
                                        throw UnimplementedException{};
                                    }
                                    else {
                                        for (const auto & v : state.each_value_immutable(array_var))
                                            logger->emit_rup_proof_line_under_reason(reason,
                                                sum_so_far + 1_i * (index_vars.at(fixed_dim) != test_val) + 1_i * (array_var != v) >= 1_i, ProofLevel::Temporary);
                                    }
                                }
                                else
                                    show_no_support(d + 1);

                                elem.pop_back();
                            };

                            if (d == fixed_dim)
                                return do_it_with(test_val);
                            else {
                                for (const auto & x : state.each_value_immutable(index_vars.at(d))) {
                                    auto save_sum_so_far = sum_so_far;
                                    sum_so_far += 1_i * (index_vars.at(d) != x);
                                    do_it_with(x);
                                    logger->emit_rup_proof_line_under_reason(reason,
                                        sum_so_far + 1_i * (index_vars.at(fixed_dim) != test_val) >= 1_i,
                                        ProofLevel::Temporary);
                                    sum_so_far = save_sum_so_far;
                                }
                            }
                        };

                        show_no_support(0);
                    }},
                        transform_into_reason_outline<ExactValuesLost>(explored_vars));
                }
            }

            return PropagatorState::Enable;
        },
            {all_array_vars, _index_vars, _result_var}, index_triggers, "NDimensionalElement index");
    }

    if (_bounds_only) {
        Triggers result_triggers;
        if (array_has_nonconstants)
            result_triggers.on_bounds.insert(result_triggers.on_change.end(), all_array_vars.begin(), all_array_vars.end());
        result_triggers.on_change.insert(result_triggers.on_change.end(), _index_vars.begin(), _index_vars.end());
        result_triggers.on_bounds.emplace_back(_result_var);

        propagators.install([array = _array, index_vars = _index_vars, index_starts = _index_starts, result_var = _result_var, array_has_nonconstants = array_has_nonconstants](
                                const State & state, auto & inference, ProofLogger * const logger) -> PropagatorState {
            // bounds only, so the result variable has to be in the range
            // (rather than the union) of possible values
            vector<size_t> elem;
            optional<Integer> lowest_found, highest_found;
            auto current_bounds = state.bounds(result_var);
            vector<IntegerVariableID> considered_vars;
            function<auto(unsigned)->void> collect_supported_bounds = [&](unsigned d) {
                for (const auto & x : state.each_value_immutable(index_vars.at(d))) {
                    if (lowest_found && *lowest_found <= current_bounds.first && highest_found && *highest_found >= current_bounds.second)
                        return;

                    elem.push_back(x.raw_value - index_starts.at(d).raw_value);
                    if (elem.size() == dimensions_) {
                        auto array_var = get_array_var<dimensions_>(elem, *array);
                        if (array_has_nonconstants)
                            considered_vars.push_back(array_var);
                        auto array_var_bounds = state.bounds(array_var);
                        if (current_bounds.second >= array_var_bounds.first && current_bounds.first <= array_var_bounds.second) {
                            lowest_found = lowest_found ? min(*lowest_found, array_var_bounds.first) : array_var_bounds.first;
                            highest_found = highest_found ? max(*highest_found, array_var_bounds.second) : array_var_bounds.second;
                        }
                    }
                    else {
                        collect_supported_bounds(d + 1);
                    }
                    elem.pop_back();
                }
            };
            collect_supported_bounds(0);

            auto infer_bound = [&](Integer relevant_bound, bool ge) {
                auto lit_to_infer = ge ? (result_var >= relevant_bound) : (result_var < relevant_bound + 1_i);
                auto reason = transform_into_reason_outline<ExactValuesLost>(index_vars);
                for (const auto & var : considered_vars)
                    reason.push_back(ge ? (var >= relevant_bound) : (var < relevant_bound + 1_i));
                reason.push_back(result_var >= current_bounds.first);
                reason.push_back(result_var < current_bounds.second + 1_i);
                inference.infer(logger, lit_to_infer, JustifyExplicitly{[&](const ExpandedReason & reason) {
                    // show that it doesn't work for any feasible choice of indices
                    WeightedPseudoBooleanSum sum_so_far;
                    function<auto(unsigned)->void> rule_out = [&](unsigned d) {
                        for (const auto & v : state.each_value_immutable(index_vars.at(d))) {
                            if (d + 1 == dimensions_)
                                logger->emit_rup_proof_line_under_reason(reason,
                                    sum_so_far + 1_i * lit_to_infer + 1_i * (index_vars.at(d) != v) >= 1_i,
                                    ProofLevel::Temporary);
                            else {
                                auto save_sum_so_far = sum_so_far;
                                sum_so_far += 1_i * (index_vars.at(d) != v);
                                rule_out(d + 1);
                                sum_so_far = save_sum_so_far;
                            }
                        }
                        if (! sum_so_far.terms.empty()) {
                            logger->emit_rup_proof_line_under_reason(reason,
                                sum_so_far + 1_i * lit_to_infer >= 1_i,
                                ProofLevel::Temporary);
                        }
                    };
                    rule_out(0);
                }},
                    reason);
            };

            if (lowest_found && *lowest_found > current_bounds.first)
                infer_bound(*lowest_found, true);

            if (highest_found && *highest_found < current_bounds.second)
                infer_bound(*highest_found, false);

            return PropagatorState::Enable;
        },
            {all_array_vars, _index_vars, _result_var}, result_triggers, "NDimensionalElement");
    }
    else {
        Triggers result_triggers;
        if (array_has_nonconstants)
            result_triggers.on_change.insert(result_triggers.on_change.end(), all_array_vars.begin(), all_array_vars.end());
        result_triggers.on_change.insert(result_triggers.on_change.end(), _index_vars.begin(), _index_vars.end());

        propagators.install([array = _array, index_vars = _index_vars, index_starts = _index_starts, result_var = _result_var, array_has_nonconstants = array_has_nonconstants](
                                const State & state, auto & inference, ProofLogger * const logger) -> PropagatorState {
            // the result variable has to be in the union of possible values
            vector<size_t> elem;
            IntervalSet<Integer> still_to_find_support_for = state.copy_of_values(result_var);
            vector<IntegerVariableID> considered_vars;
            function<auto(unsigned)->void> collect_supported_values = [&](unsigned d) {
                for (const auto & x : state.each_value_immutable(index_vars.at(d))) {
                    if (still_to_find_support_for.empty())
                        return;

                    elem.push_back(x.raw_value - index_starts.at(d).raw_value);
                    if (elem.size() == dimensions_) {
                        auto array_var = get_array_var<dimensions_>(elem, *array);
                        if (array_has_nonconstants)
                            considered_vars.push_back(array_var);
                        for (const auto & v : state.each_value_immutable(array_var))
                            still_to_find_support_for.erase(v);
                    }
                    else {
                        collect_supported_values(d + 1);
                    }
                    elem.pop_back();
                }
            };
            collect_supported_values(0);

            for (auto value : still_to_find_support_for.each()) {
                auto reason = transform_into_reason_outline<ExactValuesLost>(index_vars);
                for (const auto & var : considered_vars)
                    reason.push_back(var != value);
                inference.infer_not_equal(logger, result_var, value, JustifyExplicitly{[&](const ExpandedReason & reason) {
                    // show that it doesn't work for any feasible choice of indices
                    WeightedPseudoBooleanSum sum_so_far;
                    function<auto(unsigned)->void> rule_out = [&](unsigned d) {
                        for (const auto & v : state.each_value_immutable(index_vars.at(d))) {
                            if (d + 1 == dimensions_)
                                logger->emit_rup_proof_line_under_reason(reason,
                                    sum_so_far + 1_i * (result_var != value) + 1_i * (index_vars.at(d) != v) >= 1_i,
                                    ProofLevel::Temporary);
                            else {
                                auto save_sum_so_far = sum_so_far;
                                sum_so_far += 1_i * (index_vars.at(d) != v);
                                rule_out(d + 1);
                                sum_so_far = save_sum_so_far;
                            }
                        }
                        if (! sum_so_far.terms.empty()) {
                            logger->emit_rup_proof_line_under_reason(reason,
                                sum_so_far + 1_i * (result_var != value) >= 1_i,
                                ProofLevel::Temporary);
                        }
                    };
                    rule_out(0);
                }},
                    reason);
            }

            return PropagatorState::Enable;
        },
            {all_array_vars, _index_vars, _result_var}, result_triggers, "NDimensionalElement");
    }

    if (array_has_nonconstants) {
        Triggers equality_triggers;
        equality_triggers.on_change.insert(equality_triggers.on_change.end(), _index_vars.begin(), _index_vars.end());
        equality_triggers.on_change.emplace_back(_result_var);
        propagators.install([array = _array, index_vars = _index_vars, index_starts = _index_starts, result_var = _result_var](
                                const State & state, auto & inference, ProofLogger * const logger) -> PropagatorState {
            // if there's only a single possible array variable left, it can only take values
            // that are present in the result variable
            bool index_is_fully_defined = true;
            vector<size_t> elem;
            DetailedReasonOutline index_reason;
            for (const auto & [p, i] : enumerate(index_vars)) {
                auto v = state.optional_single_value(i);
                if (! v) {
                    index_is_fully_defined = false;
                    break;
                }
                elem.push_back(v->raw_value - index_starts.at(p).raw_value);
                index_reason.push_back(i == *v);
            }

            if (index_is_fully_defined) {
                auto array_var = get_array_var<dimensions_>(elem, *array);
                enforce_equality(logger, result_var, array_var, state, inference, index_reason);
            }

            return PropagatorState::Enable;
        },
            {all_array_vars, _index_vars, _result_var}, equality_triggers, "NDimensionalElement");
    }
}

template <typename EntryType_, unsigned dimensions_>
auto NDimensionalElement<EntryType_, dimensions_>::clone() const -> unique_ptr<Constraint>
{
    return unique_ptr<Constraint>(new NDimensionalElement{_result_var, _index_vars, _index_starts, _array, _bounds_only});
}

namespace gcs
{
    template class NDimensionalElement<IntegerVariableID, 1>;
    template class NDimensionalElement<IntegerVariableID, 2>;
    template class NDimensionalElement<IntegerVariableID, 3>;
    template class NDimensionalElement<Integer, 1>;
    template class NDimensionalElement<Integer, 2>;
    template class NDimensionalElement<Integer, 3>;
}
