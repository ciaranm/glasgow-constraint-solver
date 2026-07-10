#include <gcs/constraints/comparison.hh>
#include <gcs/constraints/element/element.hh>
#include <gcs/constraints/element/hints.hh>
#include <gcs/constraints/equals.hh>
#include <gcs/exception.hh>
#include <gcs/innards/inference_tracker.hh>
#include <gcs/innards/proofs/names_and_ids_tracker.hh>
#include <gcs/innards/proofs/proof_logger.hh>
#include <gcs/innards/proofs/proof_model.hh>
#include <gcs/innards/propagators.hh>
#include <gcs/innards/s_expr.hh>
#include <gcs/innards/state.hh>
#include <gcs/innards/variable_id_utils.hh>
#include <gcs/integer.hh>

#include <gch/small_vector.hpp>

#include <util/enumerate.hh>
#include <util/overloaded.hh>

#include <version>

#if defined(__cpp_lib_print) && defined(__cpp_lib_format)
#include <print>
#else
#include <fmt/ostream.h>
#endif

#include <algorithm>
#include <functional>
#include <memory>
#include <optional>
#include <sstream>
#include <string>
#include <type_traits>
#include <utility>
#include <variant>
#include <vector>

using namespace gcs;
using namespace gcs::innards;

using std::function;
using std::max;
using std::min;
using std::optional;
using std::string;
using std::stringstream;
using std::unique_ptr;
using std::vector;
using std::ranges::adjacent_find;
using std::ranges::sort;

#if defined(__cpp_lib_print) && defined(__cpp_lib_format)
using std::print;
#else
using fmt::print;
#endif

namespace
{
    template <typename T_>
    auto check_array_dimensions(const vector<vector<T_>> & v, size_t expected) -> void;

    template <typename T_>
    auto check_array_dimensions(const vector<T_> & v, size_t expected) -> void
    {
        if (v.size() != expected)
            throw InvalidProblemDefinitionException{"didn't get a regularly sized array for element constraint"};
    }

    template <typename T_>
    auto check_array_dimensions(const vector<vector<T_>> & v, size_t expected) -> void
    {
        if (v.size() != expected)
            throw InvalidProblemDefinitionException{"didn't get a regularly sized array for element constraint"};

        for (const auto & vv : v) {
            check_array_dimensions(vv, v.at(0).size());
        }
    }
}

template <typename EntryType_, unsigned dimensions_>
NDimensionalElement<EntryType_, dimensions_>::NDimensionalElement(IntegerVariableID var, IndexVariables i, IndexStarts s, Array a, bool b) :
    _result_var(var), _index_vars(move(i)), _index_starts(move(s)), _array(move(a)), _bounds_only(b)
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
    auto get_array_var(const auto & indices, const T_ & vec, size_t current_index = 0) -> IntegerVariableID
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

    // Constant-array sibling of get_array_var: fetch the entry's Integer value
    // directly. Only instantiated for an Integer-valued array (EntryType_ ==
    // Integer), where it skips the IntegerVariableID variant construction and the
    // State round-trip that get_array_var + state.* would otherwise pay per leaf.
    template <unsigned dims_remaining_, typename T_>
    auto get_array_value(const auto & indices, const T_ & vec, size_t current_index = 0) -> Integer
    {
        if constexpr (1 == dims_remaining_) {
            return vec.at(indices.at(current_index));
        }
        else if constexpr (0 == dims_remaining_) {
            throw UnexpectedException{"NDimensionalElement element fetching code is broken"};
        }
        else {
            return get_array_value<dims_remaining_ - 1>(indices, vec.at(indices.at(current_index)), current_index + 1);
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
auto NDimensionalElement<EntryType_, dimensions_>::install(
    Propagators & propagators, State & initial_state, ProofModel * const optional_model) && -> void
{
    if (! prepare(propagators, initial_state, optional_model))
        return;

    if (optional_model)
        define_proof_model(*optional_model);

    install_propagators(propagators);
}

template <typename EntryType_, unsigned dimensions_>
auto NDimensionalElement<EntryType_, dimensions_>::prepare(Propagators & propagators, State & initial_state, ProofModel * const optional_model)
    -> bool
{
    // A zero-sized dimension means there is no valid assignment. Record the
    // flag so define_proof_model emits a trivially-false `0 ≥ 1` constraint,
    // and install_propagators installs a contradiction initialiser. Skip
    // the index-range bound definitions for that dimension — they would
    // produce a `[start, start - 1]` empty interval whose labels would
    // misleadingly suggest a normal trim.
    for (const auto & [i, _] : enumerate(_index_vars)) {
        if (0_i == Integer(get_dimension_size<dimensions_>(i, *_array))) {
            _has_empty_dim = true;
            return true;
        }
    }

    for (const auto & [i, var] : enumerate(_index_vars)) {
        auto s = Integer(get_dimension_size<dimensions_>(i, *_array));
        propagators.define_bound(initial_state, optional_model, var, Bound::Lower, _index_starts.at(i));
        propagators.define_bound(initial_state, optional_model, var, Bound::Upper, _index_starts.at(i) + s - 1_i);
    }

    _array_has_nonconstants = any_array_variable_is_nonconstant(initial_state, *_array);
    return true;
}

template <typename EntryType_, unsigned dimensions_>
auto NDimensionalElement<EntryType_, dimensions_>::define_proof_model(ProofModel & model) -> void
{
    if (_has_empty_dim) {
        // No valid assignment: emit a trivially-false constraint so the OPB
        // file remains self-describing. The encoding's recursion over the
        // empty dimension would have produced no constraints at all, which
        // wouldn't capture the unsatisfiability.
        model.add_constraint(WPBSum{} >= 1_i);
        return;
    }

    HalfReifyOnConjunctionOf reif;
    gch::small_vector<size_t, dimensions_> elem;

    function<auto(unsigned)->void> build_implication_constraints = [&](unsigned d) {
        auto s = get_dimension_size<dimensions_>(d, *_array);
        for (size_t x = 0; x != s; ++x) {
            reif.push_back(_index_vars.at(d) == Integer(x) + _index_starts.at(d));
            elem.push_back(x);
            if (elem.size() == dimensions_) {
                // this still works out fine if the variable is actually a constant
                auto array_var = get_array_var<dimensions_>(elem, *_array);
                model.add_constraint(WPBSum{} + (1_i * _result_var) + (-1_i * array_var) == 0_i, reif);
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

// GCC's -O3 scalar-replacement of aggregates picks apart the small-buffer storage
// of ReasonLiterals (gch::small_vector<ProofLiteralOrFlag, 2>) used for the reason
// literals below, then cannot prove one of the resulting temporaries initialised,
// emitting a -Wmaybe-uninitialized false positive (attributed to the first
// install() lambda). The reason locals are all default-constructed before use --
// there is no real uninitialised read -- and clang's analysis does not warn.
#if defined(__GNUC__) && ! defined(__clang__)
#pragma GCC diagnostic push
#pragma GCC diagnostic ignored "-Wmaybe-uninitialized"
#endif
template <typename EntryType_, unsigned dimensions_>
auto NDimensionalElement<EntryType_, dimensions_>::install_propagators(Propagators & propagators) -> void
{
    if (_has_empty_dim) {
        propagators.install_initial_contradiction("NDimensionalElement constraint with no values", JustifyUsingRUP{hints::Element{constraint_id()}});
        return;
    }

    // Specialise on the index variables' concrete type when they are homogeneous,
    // so the hot per-element iteration skips the variant deview; mixed scopes fall
    // back to the general IntegerVariableID path.
    std::visit([&](const auto & index_vars) { install_propagators_impl(propagators, index_vars); }, as_homogeneous(_index_vars));
}

template <typename EntryType_, unsigned dimensions_>
template <typename IndexVec_>
auto NDimensionalElement<EntryType_, dimensions_>::install_propagators_impl(Propagators & propagators, const IndexVec_ & index_vars) -> void
{
    auto array_has_nonconstants = _array_has_nonconstants;

    vector<IntegerVariableID> all_array_vars;
    {
        gch::small_vector<size_t, dimensions_> elem;
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
        // A variable-entried array's variables are needed for the aliasing
        // check below even when they are all root-fixed; the trigger sets
        // still guard on array_has_nonconstants.
        if constexpr (std::is_same_v<EntryType_, IntegerVariableID>)
            collect_array_variables(0);
    }

    // The idempotence claims below must de-alias their own scope: the index
    // propagators deliberately do not watch the variable they write (before
    // claims existed, a self-wake was pure waste), so Propagators::install's
    // trigger-scope downgrade cannot see aliasing that involves the written
    // variable. If any two scope positions share an underlying variable --
    // result also an index (the *_dup_xx tests), an index repeated, result or
    // an index inside the array -- a claiming propagator's snapshot of its
    // read side can be invalidated by its own writes, so no propagator of
    // this constraint claims.
    bool scope_has_aliasing = false;
    {
        vector<unsigned long long> underlying;
        auto add_underlying = [&](const IntegerVariableID & v) {
            overloaded{
                [&](const SimpleIntegerVariableID & sv) { underlying.push_back(sv.index); },                 //
                [&](const ViewOfIntegerVariableID & vv) { underlying.push_back(vv.actual_variable.index); }, //
                [&](const ConstantIntegerVariableID &) {}                                                    //
            }
                .visit(v);
        };
        add_underlying(_result_var);
        for (const auto & v : index_vars)
            add_underlying(v);
        for (const auto & v : all_array_vars)
            add_underlying(v);
        sort(underlying);
        scope_has_aliasing = adjacent_find(underlying) != underlying.end();
    }

    for (unsigned fixed_dim = 0; fixed_dim != index_vars.size(); ++fixed_dim) {
        Triggers index_triggers;
        // The index side is always GAC. bounds_only only weakens the result
        // propagator (range vs union); the index propagator must therefore watch
        // the full domains (on_change) and test against result's whole domain, so
        // that an interior hole in result removes the now-unsupported index value.
        if (array_has_nonconstants)
            index_triggers.on_change.insert(index_triggers.on_change.end(), all_array_vars.begin(), all_array_vars.end());

        index_triggers.on_change.emplace_back(_result_var);

        for (const auto & [idx, var] : enumerate(index_vars))
            if (idx != fixed_dim)
                index_triggers.on_change.emplace_back(var);

        propagators.install(
            constraint_id(),
            [array = _array, index_vars = index_vars, index_starts = _index_starts, result_var = _result_var, fixed_dim = fixed_dim,
                array_has_nonconstants = array_has_nonconstants, scope_has_aliasing = scope_has_aliasing,
                owner = constraint_id()](const State & state, auto & inference, ProofLogger * const logger) -> PropagatorState {
                // for each index variable, update it to only contain values where
                // there's at least one supporting option. result_var's domain is
                // not modified by anything inside the loop body (the only infer_*
                // calls are on index_vars[fixed_dim]), so the looking_for set is
                // constant across iterations and only needs computing once.
                auto looking_for = state.copy_of_values(result_var);
                // explored_vars only feeds the reason; building it is a per-test_val
                // (no-SBO) allocation, so skip it when no reason will be read.
                auto want_reason = inference.want_reasons();

                state.for_each_value_mutable(index_vars.at(fixed_dim), [&](Integer test_val) {
                    gch::small_vector<size_t, dimensions_> elem;
                    vector<IntegerVariableID> explored_vars;
                    if (want_reason)
                        explored_vars.push_back(result_var);
                    auto look_for_support = [&](auto && self, unsigned d) -> bool {
                        // we're iterating over every dimension recursively, except for the one where
                        // we're checking support for the fixed test_val.
                        auto do_it_with = [&](Integer x) {
                            elem.push_back((x - index_starts.at(d)).as_index());
                            if (elem.size() == dimensions_) {
                                if constexpr (std::is_same_v<EntryType_, Integer>) {
                                    // Constant array: test the value directly, skipping the
                                    // IntegerVariableID construction and the State round-trip.
                                    auto value = get_array_value<dimensions_>(elem, *array);
                                    if (looking_for.contains(value))
                                        return true;
                                }
                                else {
                                    auto array_var = get_array_var<dimensions_>(elem, *array);
                                    if (want_reason && array_has_nonconstants)
                                        explored_vars.push_back(array_var);

                                    if (state.domain_intersects_with(array_var, looking_for))
                                        return true;
                                }
                            }
                            else {
                                if (self(self, d + 1))
                                    return true;
                            }
                            elem.pop_back();
                            return false;
                        };

                        if (d == fixed_dim)
                            return do_it_with(test_val);
                        else {
                            if (want_reason)
                                explored_vars.push_back(index_vars.at(d));
                            bool support_found = false;
                            state.for_each_value_immutable(index_vars.at(d), [&](Integer x) {
                                if (do_it_with(x)) {
                                    support_found = true;
                                    return false;
                                }
                                return true;
                            });
                            return support_found;
                        }
                    };

                    if (! look_for_support(look_for_support, 0)) {
                        inference.infer_not_equal(logger, index_vars.at(fixed_dim), test_val,
                            JustifyExplicitly{//
                                [&](const ReasonLiterals & reason) {
                                    // show there's no overlap between array_var and result, for any way the other
                                    // index vars are assigned
                                    gch::small_vector<size_t, dimensions_> elem;
                                    WPBSum sum_so_far;
                                    auto show_no_support = [&](auto && self, unsigned d) -> void {
                                        // again, we're iterating over every dimension recursively, except for the one where
                                        // we're checking support for the fixed test_val.
                                        auto do_it_with = [&](Integer x) {
                                            elem.push_back((x - index_starts.at(d)).as_index());

                                            if (elem.size() == dimensions_) {
                                                auto array_var = get_array_var<dimensions_>(elem, *array);
                                                state.for_each_value_immutable(array_var, [&](Integer v) {
                                                    logger->emit_rup_proof_line_under_reason(reason,
                                                        sum_so_far + 1_i * (index_vars.at(fixed_dim) != test_val) + 1_i * (array_var != v) >= 1_i,
                                                        ProofLevel::Temporary);
                                                });
                                            }
                                            else
                                                self(self, d + 1);

                                            elem.pop_back();
                                        };

                                        if (d == fixed_dim)
                                            return do_it_with(test_val);
                                        else {
                                            state.for_each_value_immutable(index_vars.at(d), [&](Integer x) {
                                                auto save_sum_so_far = sum_so_far;
                                                sum_so_far += 1_i * (index_vars.at(d) != x);
                                                do_it_with(x);
                                                logger->emit_rup_proof_line_under_reason(
                                                    reason, sum_so_far + 1_i * (index_vars.at(fixed_dim) != test_val) >= 1_i, ProofLevel::Temporary);
                                                sum_so_far = save_sum_so_far;
                                            });
                                        }
                                    };

                                    show_no_support(show_no_support, 0);
                                },
                                ThenRUP::Yes, hints::Element{owner}},
                            want_reason ? generic_reason(explored_vars) : Reason{});
                    }
                });

                // Idempotent when the scope has no aliasing: this run writes
                // only index_vars[fixed_dim], and no support test reads it (a
                // value's support depends on result, the other index
                // variables, and the array only), so at return every
                // remaining value's support is intact and a re-run removes
                // nothing. The engine's trigger downgrade cannot stand in for
                // the scope_has_aliasing guard here, because the written
                // variable is deliberately absent from the triggers.
                return scope_has_aliasing ? PropagatorState::Enable : PropagatorState::EnableButIdempotent;
            },
            index_triggers);
    }

    if (_bounds_only) {
        Triggers result_triggers;
        if (array_has_nonconstants)
            result_triggers.on_bounds.insert(result_triggers.on_bounds.end(), all_array_vars.begin(), all_array_vars.end());
        result_triggers.on_change.insert(result_triggers.on_change.end(), index_vars.begin(), index_vars.end());
        result_triggers.on_bounds.emplace_back(_result_var);

        propagators.install(
            constraint_id(),
            [array = _array, index_vars = index_vars, index_starts = _index_starts, result_var = _result_var,
                array_has_nonconstants = array_has_nonconstants,
                owner = constraint_id()](const State & state, auto & inference, ProofLogger * const logger) -> PropagatorState {
                // bounds only, so the result variable has to be in the range
                // (rather than the union) of possible values
                gch::small_vector<size_t, dimensions_> elem;
                optional<Integer> lowest_found, highest_found;
                auto current_bounds = state.bounds(result_var);
                vector<IntegerVariableID> considered_vars;
                auto collect_supported_bounds = [&](auto && self, unsigned d) -> void {
                    state.for_each_value_immutable(index_vars.at(d), [&](Integer x) {
                        if (lowest_found && *lowest_found <= current_bounds.first && highest_found && *highest_found >= current_bounds.second)
                            return false;

                        elem.push_back((x - index_starts.at(d)).as_index());
                        if (elem.size() == dimensions_) {
                            if constexpr (std::is_same_v<EntryType_, Integer>) {
                                auto value = get_array_value<dimensions_>(elem, *array);
                                if (current_bounds.second >= value && current_bounds.first <= value) {
                                    lowest_found = lowest_found ? min(*lowest_found, value) : value;
                                    highest_found = highest_found ? max(*highest_found, value) : value;
                                }
                            }
                            else {
                                auto array_var = get_array_var<dimensions_>(elem, *array);
                                if (array_has_nonconstants)
                                    considered_vars.push_back(array_var);
                                auto array_var_bounds = state.bounds(array_var);
                                if (current_bounds.second >= array_var_bounds.first && current_bounds.first <= array_var_bounds.second) {
                                    lowest_found = lowest_found ? min(*lowest_found, array_var_bounds.first) : array_var_bounds.first;
                                    highest_found = highest_found ? max(*highest_found, array_var_bounds.second) : array_var_bounds.second;
                                }
                            }
                        }
                        else {
                            self(self, d + 1);
                        }
                        elem.pop_back();
                        return true;
                    });
                };
                collect_supported_bounds(collect_supported_bounds, 0);

                auto infer_bound = [&](Integer relevant_bound, bool ge) {
                    auto lit_to_infer = ge ? (result_var >= relevant_bound) : (result_var <= relevant_bound);
                    // Assemble the reason only when one will be read: this bound
                    // reason is generic_reason(index_vars) concatenated with the
                    // captured bound facts, and that concat allocates, so skip it
                    // entirely during ordinary search.
                    Reason reason;
                    if (inference.want_reasons()) {
                        ReasonLiterals extra;
                        for (const auto & var : considered_vars)
                            extra.push_back(ge ? (var >= relevant_bound) : (var <= relevant_bound));
                        extra.push_back(result_var >= current_bounds.first);
                        extra.push_back(result_var <= current_bounds.second);
                        reason = with_extra(generic_reason(vector<IntegerVariableID>{index_vars.begin(), index_vars.end()}), std::move(extra));
                    }
                    inference.infer(logger, lit_to_infer,
                        JustifyExplicitly{//
                            [&](const ReasonLiterals & reason) {
                                // show that it doesn't work for any feasible choice of indices
                                WPBSum sum_so_far;
                                auto rule_out = [&](auto && self, unsigned d) -> void {
                                    state.for_each_value_immutable(index_vars.at(d), [&](Integer v) {
                                        if (d + 1 == dimensions_)
                                            logger->emit_rup_proof_line_under_reason(reason,
                                                sum_so_far + 1_i * lit_to_infer + 1_i * (index_vars.at(d) != v) >= 1_i, ProofLevel::Temporary);
                                        else {
                                            auto save_sum_so_far = sum_so_far;
                                            sum_so_far += 1_i * (index_vars.at(d) != v);
                                            self(self, d + 1);
                                            sum_so_far = save_sum_so_far;
                                        }
                                    });
                                    if (! sum_so_far.terms.empty()) {
                                        logger->emit_rup_proof_line_under_reason(
                                            reason, sum_so_far + 1_i * lit_to_infer >= 1_i, ProofLevel::Temporary);
                                    }
                                };
                                rule_out(rule_out, 0);
                            },
                            ThenRUP::Yes, hints::Element{owner}},
                        reason);
                };

                if (lowest_found && *lowest_found > current_bounds.first)
                    infer_bound(*lowest_found, true);

                if (highest_found && *highest_found < current_bounds.second)
                    infer_bound(*highest_found, false);

                // Deliberately not EnableButIdempotent: this propagator reads
                // and writes result's bounds, and a bound write that snaps
                // past a hole tightens the range the next run filters array
                // entries against, which can exclude the entries that
                // supported the old bounds and so licence a strictly tighter
                // inference on an immediate re-run (result {0,3,6,10} against
                // entries {2,5,9} first infers [2,9], snapping to [3,6], and
                // only a re-run gets >= 5 from the sole surviving entry).
                return PropagatorState::Enable;
            },
            result_triggers);
    }
    else {
        Triggers result_triggers;
        if (array_has_nonconstants)
            result_triggers.on_change.insert(result_triggers.on_change.end(), all_array_vars.begin(), all_array_vars.end());
        result_triggers.on_change.insert(result_triggers.on_change.end(), index_vars.begin(), index_vars.end());

        propagators.install(
            constraint_id(),
            [array = _array, index_vars = index_vars, index_starts = _index_starts, result_var = _result_var,
                array_has_nonconstants = array_has_nonconstants, scope_has_aliasing = scope_has_aliasing,
                owner = constraint_id()](const State & state, auto & inference, ProofLogger * const logger) -> PropagatorState {
                // the result variable has to be in the union of possible values
                gch::small_vector<size_t, dimensions_> elem;
                IntervalSet<Integer> still_to_find_support_for = state.copy_of_values(result_var);
                vector<IntegerVariableID> considered_vars;
                auto collect_supported_values = [&](auto && self, unsigned d) -> void {
                    state.for_each_value_immutable(index_vars.at(d), [&](Integer x) {
                        if (still_to_find_support_for.empty())
                            return false;

                        elem.push_back((x - index_starts.at(d)).as_index());
                        if (elem.size() == dimensions_) {
                            if constexpr (std::is_same_v<EntryType_, Integer>) {
                                still_to_find_support_for.erase(get_array_value<dimensions_>(elem, *array));
                            }
                            else {
                                auto array_var = get_array_var<dimensions_>(elem, *array);
                                if (array_has_nonconstants)
                                    considered_vars.push_back(array_var);
                                state.for_each_value_immutable(array_var, [&](Integer v) { still_to_find_support_for.erase(v); });
                            }
                        }
                        else {
                            self(self, d + 1);
                        }
                        elem.pop_back();
                        return true;
                    });
                };
                collect_supported_values(collect_supported_values, 0);

                for (auto value : still_to_find_support_for.each()) {
                    // index_vars stay a declarative generic_reason, concatenated with
                    // the per-considered-var literals; assembled only when a reason
                    // will be read.
                    Reason reason;
                    if (inference.want_reasons()) {
                        ReasonLiterals extra;
                        for (const auto & var : considered_vars)
                            extra.push_back(var != value);
                        reason = with_extra(generic_reason(vector<IntegerVariableID>{index_vars.begin(), index_vars.end()}), std::move(extra));
                    }
                    inference.infer_not_equal(logger, result_var, value,
                        JustifyExplicitly{//
                            [&](const ReasonLiterals & reason) {
                                // show that it doesn't work for any feasible choice of indices
                                WPBSum sum_so_far;
                                auto rule_out = [&](auto && self, unsigned d) -> void {
                                    state.for_each_value_immutable(index_vars.at(d), [&](Integer v) {
                                        if (d + 1 == dimensions_)
                                            logger->emit_rup_proof_line_under_reason(reason,
                                                sum_so_far + 1_i * (result_var != value) + 1_i * (index_vars.at(d) != v) >= 1_i,
                                                ProofLevel::Temporary);
                                        else {
                                            auto save_sum_so_far = sum_so_far;
                                            sum_so_far += 1_i * (index_vars.at(d) != v);
                                            self(self, d + 1);
                                            sum_so_far = save_sum_so_far;
                                        }
                                    });
                                    if (! sum_so_far.terms.empty()) {
                                        logger->emit_rup_proof_line_under_reason(
                                            reason, sum_so_far + 1_i * (result_var != value) >= 1_i, ProofLevel::Temporary);
                                    }
                                };
                                rule_out(rule_out, 0);
                            },
                            ThenRUP::Yes, hints::Element{owner}},
                        reason);
                }

                // Idempotent when the scope has no aliasing: this run writes
                // only result, whose values play no part in the supported-set
                // computation (that reads the index variables and the array
                // only), so the values that survive are exactly the supported
                // ones and a re-run removes nothing. Value removals are
                // exact, so there is no snapping hazard, unlike the bounds
                // variant above.
                return scope_has_aliasing ? PropagatorState::Enable : PropagatorState::EnableButIdempotent;
            },
            result_triggers);
    }

    if (array_has_nonconstants) {
        Triggers equality_triggers;
        equality_triggers.on_change.insert(equality_triggers.on_change.end(), index_vars.begin(), index_vars.end());
        equality_triggers.on_change.emplace_back(_result_var);
        propagators.install(
            constraint_id(),
            [array = _array, index_vars = index_vars, index_starts = _index_starts, result_var = _result_var, scope_has_aliasing = scope_has_aliasing,
                owner = constraint_id()](const State & state, auto & inference, ProofLogger * const logger) -> PropagatorState {
                // if there's only a single possible array variable left, it can only take values
                // that are present in the result variable
                bool index_is_fully_defined = true;
                gch::small_vector<size_t, dimensions_> elem;
                ReasonLiterals index_reason;
                for (const auto & [p, i] : enumerate(index_vars)) {
                    auto v = state.optional_single_value(i);
                    if (! v) {
                        index_is_fully_defined = false;
                        break;
                    }
                    elem.push_back((*v - index_starts.at(p)).as_index());
                    index_reason.push_back(i == *v);
                }

                if (index_is_fully_defined) {
                    auto array_var = get_array_var<dimensions_>(elem, *array);
                    enforce_equality(logger, result_var, array_var, state, inference, index_reason, owner);
                }

                // Idempotent when the scope has no aliasing: a run that did
                // nothing (index not fully defined) trivially so; otherwise
                // the run writes only result and the selected array variable,
                // which enforce_equality leaves with equal domains -- the
                // holey path prunes both sides' symmetric difference from
                // entry snapshots, the hole-free path intersects bounds
                // exactly (no snapping without holes) -- so a re-run finds
                // nothing left to remove, and its single-value shortcut can
                // only re-infer an equality that already holds (NoChange).
                return scope_has_aliasing ? PropagatorState::Enable : PropagatorState::EnableButIdempotent;
            },
            equality_triggers);
    }
}
#if defined(__GNUC__) && ! defined(__clang__)
#pragma GCC diagnostic pop
#endif

template <typename EntryType_, unsigned dimensions_>
auto NDimensionalElement<EntryType_, dimensions_>::clone() const -> unique_ptr<Constraint>
{
    return unique_ptr<Constraint>(new NDimensionalElement{_result_var, _index_vars, _index_starts, _array, _bounds_only});
}

template <typename EntryType_, unsigned dimensions_>
auto NDimensionalElement<EntryType_, dimensions_>::constraint_type() const -> std::string
{
    return dimensions_ == 1 ? "element" : "element_2d";
}

template <typename EntryType_, unsigned dimensions_>
auto NDimensionalElement<EntryType_, dimensions_>::s_expr(const ProofModel * const model) const -> SExpr
{
    auto & tracker = model->names_and_ids_tracker();

    // cake_pb_cp reads the array as a bare varc list -- position is implicit, so
    // no per-entry index -- and each index as a (variable offset) pair, then the
    // result: "(X0 ... Xn-1) (Y0 off0) ... Z". The offset matches our
    // _index_starts (both subtract it: the chosen entry is Xs[val(Y) - off]).
    auto entry_term = [&](const auto & elem) -> SExpr {
        if constexpr (std::is_same_v<EntryType_, IntegerVariableID>)
            return tracker.s_expr_term_of(elem);
        else
            return SExpr::atom(elem.to_string());
    };

    // Build the array's children: the innermost rows (a vector of EntryType_) in
    // traversal order; in a multi-dimensional array each row is its own sub-list
    // (cake reads element_2d's array as ((row1) (row2) ...)), in 1-D they are flat.
    vector<SExpr> array_children;
    auto build_array = [&](auto & self, const auto & arr) -> void {
        using ArrayType = std::decay_t<decltype(arr)>;
        if constexpr (std::is_same_v<typename ArrayType::value_type, EntryType_>) {
            if (dimensions_ > 1) {
                vector<SExpr> row;
                for (const auto & e : arr)
                    row.push_back(entry_term(e));
                array_children.push_back(SExpr::list(move(row)));
            }
            else {
                for (const auto & e : arr)
                    array_children.push_back(entry_term(e));
            }
        }
        else {
            for (const auto & sub_arr : arr)
                self(self, sub_arr);
        }
    };
    build_array(build_array, *_array);

    vector<SExpr> terms{SExpr::atom(as_string(_constraint_id)), SExpr::atom(constraint_type()), SExpr::list(move(array_children))};

    for (size_t i = 0; i < _index_vars.size(); ++i)
        terms.push_back(SExpr::list({tracker.s_expr_term_of(_index_vars[i]), SExpr::atom(_index_starts[i].to_string())}));

    terms.push_back(tracker.s_expr_term_of(_result_var));

    return SExpr::list(move(terms));
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
