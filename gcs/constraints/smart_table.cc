#include <gcs/constraints/smart_table.hh>
#include <gcs/innards/inference_tracker.hh>
#include <gcs/innards/proofs/proof_logger.hh>
#include <gcs/innards/proofs/proof_model.hh>
#include <gcs/innards/propagators.hh>

#include <algorithm>
#include <map>
#include <set>
#include <sstream>
#include <string>
#include <tuple>
#include <unordered_map>
#include <variant>
#include <vector>

#include <gcs/exception.hh>
#include <util/overloaded.hh>

using std::copy_if;
using std::count;
using std::make_tuple;
using std::make_unique;
using std::map;
using std::move;
using std::optional;
using std::pair;
using std::set;
using std::set_difference;
using std::set_intersection;
using std::sort;
using std::string;
using std::stringstream;
using std::to_string;
using std::tuple;
using std::unique_ptr;
using std::unordered_map;
using std::vector;

using namespace gcs;
using namespace gcs::innards;

SmartTable::SmartTable(vector<IntegerVariableID> v, SmartTuples t) :
    _vars(move(v)),
    _tuples(move(t))
{
}

namespace
{
    // Shorthands
    using VariableDomainMap = unordered_map<IntegerVariableID, vector<Integer>>;
    using BinaryEntryData = tuple<IntegerVariableID, IntegerVariableID, SmartEntryConstraint>;
    using TreeEdges = vector<vector<SmartEntry>>;
    using Forest = vector<TreeEdges>;

    // Annoying workaround access functions to make sure this all works with views
    auto get_for_actual_var(VariableDomainMap & vdom, const IntegerVariableID & v) -> vector<Integer>
    {
        return overloaded{
            [&](ConstantIntegerVariableID) -> vector<Integer> {
                throw UnimplementedException{};
            },
            [&](ViewOfIntegerVariableID v) -> vector<Integer> {
                auto vec = vector<Integer>(vdom[v.actual_variable].size(), 0_i);
                for (unsigned i = 0; i < vec.size(); i++) {
                    vec[i] = (v.negate_first ? -1_i : 1_i) * vdom[v.actual_variable][i] + v.then_add;
                }
                return vec;
            },
            [&](SimpleIntegerVariableID s) -> vector<Integer> {
                vector<Integer> vec = vdom.at(s);
                return vec;
            }}
            .visit(v);
    }

    auto set_for_actual_var(VariableDomainMap & vdom, const IntegerVariableID & v, vector<Integer> & vec) -> void
    {
        overloaded{
            [&](ConstantIntegerVariableID) -> void {
                throw UnimplementedException{};
            },
            [&](ViewOfIntegerVariableID v) -> void {
                auto mod_vec = vector<Integer>(vdom[v.actual_variable].size(), 0_i);
                for (unsigned i = 0; i < vec.size(); i++) {
                    mod_vec[i] = (v.negate_first ? -1_i : 1_i) * (vec[i] - v.then_add);
                }
                vdom.at(v.actual_variable) = move(mod_vec);
            },
            [&](SimpleIntegerVariableID s) -> void {
                vdom.at(s) = move(vec);
            }}
            .visit(v);
    }

    auto deview(IntegerVariableID v) -> IntegerVariableID
    {
        return overloaded{
            [&](SimpleIntegerVariableID & s) -> IntegerVariableID {
                return s;
            },
            [&](ViewOfIntegerVariableID & v) -> IntegerVariableID {
                return v.actual_variable;
            },
            [&](ConstantIntegerVariableID & c) -> IntegerVariableID {
                return c;
            }}
            .visit(v);
    }

    auto log_filtering_inference(ProofLogger * const logger, const ProofFlag & tuple_selector, const Literal & lit,
        const State &, auto &, const ExpandedReason & reason)
    {
        logger->emit_rup_proof_line_under_reason(reason,
            WeightedPseudoBooleanSum{} + 1_i * (! tuple_selector) + 1_i * lit >= 1_i, ProofLevel::Current);
    }

    auto filter_edge(const SmartEntry & edge, VariableDomainMap & supported_by_tree, const ProofFlag & tuple_selector,
        const State & state, auto & inference, const ExpandedReason & reason, ProofLogger * const logger) -> void
    {
        // Currently filter both domains - might be overkill
        // If the tree was in a better form, think this can be optimised to do less redundant filtering.
        overloaded{
            [&](const BinaryEntry & binary_entry) {
                vector<Integer> new_dom_1{};
                vector<Integer> new_dom_2{};

                auto dom_1 = get_for_actual_var(supported_by_tree, binary_entry.var_1);
                auto dom_2 = get_for_actual_var(supported_by_tree, binary_entry.var_2);
                sort(dom_1.begin(), dom_1.end());
                sort(dom_2.begin(), dom_2.end());

                switch (binary_entry.constraint_type) {
                case SmartEntryConstraint::LessThan:
                    copy_if(dom_2.begin(), dom_2.end(), back_inserter(new_dom_2),
                        [&](Integer val) { return val > dom_1[0]; });
                    copy_if(dom_1.begin(), dom_1.end(), back_inserter(new_dom_1),
                        [&](Integer val) { return val < dom_2[dom_2.size() - 1]; });
                    if (logger) {
                        if (new_dom_2.size() < dom_2.size())
                            log_filtering_inference(logger, tuple_selector, deview(binary_entry.var_2) >= (dom_1[0] + 1_i),
                                state, inference, reason);
                        if (new_dom_1.size() < dom_1.size())
                            log_filtering_inference(logger, tuple_selector, deview(binary_entry.var_1) < dom_2[dom_2.size() - 1],
                                state, inference, reason);
                    }
                    break;
                case SmartEntryConstraint::LessThanEqual:
                    copy_if(dom_2.begin(), dom_2.end(), back_inserter(new_dom_2),
                        [&](Integer val) { return val >= dom_1[0]; });
                    copy_if(dom_1.begin(), dom_1.end(), back_inserter(new_dom_1),
                        [&](Integer val) { return val <= dom_2[dom_2.size() - 1]; });
                    if (logger) {
                        if (new_dom_2.size() < dom_2.size())
                            log_filtering_inference(logger, tuple_selector, deview(binary_entry.var_2) >= (dom_1[0]), state, inference, reason);
                        if (new_dom_1.size() < dom_1.size())
                            log_filtering_inference(logger, tuple_selector, deview(binary_entry.var_1) < (dom_2[dom_2.size() - 1] + 1_i), state, inference, reason);
                    }
                    break;
                case SmartEntryConstraint::Equal:
                    set_intersection(dom_1.begin(), dom_1.end(),
                        dom_2.begin(), dom_2.end(),
                        back_inserter(new_dom_1));
                    new_dom_2 = new_dom_1;

                    if (logger) {
                        // This one seems particularly annoying. Is it necessary? - not sure
                        if (new_dom_1.size() < dom_1.size()) {
                            vector<Integer> discarded_dom1;
                            set_difference(dom_1.begin(), dom_1.end(), dom_2.begin(), dom_2.end(),
                                back_inserter(discarded_dom1));
                            for (const auto & val : discarded_dom1) {
                                log_filtering_inference(logger, tuple_selector, deview(binary_entry.var_1) != val, state, inference, reason);
                            }
                        }

                        if (new_dom_2.size() < dom_2.size()) {
                            vector<Integer> discarded_dom2;
                            set_difference(dom_2.begin(), dom_2.end(), dom_1.begin(), dom_1.end(),
                                back_inserter(discarded_dom2));
                            for (const auto & val : discarded_dom2) {
                                log_filtering_inference(logger, tuple_selector, deview(binary_entry.var_2) != val, state, inference, reason);
                            }
                        }
                    }
                    break;
                case SmartEntryConstraint::NotEqual:
                    if (dom_1.size() == 1) {
                        new_dom_1 = dom_1;
                        set_difference(dom_2.begin(), dom_2.end(),
                            dom_1.begin(), dom_1.end(),
                            back_inserter(new_dom_2));
                        if (logger && new_dom_2.size() < dom_2.size()) {
                            log_filtering_inference(logger, tuple_selector, deview(binary_entry.var_2) != (dom_1[0]), state, inference, reason);
                        }
                    }
                    else if (dom_2.size() == 1) {
                        new_dom_2 = dom_2;
                        set_difference(dom_1.begin(), dom_1.end(),
                            dom_2.begin(), dom_2.end(),
                            back_inserter(new_dom_1));
                        if (logger && new_dom_1.size() < dom_1.size()) {
                            log_filtering_inference(logger, tuple_selector, deview(binary_entry.var_1) != (dom_2[0]), state, inference, reason);
                        }
                    }
                    else {
                        new_dom_1 = move(dom_1);
                        new_dom_2 = move(dom_2);
                    }
                    break;
                case SmartEntryConstraint::GreaterThan:
                    copy_if(dom_1.begin(), dom_1.end(), back_inserter(new_dom_1),
                        [&](Integer val) { return val > dom_2[0]; });
                    copy_if(dom_2.begin(), dom_2.end(), back_inserter(new_dom_2),
                        [&](Integer val) { return val < dom_1[dom_1.size() - 1]; });
                    if (logger) {
                        if (new_dom_1.size() < dom_1.size())
                            log_filtering_inference(logger, tuple_selector, deview(binary_entry.var_1) >= (dom_2[0] + 1_i), state, inference, reason);
                        if (new_dom_2.size() < dom_2.size())
                            log_filtering_inference(logger, tuple_selector, deview(binary_entry.var_2) < dom_1[dom_1.size() - 1], state, inference, reason);
                    }
                    break;
                case SmartEntryConstraint::GreaterThanEqual:
                    copy_if(dom_1.begin(), dom_1.end(), back_inserter(new_dom_1),
                        [&](Integer val) { return val >= dom_2[0]; });
                    copy_if(dom_2.begin(), dom_2.end(), back_inserter(new_dom_2),
                        [&](Integer val) { return val <= dom_1[dom_1.size() - 1]; });
                    if (logger) {
                        if (new_dom_1.size() < dom_1.size())
                            log_filtering_inference(logger, tuple_selector, deview(binary_entry.var_1) >= (dom_2[0]), state, inference, reason);
                        if (new_dom_2.size() < dom_2.size())
                            log_filtering_inference(logger, tuple_selector, deview(binary_entry.var_2) < (dom_1[dom_1.size() - 1] + 1_i), state, inference, reason);
                    }
                    break;
                default:
                    throw UnexpectedException{"Unexpected SmartEntry type encountered."};
                }
                set_for_actual_var(supported_by_tree, binary_entry.var_1, new_dom_1);
                set_for_actual_var(supported_by_tree, binary_entry.var_2, new_dom_2);
            },
            [&](const UnarySetEntry & unary_set_entry) {
                vector<Integer> new_dom{};
                auto dom = get_for_actual_var(supported_by_tree, unary_set_entry.var);
                auto set_values = unary_set_entry.values;
                sort(dom.begin(), dom.end());
                sort(set_values.begin(), set_values.end());

                switch (unary_set_entry.constraint_type) {
                case SmartEntryConstraint::In:
                    set_intersection(dom.begin(), dom.end(),
                        set_values.begin(), set_values.end(),
                        back_inserter(new_dom));
                    break;
                case SmartEntryConstraint::NotIn:
                    set_difference(dom.begin(), dom.end(),
                        set_values.begin(), set_values.end(),
                        back_inserter(new_dom));
                    break;
                default:
                    throw UnexpectedException{"Unexpected SmartEntry type encountered."};
                }

                set_for_actual_var(supported_by_tree, unary_set_entry.var, new_dom);
            },
            [&](const UnaryValueEntry & unary_val_entry) {
                vector<Integer> new_dom{};
                auto dom = get_for_actual_var(supported_by_tree, unary_val_entry.var);
                auto value = unary_val_entry.value;
                sort(dom.begin(), dom.end());

                switch (unary_val_entry.constraint_type) {
                case SmartEntryConstraint::LessThan:
                    copy_if(dom.begin(), dom.end(), back_inserter(new_dom),
                        [&](Integer dom_val) { return dom_val < value; });
                    break;
                case SmartEntryConstraint::LessThanEqual:
                    copy_if(dom.begin(), dom.end(), back_inserter(new_dom),
                        [&](Integer dom_val) { return dom_val <= value; });
                    break;
                case SmartEntryConstraint::Equal:
                    copy_if(dom.begin(), dom.end(), back_inserter(new_dom),
                        [&](Integer dom_val) { return dom_val == value; });
                    break;
                case SmartEntryConstraint::NotEqual:
                    copy_if(dom.begin(), dom.end(), back_inserter(new_dom),
                        [&](Integer dom_val) { return dom_val != value; });
                    break;
                case SmartEntryConstraint::GreaterThan:
                    copy_if(dom.begin(), dom.end(), back_inserter(new_dom),
                        [&](Integer dom_val) { return dom_val > value; });
                    break;
                case SmartEntryConstraint::GreaterThanEqual:
                    copy_if(dom.begin(), dom.end(), back_inserter(new_dom),
                        [&](Integer dom_val) { return dom_val >= value; });
                    break;
                default:
                    throw UnexpectedException{"Unexpected SmartEntry type encountered."};
                }

                set_for_actual_var(supported_by_tree, unary_val_entry.var, new_dom);
            }}
            .visit(edge);
    }

    [[nodiscard]] auto filter_and_check_valid(const TreeEdges & tree, VariableDomainMap & supported_by_tree,
        const ProofFlag & tuple_selector, const State & state, auto & inference,
        const ExpandedReason & reason, ProofLogger * const logger) -> bool
    {
        for (int l = tree.size() - 1; l >= 0; --l) {
            for (const auto & edge : tree[l]) {

                filter_edge(edge, supported_by_tree, tuple_selector, state, inference, reason, logger);

                bool domain_became_empty = false;
                overloaded{
                    [&](const BinaryEntry & binary_entry) {
                        if (get_for_actual_var(supported_by_tree, binary_entry.var_1).empty()) domain_became_empty = true;
                        if (get_for_actual_var(supported_by_tree, binary_entry.var_2).empty()) domain_became_empty = true;
                    },
                    [&](const UnarySetEntry & unary_set_entry) {
                        if (get_for_actual_var(supported_by_tree, unary_set_entry.var).empty()) domain_became_empty = true;
                    },
                    [&](const UnaryValueEntry & unary_val_entry) {
                        if (get_for_actual_var(supported_by_tree, unary_val_entry.var).empty()) domain_became_empty = true;
                    }}
                    .visit(edge);

                if (domain_became_empty) {
                    return false;
                }
            }
        }
        return true;
    }

    auto remove_supported(VariableDomainMap & unsupported, IntegerVariableID var, vector<Integer> & to_remove) -> void
    {
        vector<Integer> new_unsupported{};
        auto unsupported_set = set(unsupported[var].begin(), unsupported[var].end());
        auto to_remove_set = set(to_remove.begin(), to_remove.end());
        set_difference(unsupported_set.begin(), unsupported_set.end(),
            to_remove_set.begin(), to_remove_set.end(),
            back_inserter(new_unsupported));

        unsupported[var] = new_unsupported;
    }

    auto filter_again_and_remove_supported(const TreeEdges & tree, VariableDomainMap & supported_by_tree,
        VariableDomainMap & unsupported, const ProofFlag & tuple_selector, const State & state,
        auto & inference, const ExpandedReason & reason, ProofLogger * const logger) -> void
    {
        for (int l = tree.size() - 1; l >= 0; --l) {
            for (const auto & edge : tree[l]) {
                filter_edge(edge, supported_by_tree, tuple_selector, state, inference, reason, logger);

                // Collect supported vals for this tree
                overloaded{
                    [&](const BinaryEntry & binary_entry) {
                        auto supported_var_1 = get_for_actual_var(supported_by_tree, binary_entry.var_1);
                        auto supported_var_2 = get_for_actual_var(supported_by_tree, binary_entry.var_2);
                        remove_supported(unsupported, binary_entry.var_1, supported_var_1);
                        remove_supported(unsupported, binary_entry.var_2, supported_var_2);
                    },
                    [&](const UnarySetEntry & unary_set_entry) {
                        auto supported = get_for_actual_var(supported_by_tree, unary_set_entry.var);
                        remove_supported(unsupported, unary_set_entry.var, supported);
                    },
                    [&](const UnaryValueEntry & unary_val_entry) {
                        auto supported = get_for_actual_var(supported_by_tree, unary_val_entry.var);
                        remove_supported(unsupported, unary_val_entry.var, supported);
                    }}
                    .visit(edge);
            }
        }
    }

    auto get_unrestricted(const vector<IntegerVariableID> & vars, const vector<SmartEntry> & tuple) -> vector<IntegerVariableID>
    {
        vector<IntegerVariableID> vars_in_tuple;
        vector<IntegerVariableID> unrestricted;
        for (const auto & entry : tuple) {
            overloaded{
                [&](const BinaryEntry & binary_entry) {
                    vars_in_tuple.emplace_back(binary_entry.var_1);
                    vars_in_tuple.emplace_back(binary_entry.var_2);
                },
                [&](const UnarySetEntry & unary_set_entry) {
                    vars_in_tuple.emplace_back(unary_set_entry.var);
                },
                [&](const UnaryValueEntry & unary_val_entry) {
                    vars_in_tuple.emplace_back(unary_val_entry.var);
                }}
                .visit(entry);
        }

        auto vars_set = set(vars.begin(), vars.end());
        auto vars_in_tuple_set = set(vars_in_tuple.begin(), vars_in_tuple.end());

        set_difference(vars_set.begin(), vars_set.end(),
            vars_in_tuple_set.begin(), vars_in_tuple_set.end(),
            back_inserter(unrestricted));
        return unrestricted;
    }

    auto propagate_using_smart_str(const vector<IntegerVariableID> & selectors, const vector<IntegerVariableID> & vars,
        const SmartTuples & tuples, const vector<Forest> & forests, const State & state, auto & inference, const ExpandedReason & reason,
        vector<ProofFlag> pb_selectors, ProofLogger * const logger) -> void
    {
        VariableDomainMap unsupported{};
        // Initialise unsupported values to everything in each variable's current domain.
        for (const auto & var : vars) {
            for (auto value : state.each_value(var)) {
                unsupported[var].emplace_back(value);
            }
        }

        // Check that feasible tuples are still feasible
        // and also have them remove values from "unsupported" that they support
        for (unsigned int tuple_idx = 0; tuple_idx < tuples.size(); ++tuple_idx) {
            // Skip infeasible tuple
            if (state.optional_single_value(selectors[tuple_idx]) == 0_i) {
                continue;
            }

            for (const auto & tree : forests[tuple_idx]) {
                // Initialise supported by tree to current variable domains
                VariableDomainMap supported_by_tree{};

                for (const auto & var : vars)
                    for (auto value : state.each_value(var))
                        supported_by_tree[var].emplace_back(value);

                // First pass of filtering supported_by_tree and check of validity
                if (! filter_and_check_valid(tree, supported_by_tree, pb_selectors[tuple_idx], state, inference, reason, logger)) {
                    // Not feasible
                    inference.infer_equal(logger, selectors[tuple_idx], 0_i, NoJustificationNeeded{}, NoReason{});
                    break;
                }

                filter_again_and_remove_supported(tree, supported_by_tree, unsupported, pb_selectors[tuple_idx],
                    state, inference, reason, logger);
            }

            if (state.optional_single_value(selectors[tuple_idx]) != 0_i) {
                const auto unrestricted = get_unrestricted(vars, tuples[tuple_idx]);
                for (const auto & var : unrestricted) {
                    unsupported[var] = vector<Integer>{};
                }
            }
        }

        bool some_tuple_still_feasible = false;
        for (unsigned int tuple_idx = 0; tuple_idx < tuples.size(); ++tuple_idx) {
            if (state.optional_single_value(selectors[tuple_idx]) != 0_i) {
                some_tuple_still_feasible = true;
                break;
            }
        }

        for (const auto & var : vars) {
            for (const auto & value : unsupported[var]) {
                auto justf = [&tuples, &pb_selectors, logger, var, value](const ExpandedReason & reason) -> void {
                    for (unsigned int tuple_idx = 0; tuple_idx < tuples.size(); ++tuple_idx) {
                        logger->emit_rup_proof_line_under_reason(reason,
                            WeightedPseudoBooleanSum{} + 1_i * (var != value) + 1_i * (! pb_selectors[tuple_idx]) >= 1_i,
                            ProofLevel::Current);
                    }
                };
                inference.infer_not_equal(logger, var, value, JustifyExplicitly{justf}, reason);
            }
        }

        if (! some_tuple_still_feasible)
            inference.contradiction(logger, JustifyUsingRUP{}, reason);
    }

    auto build_tree(const IntegerVariableID & root, int current_level, vector<vector<SmartEntry>> & entry_tree,
        unordered_map<IntegerVariableID, bool> & node_visited,
        const unordered_map<IntegerVariableID, vector<SmartEntry>> & adjacent_edges) -> void
    {
        node_visited[deview(root)] = true;

        // Simple recursive traverse
        // Note: Perhaps we should build the tree in a "smarter" form e.g. make sure var_1 is always the node
        //       closer to the root.
        for (const auto & edge : adjacent_edges.at(deview(root))) {
            overloaded{
                [&](BinaryEntry binary_entry) {
                    if (! node_visited[deview(binary_entry.var_1)]) {
                        entry_tree[current_level].emplace_back(edge);
                        entry_tree.emplace_back();

                        build_tree(binary_entry.var_1, current_level + 1, entry_tree, node_visited, adjacent_edges);
                    }
                    else if (! node_visited[deview(binary_entry.var_2)]) {
                        entry_tree[current_level].emplace_back(edge);
                        entry_tree.emplace_back();
                        build_tree(binary_entry.var_2, current_level + 1, entry_tree, node_visited, adjacent_edges);
                    }
                },
                [&](const UnarySetEntry &) {
                    entry_tree[current_level].emplace_back(edge);
                },
                [&](const UnaryValueEntry &) {
                    entry_tree[current_level].emplace_back(edge);
                }}
                .visit(edge);
        }
    }

    [[nodiscard]] auto build_forests(SmartTuples & tuples) -> vector<Forest>
    {
        vector<Forest> forests{};
        for (const auto & current_tuple : tuples) {
            unordered_map<IntegerVariableID, bool> node_visited;
            unordered_map<IntegerVariableID, vector<SmartEntry>> adjacent_edges;

            // Get all the vars in the tuple and record adjacencies
            for (const auto & entry : current_tuple) {
                overloaded{
                    [&](const BinaryEntry & binary_entry) {
                        node_visited[deview(binary_entry.var_1)] = false;
                        node_visited[deview(binary_entry.var_2)] = false;
                        adjacent_edges[deview(binary_entry.var_1)].emplace_back(binary_entry);
                        adjacent_edges[deview(binary_entry.var_2)].emplace_back(binary_entry);
                    },
                    [&](const UnaryValueEntry & unary_val_entry) {
                        node_visited[deview(unary_val_entry.var)] = false;
                        adjacent_edges[deview(unary_val_entry.var)].emplace_back(unary_val_entry);
                    },
                    [&](const UnarySetEntry & unary_set_entry) {
                        node_visited[deview(unary_set_entry.var)] = false;
                        adjacent_edges[deview(unary_set_entry.var)].emplace_back(unary_set_entry);
                    }}
                    .visit(entry);
            }

            Forest forest{};
            for (auto & var_pair : node_visited) {
                auto & var = var_pair.first;
                auto & visited = var_pair.second;
                if (visited) continue;
                vector<vector<SmartEntry>> entry_tree;
                entry_tree.emplace_back();
                // Recursively build the tree starting from this node
                build_tree(var, 0, entry_tree, node_visited, adjacent_edges);
                forest.emplace_back(entry_tree);
            }

            forests.emplace_back(forest);
        }
        return forests;
    }

    // For PB model
    [[nodiscard]] auto make_binary_entry_flag(State &, ProofModel & model, const IntegerVariableID & var_1, const IntegerVariableID & var_2, const SmartEntryConstraint & c) -> ProofFlag
    {
        switch (c) {
        case SmartEntryConstraint::Equal: {
            // f => var1 == var2
            auto flag = model.create_proof_flag("bin_eq");
            model.add_constraint(WeightedPseudoBooleanSum{} + 1_i * var_1 + -1_i * var_2 == 0_i,
                HalfReifyOnConjunctionOf{{flag}});

            // !f => var1 != var2
            auto flag_lt = model.create_proof_flag("lt");
            auto flag_gt = model.create_proof_flag("gt");
            model.add_constraint(WeightedPseudoBooleanSum{} + 1_i * var_1 + -1_i * var_2 >= 1_i,
                HalfReifyOnConjunctionOf{{flag_gt}});
            model.add_constraint(WeightedPseudoBooleanSum{} + 1_i * var_2 + -1_i * var_1 >= 0_i,
                HalfReifyOnConjunctionOf{{! flag_gt}});
            model.add_constraint(WeightedPseudoBooleanSum{} + 1_i * var_2 + -1_i * var_1 >= 1_i,
                HalfReifyOnConjunctionOf{{flag_lt}});
            model.add_constraint(WeightedPseudoBooleanSum{} + 1_i * var_1 + -1_i * var_2 >= 0_i,
                HalfReifyOnConjunctionOf{{! flag_lt}});
            model.add_constraint(WeightedPseudoBooleanSum{} + 1_i * flag_lt + 1_i * flag_gt >= 1_i,
                HalfReifyOnConjunctionOf{{! flag}});
            return flag;
        }

        case SmartEntryConstraint::GreaterThan: {
            auto flag = model.create_proof_flag("bin_gt");
            model.add_constraint(WeightedPseudoBooleanSum{} + 1_i * var_1 + -1_i * var_2 >= 1_i,
                HalfReifyOnConjunctionOf{{flag}});
            model.add_constraint(WeightedPseudoBooleanSum{} + 1_i * var_2 + -1_i * var_1 >= 0_i,
                HalfReifyOnConjunctionOf{{! flag}});
            return flag;
        }

        case SmartEntryConstraint::LessThan: {
            auto flag = model.create_proof_flag("bin_lt");
            model.add_constraint(WeightedPseudoBooleanSum{} + 1_i * var_2 + -1_i * var_1 >= 1_i,
                HalfReifyOnConjunctionOf{{flag}});
            model.add_constraint(WeightedPseudoBooleanSum{} + 1_i * var_1 + -1_i * var_2 >= 0_i,
                HalfReifyOnConjunctionOf{{! flag}});
            return flag;
        }

        case SmartEntryConstraint::LessThanEqual: {
            auto flag = model.create_proof_flag("bin_le");
            model.add_constraint(WeightedPseudoBooleanSum{} + 1_i * var_2 + -1_i * var_1 >= 0_i,
                HalfReifyOnConjunctionOf{{flag}});
            model.add_constraint(WeightedPseudoBooleanSum{} + 1_i * var_1 + -1_i * var_2 >= 1_i,
                HalfReifyOnConjunctionOf{{! flag}});
            return flag;
        }

        case SmartEntryConstraint::NotEqual: {
            // !f => var1 == var2
            auto flag = model.create_proof_flag("bin_eq");
            model.add_constraint(WeightedPseudoBooleanSum{} + 1_i * var_1 + -1_i * var_2 == 0_i,
                HalfReifyOnConjunctionOf{{! flag}});

            // f => var1 != var2
            auto flag_lt = model.create_proof_flag("lt");
            auto flag_gt = model.create_proof_flag("gt");

            // Means we need f => fgt or flt
            model.add_constraint(WeightedPseudoBooleanSum{} + 1_i * flag_lt + 1_i * flag_gt >= 1_i,
                HalfReifyOnConjunctionOf{{flag}});

            // And then fgt <==> var1 > var2
            model.add_constraint(WeightedPseudoBooleanSum{} + 1_i * var_1 + -1_i * var_2 >= 1_i,
                HalfReifyOnConjunctionOf{{flag_gt}});
            model.add_constraint(WeightedPseudoBooleanSum{} + 1_i * var_2 + -1_i * var_1 >= 0_i,
                HalfReifyOnConjunctionOf{{! flag_gt}});

            // flt <==> var1 < var2
            model.add_constraint(WeightedPseudoBooleanSum{} + 1_i * var_2 + -1_i * var_1 >= 1_i,
                HalfReifyOnConjunctionOf{{flag_lt}});
            model.add_constraint(WeightedPseudoBooleanSum{} + 1_i * var_1 + -1_i * var_2 >= 0_i,
                HalfReifyOnConjunctionOf{{! flag_lt}});

            return flag;
        }

        case SmartEntryConstraint::GreaterThanEqual: {
            auto flag = model.create_proof_flag("bin_ge");
            model.add_constraint(WeightedPseudoBooleanSum{} + 1_i * var_1 + -1_i * var_2 >= 0_i,
                HalfReifyOnConjunctionOf{{flag}});
            model.add_constraint(WeightedPseudoBooleanSum{} + 1_i * var_2 + -1_i * var_1 >= 1_i,
                HalfReifyOnConjunctionOf{{! flag}});
            return flag;
        }

        case SmartEntryConstraint::NotIn:
        case SmartEntryConstraint::In:
            throw UnexpectedException{"Unexpected SmartEntry type encountered while creating PB model."};
        }
        throw NonExhaustiveSwitch{};
    }

    auto literal_from_unary_entry(UnaryValueEntry & unary_entry) -> Literal
    {
        auto var = unary_entry.var;
        auto value = unary_entry.value;
        switch (unary_entry.constraint_type) {
        case SmartEntryConstraint::LessThan:
            return var < value;
        case SmartEntryConstraint::LessThanEqual:
            return var < value + 1_i;
        case SmartEntryConstraint::Equal:
            return var == value;
        case SmartEntryConstraint::NotEqual:
            return var != value;
        case SmartEntryConstraint::GreaterThan:
            return var >= value + 1_i;
        case SmartEntryConstraint::GreaterThanEqual:
            return var >= value;
        case SmartEntryConstraint::In:
        case SmartEntryConstraint::NotIn:
            throw UnexpectedException{"Unexpected SmartEntry type encountered while creating PB model."};
        }
        throw NonExhaustiveSwitch{};
    }
}

auto provable_entry_member(IntegerVariableID v) -> bool
{
    return overloaded{
        [&](ViewOfIntegerVariableID & v) -> bool {
            return ! v.negate_first && v.then_add >= 0_i;
        },
        [&](ConstantIntegerVariableID) -> bool {
            return false;
        },
        [&](SimpleIntegerVariableID) -> bool {
            return true;
        }}
        .visit(v);
}

auto consolidate_unary_entries(State & state, vector<SmartEntry> tuple) -> vector<SmartEntry>
{
    // TODO:
    //  Using an IntervalSet data structure we could do this in a much better way, but this
    //  will do for now
    map<IntegerVariableID, vector<SmartEntry>> unary_entries{};
    vector<SmartEntry> new_tuple{};
    for (const auto & entry : tuple) {
        overloaded{
            [&](BinaryEntry binary_entry) {
                new_tuple.emplace_back(binary_entry);
            },
            [&](UnaryValueEntry value_entry) {
                auto & entries = unary_entries[value_entry.var];
                entries.emplace_back(value_entry);
            },
            [&](UnarySetEntry set_entry) {
                auto & entries = unary_entries[set_entry.var];
                entries.emplace_back(set_entry);
            }}
            .visit(entry);
    }

    for (auto & var_and_entries : unary_entries) {
        const auto & var = var_and_entries.first;
        const auto & entries = var_and_entries.second;
        vector<Integer> allowed_vals{};

        for (auto v : state.each_value(var)) {
            bool val_allowed = true;
            for (auto & entry : entries) {
                overloaded{
                    [&](BinaryEntry) {
                        throw UnexpectedException{"Shouldn't have a binary entry here."};
                    },
                    [&](UnaryValueEntry value_entry) {
                        switch (value_entry.constraint_type) {
                        case SmartEntryConstraint::LessThan:
                            val_allowed = val_allowed && v < value_entry.value;
                            break;
                        case SmartEntryConstraint::LessThanEqual:
                            val_allowed = val_allowed && v <= value_entry.value;
                            break;
                        case SmartEntryConstraint::Equal:
                            val_allowed = val_allowed && v == value_entry.value;
                            break;
                        case SmartEntryConstraint::NotEqual:
                            val_allowed = val_allowed && v != value_entry.value;
                            break;
                        case SmartEntryConstraint::GreaterThan:
                            val_allowed = val_allowed && v > value_entry.value;
                            break;
                        case SmartEntryConstraint::GreaterThanEqual:
                            val_allowed = val_allowed && v >= value_entry.value;
                            break;
                        case SmartEntryConstraint::In:
                        case SmartEntryConstraint::NotIn:
                            throw UnexpectedException{"Unexpected SmartEntry type encountered."};
                        }
                    },
                    [&](UnarySetEntry set_entry) {
                        switch (set_entry.constraint_type) {
                        case SmartEntryConstraint::In:
                            val_allowed = val_allowed && std::count(set_entry.values.begin(), set_entry.values.end(), v);
                            break;
                        case SmartEntryConstraint::NotIn:
                            val_allowed = val_allowed && ! std::count(set_entry.values.begin(), set_entry.values.end(), v);
                            break;
                        case SmartEntryConstraint::LessThan:
                        case SmartEntryConstraint::LessThanEqual:
                        case SmartEntryConstraint::Equal:
                        case SmartEntryConstraint::NotEqual:
                        case SmartEntryConstraint::GreaterThan:
                        case SmartEntryConstraint::GreaterThanEqual:
                            throw UnexpectedException{"Unexpected SmartEntry type encountered."};
                        }
                    }}
                    .visit(entry);
            }
            if (val_allowed) {
                allowed_vals.emplace_back(v);
            }
        }

        auto new_entry_for_var = SmartTable::in_set(var, allowed_vals);
        new_tuple.emplace_back(new_entry_for_var);
    }
    return new_tuple;
}

auto SmartTable::clone() const -> unique_ptr<Constraint>
{
    return make_unique<SmartTable>(_vars, _tuples);
}

auto SmartTable::install(Propagators & propagators, State & initial_state, ProofModel * const optional_model) && -> void
{
    vector<IntegerVariableID> selectors;
    vector<ProofFlag> pb_selectors;

    for (unsigned int i = 0; i < _tuples.size(); ++i) {
        selectors.emplace_back(initial_state.allocate_integer_variable_with_state(0_i, 1_i));
    }

    if (optional_model) {
        for (unsigned int i = 0; i < _tuples.size(); ++i) {
            pb_selectors.emplace_back(optional_model->create_proof_flag("t" + to_string(i)));
        }
        WeightedPseudoBooleanSum sum_pb_selectors{};

        for (const auto & s : pb_selectors)
            sum_pb_selectors += 1_i * s;

        optional_model->add_constraint(sum_pb_selectors >= 1_i);

        // Would need a hash function for unordered map, but this shouldn't be too slow
        map<BinaryEntryData, ProofFlag> smart_entry_flags;

        for (unsigned int tuple_idx = 0; tuple_idx < _tuples.size(); ++tuple_idx) {
            WeightedPseudoBooleanSum entry_flags_sum{};
            WeightedPseudoBooleanSum entry_flags_neg_sum{};
            for (const auto & entry : consolidate_unary_entries(initial_state, _tuples[tuple_idx])) {
                overloaded{
                    [&](BinaryEntry binary_entry) {
                        //                        if(!provable_entry_member(binary_entry.var_1) || !provable_entry_member(binary_entry.var_2)) {
                        //                            throw UnimplementedException{"Can only proof log smart table binary entries of form <var> <op> <var> + b where b >= 0."};
                        //                        }
                        auto binary_entry_data = make_tuple(binary_entry.var_1, binary_entry.var_2, binary_entry.constraint_type);
                        if (! smart_entry_flags.contains(binary_entry_data))
                            smart_entry_flags[binary_entry_data] = make_binary_entry_flag(initial_state, *optional_model,
                                binary_entry.var_1, binary_entry.var_2, binary_entry.constraint_type);

                        entry_flags_sum += 1_i * smart_entry_flags[binary_entry_data];
                        entry_flags_neg_sum += -1_i * smart_entry_flags[binary_entry_data];
                    },
                    [&](const UnarySetEntry & unary_set_entry) {
                        auto var = unary_set_entry.var;
                        auto flag = unary_set_entry.constraint_type == SmartEntryConstraint::In ? optional_model->create_proof_flag("inset") : optional_model->create_proof_flag("notinset");

                        // InSet {<empty>} is the same as False
                        if (unary_set_entry.values.empty() && unary_set_entry.constraint_type == SmartEntryConstraint::In) {
                            optional_model->add_constraint(WeightedPseudoBooleanSum{} + 1_i * ! flag >= 1_i);
                            entry_flags_sum += 1_i * flag;
                            entry_flags_neg_sum += -1_i * flag;
                            return;
                        }
                        WeightedPseudoBooleanSum set_value_sum{};
                        WeightedPseudoBooleanSum neg_set_value_sum{};
                        for (auto val : initial_state.each_value(var)) {
                            if (! count(unary_set_entry.values.begin(), unary_set_entry.values.end(), val))
                                set_value_sum += 1_i * (var != val);
                        }

                        for (const auto & val : unary_set_entry.values)
                            neg_set_value_sum += 1_i * (var != val);

                        auto set_rhs = Integer{static_cast<long long>(set_value_sum.terms.size())};
                        auto neg_set_rhs = Integer{static_cast<long long>(neg_set_value_sum.terms.size())};
                        optional_model->add_constraint(move(set_value_sum) >= set_rhs,
                            HalfReifyOnConjunctionOf{{unary_set_entry.constraint_type == SmartEntryConstraint::In ? flag : ! flag}});
                        optional_model->add_constraint(move(neg_set_value_sum) >= neg_set_rhs,
                            HalfReifyOnConjunctionOf{{unary_set_entry.constraint_type == SmartEntryConstraint::In ? ! flag : flag}});

                        entry_flags_sum += 1_i * flag;
                        entry_flags_neg_sum += -1_i * flag;
                    },
                    [&](UnaryValueEntry unary_value_entry) {
                        Literal l = literal_from_unary_entry(unary_value_entry);
                        entry_flags_sum += 1_i * l;
                        entry_flags_neg_sum += -1_i * l;
                    }}
                    .visit(entry);
            }
            auto tuple_len = Integer{static_cast<long long>(entry_flags_sum.terms.size())};
            optional_model->add_constraint(move(entry_flags_sum) >= tuple_len,
                HalfReifyOnConjunctionOf{{pb_selectors[tuple_idx]}});
            optional_model->add_constraint(move(entry_flags_neg_sum) >= -tuple_len + 1_i,
                HalfReifyOnConjunctionOf{{! pb_selectors[tuple_idx]}});
        }
    }

    // Trigger when any var changes? Is this over-kill?
    Triggers triggers;
    triggers.on_change = {_vars.begin(), _vars.end()};

    vector<Forest> forests = build_forests(_tuples);

    propagators.install(
        [selectors, vars = _vars, tuples = move(_tuples), forests = move(forests), pb_selectors = move(pb_selectors)](
            const State & state, auto & inference, ProofLogger * const logger) -> PropagatorState {
            auto reason = inference.expand(AllVariablesExactValues{});
            propagate_using_smart_str(selectors, vars, tuples, forests, state, inference, reason, pb_selectors, logger);
            return PropagatorState::Enable;
        },
        {_vars},
        triggers,
        "smart table");
}
