#include <gcs/constraints/smart_table.hh>
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

    auto log_filtering_inference(const ProofFlag & tuple_selector, const Literal & lit, State & state)
    {
        auto inference = state.infer(TrueLiteral{}, JustifyExplicitly{[&](Proof & proof) -> void {
            WeightedPseudoBooleanSum terms;
            proof.emit_rup_proof_line_under_trail(state, WeightedPseudoBooleanSum{} + 1_i * (! tuple_selector) + 1_i * lit >= 1_i, ProofLevel::Current);
        }});

        if (inference != Inference::NoChange) {
            throw UnexpectedException{"Failed to infer TrueLiteral."};
        }
    }

    auto filter_edge(const SmartEntry & edge, VariableDomainMap & supported_by_tree, const ProofFlag & tuple_selector, State & state) -> void
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
                    if (state.maybe_proof()) {
                        if (new_dom_2.size() < dom_2.size())
                            log_filtering_inference(tuple_selector, deview(binary_entry.var_2) >= (dom_1[0] + 1_i), state);
                        if (new_dom_1.size() < dom_1.size())
                            log_filtering_inference(tuple_selector, deview(binary_entry.var_1) < dom_2[dom_2.size() - 1], state);
                    }
                    break;
                case SmartEntryConstraint::LessThanEqual:
                    copy_if(dom_2.begin(), dom_2.end(), back_inserter(new_dom_2),
                        [&](Integer val) { return val >= dom_1[0]; });
                    copy_if(dom_1.begin(), dom_1.end(), back_inserter(new_dom_1),
                        [&](Integer val) { return val <= dom_2[dom_2.size() - 1]; });
                    if (state.maybe_proof()) {
                        if (new_dom_2.size() < dom_2.size())
                            log_filtering_inference(tuple_selector, deview(binary_entry.var_2) >= (dom_1[0]), state);
                        if (new_dom_1.size() < dom_1.size())
                            log_filtering_inference(tuple_selector, deview(binary_entry.var_1) < (dom_2[dom_2.size() - 1] + 1_i), state);
                    }
                    break;
                case SmartEntryConstraint::Equal:
                    set_intersection(dom_1.begin(), dom_1.end(),
                        dom_2.begin(), dom_2.end(),
                        back_inserter(new_dom_1));
                    new_dom_2 = new_dom_1;

                    if (state.maybe_proof()) {
                        // This one seems particularly annoying. Is it necessary? - not sure
                        if (new_dom_1.size() < dom_1.size()) {
                            vector<Integer> discarded_dom1;
                            set_difference(dom_1.begin(), dom_1.end(), dom_2.begin(), dom_2.end(),
                                back_inserter(discarded_dom1));
                            for (const auto & val : discarded_dom1) {
                                log_filtering_inference(tuple_selector, deview(binary_entry.var_1) != val, state);
                            }
                        }

                        if (new_dom_2.size() < dom_2.size()) {
                            vector<Integer> discarded_dom2;
                            set_difference(dom_2.begin(), dom_2.end(), dom_1.begin(), dom_1.end(),
                                back_inserter(discarded_dom2));
                            for (const auto & val : discarded_dom2) {
                                log_filtering_inference(tuple_selector, deview(binary_entry.var_2) != val, state);
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
                        if (state.maybe_proof() && new_dom_2.size() > dom_2.size()) {
                            log_filtering_inference(tuple_selector, deview(binary_entry.var_2) != (dom_1[0]), state);
                        }
                    }
                    else if (dom_2.size() == 1) {
                        new_dom_2 = dom_2;
                        set_difference(dom_1.begin(), dom_1.end(),
                            dom_2.begin(), dom_2.end(),
                            back_inserter(new_dom_1));
                        if (state.maybe_proof() && new_dom_1.size() > dom_1.size()) {
                            log_filtering_inference(tuple_selector, deview(binary_entry.var_1) != (dom_2[0]), state);
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
                    if (state.maybe_proof()) {
                        if (new_dom_1.size() < dom_1.size())
                            log_filtering_inference(tuple_selector, deview(binary_entry.var_1) >= (dom_2[0] + 1_i), state);
                        if (new_dom_2.size() < dom_2.size())
                            log_filtering_inference(tuple_selector, deview(binary_entry.var_2) < dom_1[dom_1.size() - 1], state);
                    }
                    break;
                case SmartEntryConstraint::GreaterThanEqual:
                    copy_if(dom_1.begin(), dom_1.end(), back_inserter(new_dom_1),
                        [&](Integer val) { return val >= dom_2[0]; });
                    copy_if(dom_2.begin(), dom_2.end(), back_inserter(new_dom_2),
                        [&](Integer val) { return val <= dom_1[dom_1.size() - 1]; });
                    if (state.maybe_proof()) {
                        if (new_dom_1.size() < dom_1.size())
                            log_filtering_inference(tuple_selector, deview(binary_entry.var_1) >= (dom_2[0]), state);
                        if (new_dom_2.size() < dom_2.size())
                            log_filtering_inference(tuple_selector, deview(binary_entry.var_2) < (dom_1[dom_1.size() - 1] + 1_i), state);
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

    [[nodiscard]] auto filter_and_check_valid(const TreeEdges & tree, VariableDomainMap & supported_by_tree, const ProofFlag & tuple_selector, State & state) -> bool
    {
        for (int l = tree.size() - 1; l >= 0; --l) {
            for (const auto & edge : tree[l]) {

                filter_edge(edge, supported_by_tree, tuple_selector, state);

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

    auto filter_again_and_remove_supported(const TreeEdges & tree, VariableDomainMap & supported_by_tree, VariableDomainMap & unsupported, const ProofFlag & tuple_selector, State & state) -> void
    {
        for (int l = tree.size() - 1; l >= 0; --l) {
            for (const auto & edge : tree[l]) {
                filter_edge(edge, supported_by_tree, tuple_selector, state);

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

    [[nodiscard]] auto propagate_using_smart_str(const vector<IntegerVariableID> & selectors, const vector<IntegerVariableID> & vars,
        const SmartTuples & tuples, const vector<Forest> & forests, State & state, vector<ProofFlag> pb_selectors) -> Inference
    {

        bool changed = false, contradiction = false;

        VariableDomainMap unsupported{};
        // Initialise unsupported values to everything in each variable's current domain.
        for (const auto & var : vars) {
            state.for_each_value(var, [&](Integer value) {
                unsupported[var].emplace_back(value);
            });
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

                for (const auto & var : vars) {
                    state.for_each_value(var, [&](Integer value) {
                        supported_by_tree[var].emplace_back(value);
                    });
                }

                // First pass of filtering supported_by_tree and check of validity
                if (! filter_and_check_valid(tree, supported_by_tree, pb_selectors[tuple_idx], state)) {
                    // Not feasible

                    switch (state.infer_equal(selectors[tuple_idx], 0_i, NoJustificationNeeded{})) {
                    case Inference::NoChange: break;
                    case Inference::Change: changed = true; break;
                    case Inference::Contradiction: contradiction = true; break;
                    }
                    break;
                }

                if (contradiction) {
                    return Inference::Contradiction;
                }

                filter_again_and_remove_supported(tree, supported_by_tree, unsupported, pb_selectors[tuple_idx], state);
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
        if (! some_tuple_still_feasible) {
            contradiction = true;
        }

        for (const auto & var : vars) {
            for (const auto & value : unsupported[var]) {
                switch (state.infer_not_equal(var, value, JustifyExplicitly{[&](Proof & proof) -> void {
                    for (unsigned int tuple_idx = 0; tuple_idx < tuples.size(); ++tuple_idx) {
                        proof.emit_rup_proof_line_under_trail(state, WeightedPseudoBooleanSum{} + 1_i * (var != value) + 1_i * (! pb_selectors[tuple_idx]) >= 1_i,
                            ProofLevel::Current);
                    }
                }})) {
                case Inference::NoChange: break;
                case Inference::Change: changed = true; break;
                case Inference::Contradiction: contradiction = true; break;
                }
            }
        }

        return contradiction
            ? Inference::Contradiction
            : changed ? Inference::Change
                      : Inference::NoChange;
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
    [[nodiscard]] auto make_binary_entry_flag(State & state, Propagators & propagators, const IntegerVariableID & var_1, const IntegerVariableID & var_2, const SmartEntryConstraint & c) -> ProofFlag
    {
        switch (c) {
        case SmartEntryConstraint::Equal: {
            // f => var1 == var2
            auto flag = propagators.create_proof_flag("bin_eq");
            propagators.define(state, WeightedPseudoBooleanSum{} + 1_i * var_1 + -1_i * var_2 == 0_i,
                HalfReifyOnConjunctionOf{{flag}});

            // !f => var1 != var2
            auto flag_lt = propagators.create_proof_flag("lt");
            auto flag_gt = propagators.create_proof_flag("gt");
            propagators.define(state, WeightedPseudoBooleanSum{} + 1_i * var_1 + -1_i * var_2 >= 1_i,
                HalfReifyOnConjunctionOf{{flag_gt}});
            propagators.define(state, WeightedPseudoBooleanSum{} + 1_i * var_2 + -1_i * var_1 >= 0_i,
                HalfReifyOnConjunctionOf{{! flag_gt}});
            propagators.define(state, WeightedPseudoBooleanSum{} + 1_i * var_2 + -1_i * var_1 >= 1_i,
                HalfReifyOnConjunctionOf{{flag_lt}});
            propagators.define(state, WeightedPseudoBooleanSum{} + 1_i * var_1 + -1_i * var_2 >= 0_i,
                HalfReifyOnConjunctionOf{{! flag_lt}});
            propagators.define(state, WeightedPseudoBooleanSum{} + 1_i * flag_lt + 1_i * flag_gt >= 1_i,
                HalfReifyOnConjunctionOf{{! flag}});
            return flag;
        }

        case SmartEntryConstraint::GreaterThan: {
            auto flag = propagators.create_proof_flag("bin_gt");
            propagators.define(state, WeightedPseudoBooleanSum{} + 1_i * var_1 + -1_i * var_2 >= 1_i,
                HalfReifyOnConjunctionOf{{flag}});
            propagators.define(state, WeightedPseudoBooleanSum{} + 1_i * var_2 + -1_i * var_1 >= 0_i,
                HalfReifyOnConjunctionOf{{! flag}});
            return flag;
        }

        case SmartEntryConstraint::LessThan: {
            auto flag = propagators.create_proof_flag("bin_lt");
            propagators.define(state, WeightedPseudoBooleanSum{} + 1_i * var_2 + -1_i * var_1 >= 1_i,
                HalfReifyOnConjunctionOf{{flag}});
            propagators.define(state, WeightedPseudoBooleanSum{} + 1_i * var_1 + -1_i * var_2 >= 0_i,
                HalfReifyOnConjunctionOf{{! flag}});
            return flag;
        }

        case SmartEntryConstraint::LessThanEqual: {
            auto flag = propagators.create_proof_flag("bin_le");
            propagators.define(state, WeightedPseudoBooleanSum{} + 1_i * var_2 + -1_i * var_1 >= 0_i,
                HalfReifyOnConjunctionOf{{flag}});
            propagators.define(state, WeightedPseudoBooleanSum{} + 1_i * var_1 + -1_i * var_2 >= 1_i,
                HalfReifyOnConjunctionOf{{! flag}});
            return flag;
        }

        case SmartEntryConstraint::NotEqual: {
            // !f => var1 == var2
            auto flag = propagators.create_proof_flag("bin_eq");
            propagators.define(state, WeightedPseudoBooleanSum{} + 1_i * var_1 + -1_i * var_2 == 0_i,
                HalfReifyOnConjunctionOf{{! flag}});

            // f => var1 != var2
            auto flag_lt = propagators.create_proof_flag("lt");
            auto flag_gt = propagators.create_proof_flag("gt");

            // Means we need f => fgt or flt
            propagators.define(state, WeightedPseudoBooleanSum{} + 1_i * flag_lt + 1_i * flag_gt >= 1_i,
                HalfReifyOnConjunctionOf{{flag}});

            // And then fgt <==> var1 > var2
            propagators.define(state, WeightedPseudoBooleanSum{} + 1_i * var_1 + -1_i * var_2 >= 1_i,
                HalfReifyOnConjunctionOf{{flag_gt}});
            propagators.define(state, WeightedPseudoBooleanSum{} + 1_i * var_2 + -1_i * var_1 >= 0_i,
                HalfReifyOnConjunctionOf{{! flag_gt}});

            // flt <==> var1 < var2
            propagators.define(state, WeightedPseudoBooleanSum{} + 1_i * var_2 + -1_i * var_1 >= 1_i,
                HalfReifyOnConjunctionOf{{flag_lt}});
            propagators.define(state, WeightedPseudoBooleanSum{} + 1_i * var_1 + -1_i * var_2 >= 0_i,
                HalfReifyOnConjunctionOf{{! flag_lt}});

            return flag;
        }

        case SmartEntryConstraint::GreaterThanEqual: {
            auto flag = propagators.create_proof_flag("bin_ge");
            propagators.define(state, WeightedPseudoBooleanSum{} + 1_i * var_1 + -1_i * var_2 >= 0_i,
                HalfReifyOnConjunctionOf{{flag}});
            propagators.define(state, WeightedPseudoBooleanSum{} + 1_i * var_2 + -1_i * var_1 >= 1_i,
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
auto SmartTable::clone() const -> unique_ptr<Constraint>
{
    return make_unique<SmartTable>(_vars, _tuples);
}

auto SmartTable::install(Propagators & propagators, State & initial_state) && -> void
{
    vector<IntegerVariableID> selectors;
    vector<ProofFlag> pb_selectors;

    for (unsigned int i = 0; i < _tuples.size(); ++i) {
        selectors.emplace_back(initial_state.allocate_integer_variable_with_state(0_i, 1_i));
    }

    if (propagators.want_definitions()) {

        for (unsigned int i = 0; i < _tuples.size(); ++i) {
            pb_selectors.emplace_back(propagators.create_proof_flag("t" + to_string(i)));
        }
        WeightedPseudoBooleanSum sum_pb_selectors{};

        for (const auto & s : pb_selectors)
            sum_pb_selectors += 1_i * s;

        propagators.define(initial_state, sum_pb_selectors >= 1_i);

        // Would need a hash function for unordered map, but this shouldn't be too slow
        map<BinaryEntryData, ProofFlag> smart_entry_flags;

        for (unsigned int tuple_idx = 0; tuple_idx < _tuples.size(); ++tuple_idx) {
            WeightedPseudoBooleanSum entry_flags_sum{};
            WeightedPseudoBooleanSum entry_flags_neg_sum{};
            for (const auto & entry : _tuples[tuple_idx]) {
                overloaded{
                    [&](BinaryEntry binary_entry) {
                        //                        if(!provable_entry_member(binary_entry.var_1) || !provable_entry_member(binary_entry.var_2)) {
                        //                            throw UnimplementedException{"Can only proof log smart table binary entries of form <var> <op> <var> + b where b >= 0."};
                        //                        }
                        auto binary_entry_data = make_tuple(binary_entry.var_1, binary_entry.var_2, binary_entry.constraint_type);
                        if (! smart_entry_flags.contains(binary_entry_data))
                            smart_entry_flags[binary_entry_data] = make_binary_entry_flag(initial_state, propagators, binary_entry.var_1, binary_entry.var_2, binary_entry.constraint_type);

                        entry_flags_sum += 1_i * smart_entry_flags[binary_entry_data];
                        entry_flags_neg_sum += -1_i * smart_entry_flags[binary_entry_data];
                    },
                    [&](const UnarySetEntry & unary_set_entry) {
                        auto var = unary_set_entry.var;
                        WeightedPseudoBooleanSum set_value_sum{};
                        WeightedPseudoBooleanSum neg_set_value_sum{};
                        initial_state.for_each_value(var, [&](Integer val) {
                            if (! count(unary_set_entry.values.begin(), unary_set_entry.values.end(), val))
                                set_value_sum += 1_i * (var != val);
                        });

                        for (const auto & val : unary_set_entry.values)
                            neg_set_value_sum += 1_i * (var != val);

                        auto flag = unary_set_entry.constraint_type == SmartEntryConstraint::In ? propagators.create_proof_flag("inset") : propagators.create_proof_flag("notinset");

                        auto set_rhs = Integer{static_cast<long long>(set_value_sum.terms.size())};
                        auto neg_set_rhs = Integer{static_cast<long long>(neg_set_value_sum.terms.size())};
                        propagators.define(initial_state, move(set_value_sum) >= set_rhs,
                            HalfReifyOnConjunctionOf{{unary_set_entry.constraint_type == SmartEntryConstraint::In ? flag : ! flag}});
                        propagators.define(initial_state, move(neg_set_value_sum) >= neg_set_rhs,
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
            propagators.define(initial_state, move(entry_flags_sum) >= tuple_len,
                HalfReifyOnConjunctionOf{{pb_selectors[tuple_idx]}});
            propagators.define(initial_state, move(entry_flags_neg_sum) >= -tuple_len + 1_i,
                HalfReifyOnConjunctionOf{{! pb_selectors[tuple_idx]}});
        }
    }

    // Trigger when any var changes? Is this over-kill?
    Triggers triggers;
    triggers.on_change = {_vars.begin(), _vars.end()};

    vector<Forest> forests = build_forests(_tuples);

    propagators.install(
        [selectors, vars = _vars, tuples = move(_tuples), forests = move(forests), pb_selectors = move(pb_selectors)](State & state) -> pair<Inference, PropagatorState> {
            return pair{
                propagate_using_smart_str(selectors, vars, tuples, forests, state, pb_selectors),
                PropagatorState::Enable};
        },
        triggers,
        "smart table");
}

auto SmartTable::describe_for_proof() -> string
{
    return "smart table";
}
