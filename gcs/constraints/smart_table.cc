#include <gcs/constraints/smart_table.hh>
#include <gcs/innards/propagators.hh>
#include <gcs/innards/extensional_utils.hh>

#include <utility>
#include <vector>
#include <variant>
#include <map>
#include <set>

#include <gcs/exception.hh>
#include <gcs/smart_entry.hh>
#include <util/overloaded.hh>

using std::make_unique;
using std::unique_ptr;
using std::vector;
using std::pair;
using std::visit;
using std::unordered_map;
using std::set;

using namespace gcs;
using namespace gcs::innards;


// -- Remove
#include <iostream>
#include <string>
using std::string;
using std::cout;
using std::endl;
// --

SmartTable::SmartTable(const vector<IntegerVariableID> & v, SmartTuples & t) :
        _vars(v),
        _tuples(t)
{
}

namespace
{

    auto propagate_using_smart_str(const vector<IntegerVariableID>& selectors, const vector<IntegerVariableID>& vars, const SmartTuples& tuples, const vector<SmartTable::Forest>& forests, State& state) -> Inference {
        unordered_map<IntegerVariableID, vector<Integer>> unsupported;
        // Initialise unsupported values to everything in each variable's current domain.
        for(const auto & var : vars) {
            state.for_each_value(var, [&](Integer value) {
                if( !unsupported.contains(var)) {
                    unsupported[var] = vector<Integer>{};
                }
                unsupported[var].emplace_back(value);
            });
        }

        // Check that feasible tuples are still feasible
        // and also have them remove values from "unsupported" that they support
        for(unsigned int tuple_idx = 0; tuple_idx < tuples.size(); ++tuple_idx) {
            // Skip infeasible tuple
            if(state.optional_single_value(selectors[tuple_idx]) == 0_i) {
                continue;
            }

            for(const auto& tree : forests[tuple_idx]) {
                // Initialise supported by tree to current variable domains
                unordered_map<IntegerVariableID, vector<Integer>> supported_by_tree;

                for(const auto & var : vars) {
                    state.for_each_value(var, [&](Integer value) {
                        if( !unsupported.contains(var)) {
                            supported_by_tree[var] = vector<Integer>{};
                        }
                        supported_by_tree[var].emplace_back(value);
                    });
                }

                // First pass of removal of unsupported values and check of validity
                if(!filter_and_check_valid(tree, supported_by_tree)) {

                }
            }
        }

        return Inference::NoChange;
    }

    auto build_tree(const IntegerVariableID& root, int current_level, vector<vector<SmartEntry>>& entry_tree,
                               unordered_map<IntegerVariableID, bool>& node_visited,
                               const unordered_map<IntegerVariableID, vector<SmartEntry>>& adjacent_edges) -> void {
        node_visited[root] = true;
        for(const auto& edge : adjacent_edges.at(root)) {
            overloaded{
                    [&](BinaryEntry binary_entry) {
                        if(!node_visited[binary_entry.var_1]) {
                            entry_tree[current_level].emplace_back(edge);
                            entry_tree.emplace_back(vector<SmartEntry>{});
                            build_tree(binary_entry.var_1, current_level+1, entry_tree, node_visited, adjacent_edges);
                        } else if(!node_visited[binary_entry.var_2]) {
                            entry_tree[current_level].emplace_back(edge);
                            entry_tree.emplace_back(vector<SmartEntry>{});
                            build_tree(binary_entry.var_2, current_level+1, entry_tree, node_visited, adjacent_edges);
                        }
                    },
                    [&](UnarySetEntry u) {
                        entry_tree[current_level].emplace_back(edge);
                        },
                    [&](UnaryValueEntry u) {
                        entry_tree[current_level].emplace_back(edge);
                    }
            }.visit(edge);
        }
    }

    auto build_forests(SmartTuples& tuples) -> vector<SmartTable::Forest> {
        vector<SmartTable::Forest> forests{};
        for(unsigned int tuple_idx = 0; tuple_idx < tuples.size(); ++tuple_idx) {
            auto current_tuple = tuples[tuple_idx];

            unordered_map<IntegerVariableID, bool> node_visited;
            unordered_map<IntegerVariableID, vector<SmartEntry>> adjacent_edges;

            // Get all the vars in the tuple and record adjacencies
            for(const auto & entry : current_tuple) {
                overloaded {
                        [&](const BinaryEntry& binary_entry) {
                            node_visited[binary_entry.var_1] = false;
                            node_visited[binary_entry.var_2] = false;
                            adjacent_edges.try_emplace(binary_entry.var_1, vector<SmartEntry>{});
                            adjacent_edges.try_emplace(binary_entry.var_2, vector<SmartEntry>{});
                            adjacent_edges[binary_entry.var_1].emplace_back(binary_entry);
                            adjacent_edges[binary_entry.var_2].emplace_back(binary_entry);
                        },
                        [&](const UnaryValueEntry& unary_val_entry) {
                            node_visited[unary_val_entry.var] = false;
                            adjacent_edges.try_emplace(unary_val_entry.var, vector<SmartEntry>{});
                            adjacent_edges[unary_val_entry.var].emplace_back(unary_val_entry);
                        },
                        [&](const UnarySetEntry& unary_set_entry) {
                            node_visited[unary_set_entry.var] = false;
                            adjacent_edges.try_emplace(unary_set_entry.var, vector<SmartEntry>{});
                            adjacent_edges[unary_set_entry.var].emplace_back(unary_set_entry);
                        }
                }.visit(entry);
            }

            SmartTable::Forest forest{};
            for(auto & var_pair : node_visited) {
                auto& var = var_pair.first;
                auto& visited = var_pair.second;
                if(visited) continue;
                vector<vector<SmartEntry>> entry_tree;
                entry_tree.emplace_back(vector<SmartEntry>{});
                // Recursively build the tree starting from this node
                build_tree(var, 0, entry_tree, node_visited, adjacent_edges);
                forest.emplace_back(entry_tree);
            }

            forests.emplace_back(forest);
        }

        return forests;
    }

    // --- remove - for sanity checking only
    auto index_of(const IntegerVariableID& val, const vector<IntegerVariableID>& vec) -> int {
        ptrdiff_t pos = distance(vec.begin(), find(vec.begin(), vec.end(), val));
        return (int)pos;
    }


    auto print_edge(const SmartEntry& edge, const vector<IntegerVariableID> vars) -> void {
        const string stringtypes[] = {"LESS_THAN", "LESS_THAN_EQUAL", "EQUAL", "NOT_EQUAL", "GREATER_THAN", "GREATER_THAN_EQUAL", "IN", "NOT_IN"};
        overloaded{
            [&](BinaryEntry b) {
                cout << index_of(b.var_1, vars) << ", "<< stringtypes[b.constraint_type] << ", " << index_of(b.var_2, vars);
            },
            [&](UnarySetEntry us) {
                cout << &us.var;
            },
            [&](UnaryValueEntry us) {
                cout << &us.var;
            }
        }.visit(edge);
    }
    // ---
}

auto SmartTable::clone() const -> unique_ptr<Constraint>
{
    return make_unique<SmartTable>(_vars, _tuples);
}

auto SmartTable::install(Propagators & propagators, State & initial_state) && -> void
{
    if (propagators.want_definitions()) {
        throw UnimplementedException{"PB for Smart Tables not yet implemented"};
    }

    // Trigger when any var changes? Is this overkill?
    Triggers triggers;
    triggers.on_change = {_vars.begin(), _vars.end()};

    vector<IntegerVariableID> selectors;

    for(unsigned int i = 0; i < _tuples.size(); ++i) {
        selectors.emplace_back(initial_state.allocate_integer_variable_with_state(0_i, 1_i));
    }

    vector<Forest> forests = build_forests(_tuples);

//    for (const auto & forest : forests) {
//        cout << "Tuple forest:" << endl;
//        for (const auto & tree : forest) {
//            for(const auto & level : tree) {
//                for(const auto & edge : level) {
//                    print_edge(edge, _vars);
//                }
//                cout << endl;
//            }
//            cout << "----" << endl;
//        }
//        cout << "----------------" << endl;
//    }

    propagators.install(
            [selectors, vars = _vars, tuples = _tuples, forests = forests] (State & state) -> pair<Inference, PropagatorState> {
                return pair{
                        propagate_using_smart_str(selectors, vars, tuples, forests, state),
                        PropagatorState::Enable};
            },
            triggers,
            "smart table");
}

auto SmartTable::describe_for_proof() -> std::string
{
    return "smart table";
}
