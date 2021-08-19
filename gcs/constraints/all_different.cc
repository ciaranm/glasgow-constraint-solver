/* vim: set sw=4 sts=4 et foldmethod=syntax : */

#include <gcs/constraints/all_different.hh>
#include <gcs/low_level_constraint_store.hh>
#include <gcs/state.hh>

#include <util/for_each.hh>

#include <algorithm>
#include <functional>
#include <list>
#include <map>
#include <set>
#include <sstream>
#include <type_traits>
#include <utility>
#include <variant>

using namespace gcs;

using std::decay_t;
using std::endl;
using std::is_same_v;
using std::function;
using std::list;
using std::map;
using std::max;
using std::min;
using std::nullopt;
using std::pair;
using std::set;
using std::stringstream;
using std::variant;
using std::vector;

AllDifferent::AllDifferent(const vector<IntegerVariableID> & v) :
    _vars(move(v))
{
}

namespace
{
    auto build_matching(
            const set<pair<IntegerVariableID, Integer> > & edges,
            const set<IntegerVariableID> & lhs,
            set<IntegerVariableID> & left_covered,
            set<Integer> & right_covered,
            set<pair<IntegerVariableID, Integer> > & matching
            ) -> void
    {
        // start with a greedy matching
        for (auto & e : edges) {
            if ((! left_covered.count(e.first)) && (! right_covered.count(e.second))) {
                left_covered.insert(e.first);
                right_covered.insert(e.second);
                matching.insert(e);
            }
        }

        // now augment
        while (true) {
            set<IntegerVariableID> reached_on_the_left;
            set<Integer> reached_on_the_right;

            map<Integer, IntegerVariableID> how_we_got_to_on_the_right;
            map<IntegerVariableID, Integer> how_we_got_to_on_the_left;

            // start from exposed variables
            set_difference(lhs.begin(), lhs.end(), left_covered.begin(), left_covered.end(),
                    inserter(reached_on_the_left, reached_on_the_left.begin()));

            bool still_searching = true, found_a_path = false;
            Integer path_endpoint = 0_i;
            while (still_searching && ! found_a_path) {
                still_searching = false;

                // for each potential left-to-right edge that is not in the matching,
                // that starts with something on the left...
                for (auto & [ var, val ] : edges) {
                    if (reached_on_the_left.count(var) && ! matching.count(pair{ var, val })) {
                        // we've found something we can reach on the right
                        if (reached_on_the_right.insert(val).second) {
                            how_we_got_to_on_the_right.insert(pair{ val, var });
                            // is it exposed?
                            if (! right_covered.count(val)) {
                                found_a_path = true;
                                path_endpoint = val;
                                break;
                            }
                            else {
                                still_searching = true;
                            }
                        }
                    }
                }

                // if we've not grown our right set, or if we've already found a
                // path, we're done
                if (found_a_path || ! still_searching)
                    break;
                still_searching = false;

                // now, for each potential right-to-left edge that is in the matching,
                // that starts with something we've reached on the right...
                for (auto & [ var, val ] : edges) {
                    if (reached_on_the_right.count(val) && matching.count(pair{ var, val })) {
                        // we've found something we can reach on the left
                        if (reached_on_the_left.insert(var).second) {
                            how_we_got_to_on_the_left.insert(pair{ var, val });
                            still_searching = true;
                        }
                    }
                }
            }

            if (found_a_path) {
                // we've included another value
                right_covered.insert(path_endpoint);

                // reconstruct the augmenting path to figure out how we did it,
                // going backwards
                while (true) {
                    // find how we got to the thing on the right...
                    auto how_right = how_we_got_to_on_the_right.find(path_endpoint);

                    // is the thing on the left exposed?
                    if (! left_covered.count(how_right->second)) {
                        left_covered.insert(how_right->second);
                        matching.insert(pair{ how_right->second, path_endpoint });
                        break;
                    }
                    else {
                        // nope, we must have reached this from the right
                        auto how_left = how_we_got_to_on_the_left.find(how_right->second);
                        matching.erase(pair{ how_right->second, how_left->second });
                        matching.insert(pair{ how_right->second, path_endpoint });

                        path_endpoint = how_left->second;
                    }
                }
            }
            else
                break;
        }
    }

    auto prove_matching_is_too_small(
            const map<Integer, ProofLine> & constraint_numbers,
            Proof & proof,
            const set<pair<IntegerVariableID, Integer> > & edges,
            const set<IntegerVariableID> & lhs,
            const set<IntegerVariableID> & left_covered,
            const set<pair<IntegerVariableID, Integer> > & matching
            ) -> void
    {
        map<Integer, IntegerVariableID> inverse_matching;
        for (auto & [ l, r ] : matching)
            inverse_matching.emplace(r, l);

        set<IntegerVariableID> hall_variables;
        set<Integer> hall_values;

        // there must be at least one thing uncovered, and this will
        // necessarily participate in a hall violator
        for (auto & v : lhs)
            if (! left_covered.count(v)) {
                hall_variables.insert(v);
                break;
            }

        // either we have found a hall violator, or we have a spare value
        // on the right
        while (true) {
            set<Integer> n_of_hall_variables;
            for (auto & [ l, r ] : edges)
                if (hall_variables.count(l))
                    n_of_hall_variables.insert(r);

            bool is_subset = true;
            Integer not_subset_witness{ 0_i };
            for (auto & v : n_of_hall_variables)
                if (! hall_values.count(v)) {
                    is_subset = false;
                    not_subset_witness = v;
                    break;
                }

            // have we found a hall violator?
            if (is_subset)
                break;

            // not_subset_witness must be matched to something not yet in
            // hall_variables
            IntegerVariableID add_to_hall_variable = inverse_matching.find(not_subset_witness)->second;
            hall_variables.insert(add_to_hall_variable);
            hall_values.insert(not_subset_witness);
        }

        // each variable in the violator has to take at least one value that is
        // left in its domain...
        stringstream proof_step;
        proof_step << "p";
        bool first = true;
        for (auto & v : hall_variables) {
            proof_step << " " << proof.constraint_saying_variable_takes_at_least_one_value(v);
            if (! first)
                proof_step << " +";
            first = false;
        }

        // and each value in the component can only be used once
        for (auto & v : hall_values)
            proof_step << " " << constraint_numbers.find(v)->second << " +";

        proof_step << " 0";
        proof.emit_proof_line(proof_step.str());
    }

    using Vertex = variant<IntegerVariableID, Integer>;

    auto prove_deletion_using_sccs(
            const map<Integer, ProofLine> & constraint_numbers,
            Proof & proof,
            const map<IntegerVariableID, list<Integer> > & edges_out_from_variable,
            const map<Integer, list<IntegerVariableID> > & edges_out_from_value,
            const IntegerVariableID delete_variable,
            const Integer delete_value,
            const map<Vertex, int> & components
            ) -> void
    {
        // we know a hall set exists, but we have to find it. starting
        // from but not including the end of the edge we're deleting,
        // everything reachable forms a hall set.
        set<Vertex> to_explore, explored;
        set<IntegerVariableID> hall_left;
        set<Integer> hall_right;
        to_explore.insert(delete_value);
        int care_about_scc = components.find(delete_value)->second;
        while (! to_explore.empty()) {
            Vertex n = *to_explore.begin();
            to_explore.erase(n);
            explored.insert(n);

            visit([&] (const auto & x) -> void {
                    if constexpr (is_same_v<decay_t<decltype(x)>, IntegerVariableID>) {
                        hall_left.emplace(x);
                        auto e = edges_out_from_variable.find(x);
                        if (e != edges_out_from_variable.end())
                            for (const auto & t : e->second) {
                                if (care_about_scc == components.find(t)->second && ! explored.count(t))
                                    to_explore.insert(t);
                                }
                        }
                        else {
                            hall_right.emplace(x);
                            auto e = edges_out_from_value.find(x);
                            if (e != edges_out_from_value.end())
                                for (const auto & t : e->second) {
                                    if (care_about_scc == components.find(t)->second && ! explored.count(t))
                                        to_explore.insert(t);
                                }
                        }
                    }, n);
        }

        if (! hall_left.empty()) {
            stringstream proof_step;

            proof_step << "* all different, found hall set {";
            for (auto & h : hall_left)
                proof_step << " " << debug_string(h);

            proof_step << " } having values {";
            for (auto & w : hall_right)
                proof_step << " " << w;
            proof_step << " } and so " << debug_string(delete_variable) << " != " << delete_value << endl;

            proof_step << "p";
            bool first = true;
            for (auto & h : hall_left) {
                proof_step << " " << proof.constraint_saying_variable_takes_at_least_one_value(h);
                if (! first)
                    proof_step << " +";
                first = false;
            }

            for (auto & w : hall_right)
                proof_step << " " << constraint_numbers.find(w)->second << " +";

            proof_step << " 0";
            proof.emit_proof_line(proof_step.str());
        }
    }

    auto propagate_all_different(
            const map<Integer, ProofLine> & constraint_numbers,
            const vector<IntegerVariableID> & vars,
            State & state) -> Inference
    {
        // find a matching to check feasibility
        set<IntegerVariableID> lhs{ vars.begin(), vars.end() };
        set<Integer> rhs;
        set<pair<IntegerVariableID, Integer> > edges;

        for (auto & var : vars) {
            state.for_each_value(var, [&] (Integer val) {
                rhs.emplace(val);
                edges.emplace(pair{ var, val });
            });
        }

        set<IntegerVariableID> left_covered;
        set<Integer> right_covered;
        set<pair<IntegerVariableID, Integer> > matching;

        build_matching(edges, lhs, left_covered, right_covered, matching);

        // is our matching big enough?
        if (left_covered.size() != lhs.size()) {
            // nope. we've got a maximum cardinality matching that leaves at least
            // one thing on the left uncovered.
            return state.infer(+constant_variable(false), JustifyExplicitly{ [&] (Proof & proof) -> void {
                    prove_matching_is_too_small(constraint_numbers, proof, edges, lhs, left_covered, matching);
                    } });
        }

        // we have a matching that uses every variable. however, some edges may
        // not occur in any maximum cardinality matching, and we can delete
        // these. first we need to build the directed matching graph...
        map<Vertex, list<Vertex> > edges_out_from;
        map<IntegerVariableID, list<Integer> > edges_out_from_variable, edges_in_to_variable;
        map<Integer, list<IntegerVariableID> > edges_out_from_value, edges_in_to_value;

        for (auto & [ f, t ] : edges)
            if (matching.count(pair{ f, t })) {
                edges_out_from[t].push_back(f);
                edges_out_from_value[t].push_back(f);
                edges_in_to_variable[f].push_back(t);
            }
            else {
                edges_out_from[f].push_back(t);
                edges_out_from_variable[f].push_back(t);
                edges_in_to_value[t].push_back(f);
            }

        // now we need to find strongly connected components...
        map<Vertex, int> indices, lowlinks, components;
        list<Vertex> stack;
        set<Vertex> enstackinated;
        set<Vertex> all_vertices;
        int next_index = 0, number_of_components = 0;

        for (auto & v : vars) {
            all_vertices.emplace(v);
            state.for_each_value(v, [&] (Integer val) {
                    all_vertices.emplace(val);
                    });
        }

        function<auto (Vertex) -> void> scc;
        scc = [&] (Vertex v) -> void {
            indices.emplace(v, next_index);
            lowlinks.emplace(v, next_index);
            ++next_index;
            stack.emplace_back(v);
            enstackinated.emplace(v);

            for (auto & w : edges_out_from[v]) {
                if (! indices.count(w)) {
                    scc(w);
                    lowlinks[v] = min(lowlinks[v], lowlinks[w]);
                }
                else if (enstackinated.count(w)) {
                    lowlinks[v] = min(lowlinks[v], lowlinks[w]);
                }
            }

            if (lowlinks[v] == indices[v]) {
                Vertex w = 0_i;
                do {
                    w = stack.back();
                    stack.pop_back();
                    enstackinated.erase(w);
                    components.emplace(w, number_of_components);
                } while (v != w);
                ++number_of_components;
            }
        };

        for (auto & v : all_vertices)
            if (! indices.count(v))
                scc(v);

        // every edge in the original matching is used, and so cannot be
        // deleted
        auto used_edges = matching;

        // for each unmatched vertex, bring in everything that could be updated
        // to take it
        {
            set<Vertex> to_explore{ rhs.begin(), rhs.end() }, explored;
            for (auto & [ _, t ] : matching)
                to_explore.erase(t);

            while (! to_explore.empty()) {
                Vertex v = *to_explore.begin();
                to_explore.erase(v);
                explored.insert(v);

                visit([&] (const auto & x) {
                        if constexpr (is_same_v<decay_t<decltype(x)>, IntegerVariableID>) {
                            for (auto & t : edges_in_to_variable[x]) {
                                used_edges.emplace(x, t);
                                if (! explored.count(t))
                                    to_explore.insert(t);
                            }
                        }
                        else {
                            for (auto & t : edges_in_to_value[x]) {
                                used_edges.emplace(t, x);
                                if (! explored.count(t))
                                    to_explore.insert(t);
                            }
                        }
                        }, v);
            }
        }

        // every edge that starts and ends in the same component is also used
        for (auto & [ f, t ] : edges)
            if (components.find(f)->second == components.find(t)->second)
                used_edges.emplace(f, t);

        // avoid outputting duplicate proof lines
        set<int> sccs_already_done;

        bool changed = false;

        // anything left can be deleted. need to do all of these together if we're doing
        // justifications, to avoid having to figure out an ordering for nested Hall sets
        vector<Literal> deletions;
        for (auto & [ delete_var_name, delete_value ] : edges) {
            if (used_edges.count(pair{ delete_var_name, delete_value }))
                continue;
            deletions.emplace_back(delete_var_name != delete_value);
        }

        switch (state.infer_all(deletions, JustifyExplicitly{ [&] (Proof & proof) -> void {
                    for (auto & [ delete_var_name, delete_value ] : edges) {
                            if (used_edges.count(pair{ delete_var_name, delete_value }))
                                continue;
                            if (sccs_already_done.emplace(components.find(delete_value)->second).second)
                                prove_deletion_using_sccs(constraint_numbers, proof, edges_out_from_variable, edges_out_from_value, delete_var_name, delete_value, components);
                    }
                } })) {
            case Inference::NoChange:      break;
            case Inference::Change:        changed = true; break;
            case Inference::Contradiction: return Inference::Contradiction;
        }

        return changed ? Inference::Change : Inference::NoChange;
    }

    template <typename T_>
    auto nullopt_to_zero(std::optional<T_> && t) -> T_
    {
        return t == nullopt ? 0 : *t;
    }
}

auto AllDifferent::convert_to_low_level(LowLevelConstraintStore & constraints, const State & initial_state) && -> void
{
    map<Integer, ProofLine> constraint_numbers;
    if (constraints.want_nonpropagating()) {
        auto max_upper = initial_state.upper_bound(*max_element(_vars.begin(), _vars.end(), [&] (const IntegerVariableID & v, const IntegerVariableID & w) {
                    return initial_state.upper_bound(v) < initial_state.upper_bound(w);
                    }));
        auto min_lower = initial_state.lower_bound(*min_element(_vars.begin(), _vars.end(), [&] (const IntegerVariableID & v, const IntegerVariableID & w) {
                    return initial_state.lower_bound(v) < initial_state.lower_bound(w);
                    }));
        // for each value in at least one domain...
        for (Integer val = min_lower ; val <= max_upper ; ++val) {
            // at most one variable can take it
            Literals lits;
            for (auto & var : _vars)
                if (initial_state.in_domain(var, val))
                    lits.emplace_back(var == val);
            constraint_numbers.emplace(val, nullopt_to_zero(constraints.at_most_one(initial_state, move(lits), false)));
        }
    }

    vector<VariableID> var_ids{ _vars.begin(), _vars.end() };
    constraints.propagator(initial_state, [vars = move(_vars), save_constraint_numbers = move(constraint_numbers)] (State & state) -> Inference {
            return propagate_all_different(save_constraint_numbers, vars, state);
            }, var_ids);
}

auto AllDifferent::describe_for_proof() -> std::string
{
    return "all different";
}

