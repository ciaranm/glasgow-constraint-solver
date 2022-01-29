/* vim: set sw=4 sts=4 et foldmethod=syntax : */

#include <gcs/constraints/all_different.hh>
#include <gcs/exception.hh>
#include <gcs/propagators.hh>
#include <gcs/state.hh>

#include <util/for_each.hh>
#include <util/overloaded.hh>

#include <algorithm>
#include <functional>
#include <list>
#include <map>
#include <optional>
#include <sstream>
#include <type_traits>
#include <utility>
#include <variant>

using namespace gcs;

using std::adjacent_find;
using std::count;
using std::decay_t;
using std::endl;
using std::function;
using std::is_same_v;
using std::list;
using std::map;
using std::max;
using std::min;
using std::nullopt;
using std::optional;
using std::pair;
using std::sort;
using std::stringstream;
using std::variant;
using std::vector;
using std::visit;

AllDifferent::AllDifferent(const vector<IntegerVariableID> & v) :
    _vars(v)
{
}

namespace
{
    struct Left
    {
        vector<IntegerVariableID>::size_type offset;

        [[nodiscard]] auto operator<=>(const Left &) const = default;
    };

    struct Right
    {
        vector<Integer>::size_type offset;

        [[nodiscard]] auto operator<=>(const Right &) const = default;
    };

    auto build_matching(
        const vector<IntegerVariableID> & vars,
        const vector<Integer> & vals,
        const vector<pair<Left, Right>> & edges,
        vector<uint8_t> & left_covered,
        vector<uint8_t> & right_covered,
        vector<optional<Right>> & matching) -> void
    {
        // start with a greedy matching
        for (auto & e : edges) {
            if ((! left_covered[e.first.offset]) && (! right_covered[e.second.offset])) {
                left_covered[e.first.offset] = 1;
                right_covered[e.second.offset] = 1;
                matching[e.first.offset] = e.second;
            }
        }

        // now augment
        while (true) {
            vector<uint8_t> reached_on_the_left(vars.size(), 0);
            vector<uint8_t> reached_on_the_right(vals.size(), 0);

            vector<Left> how_we_got_to_on_the_right(vals.size(), Left{});
            vector<Right> how_we_got_to_on_the_left(vars.size(), Right{});

            // start from exposed variables
            for (Left v{0}; v.offset != vars.size(); ++v.offset)
                if (! left_covered[v.offset])
                    reached_on_the_left[v.offset] = 1;

            bool still_searching = true, found_a_path = false;
            Right path_endpoint{};
            while (still_searching && ! found_a_path) {
                still_searching = false;

                // for each potential left-to-right edge that is not in the matching,
                // that starts with something on the left...
                for (auto & [var, val] : edges) {
                    if (reached_on_the_left[var.offset] && matching[var.offset] != val) {
                        // we've found something we can reach on the right
                        if (! reached_on_the_right[val.offset]) {
                            reached_on_the_right[val.offset] = 1;
                            how_we_got_to_on_the_right[val.offset] = var;
                            // is it exposed?
                            if (! right_covered[val.offset]) {
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
                for (auto & [var, val] : edges) {
                    if (reached_on_the_right[val.offset] && matching[var.offset] == val) {
                        // we've found something we can reach on the left
                        if (! reached_on_the_left[var.offset]) {
                            reached_on_the_left[var.offset] = 1;
                            how_we_got_to_on_the_left[var.offset] = val;
                            still_searching = true;
                        }
                    }
                }
            }

            if (found_a_path) {
                // we've included another value
                right_covered[path_endpoint.offset] = 1;

                // reconstruct the augmenting path to figure out how we did it,
                // going backwards
                while (true) {
                    // is the thing on the left exposed?
                    if (! left_covered[how_we_got_to_on_the_right[path_endpoint.offset].offset]) {
                        left_covered[how_we_got_to_on_the_right[path_endpoint.offset].offset] = 1;
                        matching[how_we_got_to_on_the_right[path_endpoint.offset].offset] = path_endpoint;
                        break;
                    }
                    else {
                        // nope, we must have reached this from the right
                        matching[how_we_got_to_on_the_right[path_endpoint.offset].offset] = path_endpoint;
                        path_endpoint = how_we_got_to_on_the_left[how_we_got_to_on_the_right[path_endpoint.offset].offset];
                    }
                }
            }
            else
                break;
        }
    }

    auto prove_matching_is_too_small(
        const vector<IntegerVariableID> & vars,
        const vector<Integer> & vals,
        const map<Integer, ProofLine> & constraint_numbers,
        Proof & proof,
        const vector<pair<Left, Right>> & edges,
        const vector<uint8_t> & left_covered,
        const vector<optional<Right>> & matching) -> void
    {
        vector<optional<Left>> inverse_matching(vals.size(), nullopt);
        for_each_with_index(matching, [&](const optional<Right> & r, auto l) {
            if (r)
                inverse_matching[r->offset] = Left{l};
        });

        vector<uint8_t> hall_variables(vars.size(), 0);
        vector<uint8_t> hall_values(vals.size(), 0);

        // there must be at least one thing uncovered, and this will
        // necessarily participate in a hall violator
        for (Left v{0}; v.offset != vars.size(); ++v.offset)
            if (! left_covered[v.offset]) {
                hall_variables[v.offset] = 1;
                break;
            }

        // either we have found a hall violator, or we have a spare value
        // on the right
        while (true) {
            vector<uint8_t> n_of_hall_variables(vals.size(), 0);
            for (auto & [l, r] : edges)
                if (hall_variables[l.offset])
                    n_of_hall_variables[r.offset] = 1;

            bool is_subset = true;
            Right not_subset_witness;
            for (Right v{0}; v.offset != vals.size(); ++v.offset)
                if (n_of_hall_variables[v.offset] && ! hall_values[v.offset]) {
                    is_subset = false;
                    not_subset_witness = v;
                    break;
                }

            // have we found a hall violator?
            if (is_subset)
                break;

            // not_subset_witness must be matched to something not yet in
            // hall_variables
            Left add_to_hall_variable = *inverse_matching[not_subset_witness.offset];
            hall_variables[add_to_hall_variable.offset] = 1;
            hall_values[not_subset_witness.offset] = 1;
        }

        // we are going to need the at least one value variables
        vector<ProofLine> at_least_one_constraints;
        for (auto & v : hall_variables)
            if (v)
                at_least_one_constraints.push_back(proof.need_constraint_saying_variable_takes_at_least_one_value(vars[v]));

        // each variable in the violator has to take at least one value that is
        // left in its domain...
        stringstream proof_step;
        proof_step << "p";
        bool first = true;
        for (auto & c : at_least_one_constraints) {
            proof_step << " " << c;
            if (! first)
                proof_step << " +";
            first = false;
        }

        // and each value in the component can only be used once
        for (Right v{0}; v.offset != vals.size(); ++v.offset)
            if (hall_values[v.offset])
                proof_step << " " << constraint_numbers.find(vals[v.offset])->second << " +";

        proof_step << " 0";
        proof.emit_proof_line(proof_step.str());
    }

    using Vertex = variant<Left, Right>;

    auto vertex_to_offset(
        const vector<IntegerVariableID> & vars,
        const vector<Integer> &,
        Vertex v) -> std::size_t
    {
        return overloaded{
            [&](const Left & l) { return l.offset; },
            [&](const Right & r) { return vars.size() + r.offset; }}
            .visit(v);
    }

    auto prove_deletion_using_sccs(
        const vector<IntegerVariableID> & vars,
        const vector<Integer> & vals,
        const map<Integer, ProofLine> & constraint_numbers,
        Proof & proof,
        const vector<vector<Right>> & edges_out_from_variable,
        const vector<vector<Left>> & edges_out_from_value,
        const Left delete_variable,
        const Right delete_value,
        const vector<int> & components) -> void
    {
        // we know a hall set exists, but we have to find it. starting
        // from but not including the end of the edge we're deleting,
        // everything reachable forms a hall set.
        vector<uint8_t> in_to_explore(vars.size() + vals.size(), 0);
        vector<Vertex> to_explore;

        vector<uint8_t> explored(vars.size() + vals.size(), 0);
        vector<uint8_t> hall_left(vars.size(), 0);
        vector<uint8_t> hall_right(vals.size(), 0);
        bool have_hall_left = false;

        in_to_explore[vertex_to_offset(vars, vals, delete_value)] = 1;
        to_explore.push_back(delete_value);
        int care_about_scc = components[vertex_to_offset(vars, vals, delete_value)];
        while (! to_explore.empty()) {
            Vertex n = to_explore.back();
            to_explore.pop_back();
            in_to_explore[vertex_to_offset(vars, vals, n)] = 0;
            explored[vertex_to_offset(vars, vals, n)] = 1;

            visit([&](const auto & x) -> void {
                if constexpr (is_same_v<decay_t<decltype(x)>, Left>) {
                    hall_left[x.offset] = 1;
                    have_hall_left = true;
                    for (const auto & t : edges_out_from_variable[x.offset]) {
                        if (care_about_scc == components[vertex_to_offset(vars, vals, t)] && ! explored[vertex_to_offset(vars, vals, t)]) {
                            if (0 == in_to_explore[vertex_to_offset(vars, vals, t)]) {
                                to_explore.push_back(t);
                                in_to_explore[vertex_to_offset(vars, vals, t)] = 1;
                            }
                        }
                    }
                }
                else {
                    hall_right[x.offset] = 1;
                    for (const auto & t : edges_out_from_value[x.offset]) {
                        if (care_about_scc == components[vertex_to_offset(vars, vals, t)] && ! explored[vertex_to_offset(vars, vals, t)]) {
                            if (0 == in_to_explore[vertex_to_offset(vars, vals, t)]) {
                                to_explore.push_back(t);
                                in_to_explore[vertex_to_offset(vars, vals, t)] = 1;
                            }
                        }
                    }
                }
            },
                n);
        }

        if (have_hall_left) {
            stringstream proof_step;

            proof_step << "* all different, found hall set {";
            for (Left v{0}; v.offset != vars.size(); ++v.offset)
                if (hall_left[v.offset])
                    proof_step << " " << debug_string(vars[v.offset]);

            proof_step << " } having values {";
            for (Right v{0}; v.offset != vals.size(); ++v.offset)
                if (hall_right[v.offset])
                    proof_step << " " << vals[v.offset];
            proof_step << " } and so " << debug_string(vars[delete_variable.offset]) << " != " << vals[delete_value.offset] << endl;

            // we are going to need the at least one value variables
            vector<ProofLine> at_least_one_constraints;
            for (Left v{0}; v.offset != vars.size(); ++v.offset)
                if (hall_left[v.offset])
                    at_least_one_constraints.push_back(proof.need_constraint_saying_variable_takes_at_least_one_value(vars[v.offset]));

            proof_step << "p";
            bool first = true;
            for (auto & c : at_least_one_constraints) {
                proof_step << " " << c;
                if (! first)
                    proof_step << " +";
                first = false;
            }

            for (Right v{0}; v.offset != vals.size(); ++v.offset)
                if (hall_right[v.offset])
                    proof_step << " " << constraint_numbers.find(vals[v.offset])->second << " +";

            proof_step << " 0";
            proof.emit_proof_line(proof_step.str());
        }
    }

    auto propagate_all_different(
        const vector<IntegerVariableID> & vars,
        const vector<Integer> & vals,
        const map<Integer, ProofLine> & constraint_numbers,
        State & state) -> Inference
    {
        // find a matching to check feasibility
        vector<pair<Left, Right>> edges;

        for_each_with_index(vars, [&](IntegerVariableID var, auto var_idx) {
            for_each_with_index(vals, [&](Integer val, auto val_idx) {
                if (state.in_domain(var, val))
                    edges.emplace_back(var_idx, val_idx);
            });
        });

        vector<uint8_t> left_covered(vars.size(), 0);
        vector<uint8_t> right_covered(vals.size(), 0);
        vector<optional<Right>> matching(vars.size(), nullopt);

        build_matching(vars, vals, edges, left_covered, right_covered, matching);

        // is our matching big enough?
        if (left_covered.size() != vars.size()) {
            // nope. we've got a maximum cardinality matching that leaves at least
            // one thing on the left uncovered.
            return state.infer(FalseLiteral{}, JustifyExplicitly{[&](Proof & proof, vector<ProofLine> &) -> void {
                prove_matching_is_too_small(vars, vals, constraint_numbers, proof, edges, left_covered, matching);
            }});
        }

        // we have a matching that uses every variable. however, some edges may
        // not occur in any maximum cardinality matching, and we can delete
        // these. first we need to build the directed matching graph...
        vector<vector<Vertex>> edges_out_from(vars.size() + vals.size(), vector<Vertex>{});
        vector<vector<Right>> edges_out_from_variable(vars.size()), edges_in_to_variable(vars.size());
        vector<vector<Left>> edges_out_from_value(vals.size()), edges_in_to_value(vals.size());

        for (auto & [f, t] : edges)
            if (matching[f.offset] == t) {
                edges_out_from[vertex_to_offset(vars, vals, t)].push_back(f);
                edges_out_from_value[t.offset].push_back(f);
                edges_in_to_variable[f.offset].push_back(t);
            }
            else {
                edges_out_from[vertex_to_offset(vars, vals, f)].push_back(t);
                edges_out_from_variable[f.offset].push_back(t);
                edges_in_to_value[t.offset].push_back(f);
            }

        // now we need to find strongly connected components...
        vector<int> indices(vars.size() + vals.size(), 0), lowlinks(vars.size() + vals.size(), 0), components(vars.size() + vals.size(), 0);
        vector<Vertex> stack;
        vector<uint8_t> enstackinated(vars.size() + vals.size());
        int next_index = 1, number_of_components = 0;

        function<auto(Vertex)->void> scc;
        scc = [&](Vertex v) -> void {
            indices[vertex_to_offset(vars, vals, v)] = next_index;
            lowlinks[vertex_to_offset(vars, vals, v)] = next_index;
            ++next_index;
            stack.emplace_back(v);
            enstackinated[vertex_to_offset(vars, vals, v)] = 1;

            for (auto & w : edges_out_from[vertex_to_offset(vars, vals, v)]) {
                if (0 == indices[vertex_to_offset(vars, vals, w)]) {
                    scc(w);
                    lowlinks[vertex_to_offset(vars, vals, v)] = min(
                        lowlinks[vertex_to_offset(vars, vals, v)],
                        lowlinks[vertex_to_offset(vars, vals, w)]);
                }
                else if (enstackinated[vertex_to_offset(vars, vals, w)]) {
                    lowlinks[vertex_to_offset(vars, vals, v)] = min(
                        lowlinks[vertex_to_offset(vars, vals, v)],
                        lowlinks[vertex_to_offset(vars, vals, w)]);
                }
            }

            if (lowlinks[vertex_to_offset(vars, vals, v)] == indices[vertex_to_offset(vars, vals, v)]) {
                Vertex w;
                do {
                    w = stack.back();
                    stack.pop_back();
                    enstackinated[vertex_to_offset(vars, vals, w)] = 0;
                    components[vertex_to_offset(vars, vals, w)] = number_of_components;
                } while (v != w);
                ++number_of_components;
            }
        };

        for (Left v{0}; v.offset != vars.size(); ++v.offset)
            if (0 == indices[vertex_to_offset(vars, vals, v)])
                scc(v);

        for (Right v{0}; v.offset != vals.size(); ++v.offset)
            if (0 == indices[vertex_to_offset(vars, vals, v)])
                scc(v);

        // every edge in the original matching is used, and so cannot be
        // deleted
        vector<vector<uint8_t>> used_edges(vars.size(), vector<uint8_t>(vals.size(), 0));
        for_each_with_index(matching, [&](const optional<Right> & r, auto l) {
            if (r)
                used_edges[l][r->offset] = 1;
        });

        // for each unmatched vertex, bring in everything that could be updated
        // to take it
        {
            vector<Vertex> to_explore;
            vector<uint8_t> in_to_explore(vars.size() + vals.size(), 0);

            vector<uint8_t> explored(vars.size() + vals.size(), 0);
            for (Right v{0}; v.offset != vals.size(); ++v.offset)
                in_to_explore[vertex_to_offset(vars, vals, v)] = 1;

            for (auto & t : matching)
                if (t)
                    in_to_explore[vertex_to_offset(vars, vals, *t)] = 0;

            for (Left v{0}; v.offset != vars.size(); ++v.offset)
                if (in_to_explore[vertex_to_offset(vars, vals, v)])
                    to_explore.push_back(v);

            for (Right v{0}; v.offset != vals.size(); ++v.offset)
                if (in_to_explore[vertex_to_offset(vars, vals, v)])
                    to_explore.push_back(v);

            while (! to_explore.empty()) {
                Vertex v = to_explore.back();
                to_explore.pop_back();
                in_to_explore[vertex_to_offset(vars, vals, v)] = 0;
                explored[vertex_to_offset(vars, vals, v)] = 1;

                visit([&](const auto & x) {
                    if constexpr (is_same_v<decay_t<decltype(x)>, Left>) {
                        for (auto & t : edges_in_to_variable[x.offset]) {
                            used_edges[x.offset][t.offset] = 1;
                            if (! explored[vertex_to_offset(vars, vals, t)]) {
                                if (! in_to_explore[vertex_to_offset(vars, vals, t)]) {
                                    to_explore.push_back(t);
                                    in_to_explore[vertex_to_offset(vars, vals, t)] = 1;
                                }
                            }
                        }
                    }
                    else {
                        for (auto & t : edges_in_to_value[x.offset]) {
                            used_edges[t.offset][x.offset] = 1;
                            if (! explored[vertex_to_offset(vars, vals, t)]) {
                                if (! in_to_explore[vertex_to_offset(vars, vals, t)]) {
                                    to_explore.push_back(t);
                                    in_to_explore[vertex_to_offset(vars, vals, t)] = 1;
                                }
                            }
                        }
                    }
                },
                    v);
            }
        }

        // every edge that starts and ends in the same component is also used
        for (auto & [f, t] : edges)
            if (components[vertex_to_offset(vars, vals, f)] == components[vertex_to_offset(vars, vals, t)])
                used_edges[f.offset][t.offset] = 1;

        // avoid outputting duplicate proof lines
        vector<uint8_t> sccs_already_done(number_of_components + 1, 0);

        bool changed = false;

        // anything left can be deleted. need to do all of these together if we're doing
        // justifications, to avoid having to figure out an ordering for nested Hall sets
        vector<Literal> deletions;
        for (auto & [delete_var_name, delete_value] : edges) {
            if (used_edges[delete_var_name.offset][delete_value.offset])
                continue;
            deletions.emplace_back(vars[delete_var_name.offset] != vals[delete_value.offset]);
        }

        switch (state.infer_all(deletions, JustifyExplicitly{[&](Proof & proof, vector<ProofLine> &) -> void {
            for (auto & [delete_var_name, delete_value] : edges) {
                if (used_edges[delete_var_name.offset][delete_value.offset])
                    continue;
                if (! sccs_already_done[components[vertex_to_offset(vars, vals, delete_value)]]) {
                    sccs_already_done[components[vertex_to_offset(vars, vals, delete_value)]] = 1;
                    prove_deletion_using_sccs(vars, vals, constraint_numbers, proof, edges_out_from_variable, edges_out_from_value, delete_var_name, delete_value, components);
                }
            }
        }})) {
        case Inference::NoChange: break;
        case Inference::Change: changed = true; break;
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

auto AllDifferent::install(Propagators & propagators, const State & initial_state) && -> void
{
    map<Integer, ProofLine> constraint_numbers;
    if (propagators.want_nonpropagating()) {
        auto max_upper = initial_state.upper_bound(*max_element(_vars.begin(), _vars.end(), [&](const IntegerVariableID & v, const IntegerVariableID & w) {
            return initial_state.upper_bound(v) < initial_state.upper_bound(w);
        }));
        auto min_lower = initial_state.lower_bound(*min_element(_vars.begin(), _vars.end(), [&](const IntegerVariableID & v, const IntegerVariableID & w) {
            return initial_state.lower_bound(v) < initial_state.lower_bound(w);
        }));
        // for each value in at least one domain...
        for (Integer val = min_lower; val <= max_upper; ++val) {
            // at most one variable can take it
            Literals lits;
            for (auto & var : _vars)
                if (initial_state.in_domain(var, val))
                    lits.emplace_back(var == val);
            constraint_numbers.emplace(val, nullopt_to_zero(propagators.at_most_one(initial_state, move(lits), false)));
        }
    }

    auto sanitised_vars = move(_vars);
    sort(sanitised_vars.begin(), sanitised_vars.end());
    if (sanitised_vars.end() != adjacent_find(sanitised_vars.begin(), sanitised_vars.end()))
        throw UnexpectedException{"not sure what to do about duplicate variables in an alldifferent"};

    Triggers triggers;
    triggers.on_change = {sanitised_vars.begin(), sanitised_vars.end()};
    vector<Integer> compressed_vals;

    for (auto & var : sanitised_vars)
        initial_state.for_each_value(var, [&](Integer val) {
            if (compressed_vals.end() == find(compressed_vals.begin(), compressed_vals.end(), val))
                compressed_vals.push_back(val);
        });

    propagators.propagator(
        initial_state, [vars = move(sanitised_vars), vals = move(compressed_vals), save_constraint_numbers = move(constraint_numbers)](State & state) -> pair<Inference, PropagatorState> {
            return pair{propagate_all_different(vars, vals, save_constraint_numbers, state), PropagatorState::Enable};
        },
        triggers, "alldiff");
}

auto AllDifferent::describe_for_proof() -> std::string
{
    return "all different";
}
