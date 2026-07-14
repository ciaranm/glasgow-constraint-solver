#include <gcs/constraint.hh>
#include <gcs/constraints/all_different/encoding.hh>
#include <gcs/constraints/all_different/gac_all_different.hh>
#include <gcs/constraints/all_different/hints.hh>
#include <gcs/constraints/all_different/justify.hh>
#include <gcs/exception.hh>
#include <gcs/innards/assertion_hints.hh>
#include <gcs/innards/inference_tracker.hh>
#include <gcs/innards/proofs/names_and_ids_tracker.hh>
#include <gcs/innards/proofs/proof_logger.hh>
#include <gcs/innards/proofs/proof_model.hh>
#include <gcs/innards/propagators.hh>
#include <gcs/innards/s_expr.hh>
#include <gcs/innards/state.hh>
#include <gcs/innards/variable_id_utils.hh>

#include <gcs/proof.hh>
#include <version>

#if defined(__cpp_lib_print) && defined(__cpp_lib_format)
#include <format>
#include <print>
#else
#include <fmt/ostream.h>
#endif

#include <util/enumerate.hh>
#include <util/overloaded.hh>

#include <algorithm>
#include <map>
#include <optional>
#include <sstream>
#include <type_traits>
#include <utility>
#include <variant>

using namespace gcs;
using namespace gcs::innards;

using std::cmp_not_equal;
using std::count;
using std::decay_t;
using std::is_same_v;
using std::lower_bound;
using std::make_shared;
using std::map;
using std::min;
using std::move;
using std::nullopt;
using std::optional;
using std::pair;
using std::shared_ptr;
using std::string;
using std::tuple;
using std::unique_ptr;
using std::variant;
using std::vector;
using std::visit;
using std::ranges::adjacent_find;
using std::ranges::minmax_element;
using std::ranges::sort;

#if defined(__cpp_lib_print) && defined(__cpp_lib_format)
using std::format;
using std::print;
#else
using fmt::format;
using fmt::print;
#endif

namespace gcs::innards::hints
{
    auto emit_justification(ProofLogger & logger, const AllDifferentHall & hall, const ReasonLiterals &) -> void
    {
        justify_all_different_hall_set_or_violator(logger, *hall.all_vars, hall.hall_vars, hall.hall_vals, *hall.value_am1_constraint_numbers);
    }
}

namespace gcs::innards
{
    // Working storage for propagate_gac_all_different, hoisted out so a
    // propagator can reuse the same buffers on every wake rather than paying
    // several dozen allocations per call (issue #522). Every buffer is
    // assign()ed or clear()ed at its point of use, so capacity ratchets up to
    // the biggest wake seen and stays there. One instance per installed
    // propagator (per constraint clone), so a search owns its scratch
    // exclusively -- see dev_docs/propagator-performance.md.
    struct GacAllDifferentScratch
    {
        struct Left
        {
            std::vector<IntegerVariableID>::size_type offset;

            [[nodiscard]] auto operator<=>(const Left &) const = default;
        };

        struct Right
        {
            std::vector<Integer>::size_type offset;

            [[nodiscard]] auto operator<=>(const Right &) const = default;
        };

        using Vertex = std::variant<Left, Right>;

        // the bipartite variable-value graph and its matching. edges is
        // var-major (all real edges of variable i are contiguous, in value
        // order, at [var_edges_begin[i], var_edges_begin[i + 1])); phantom
        // edges (all_different_except) sit after the real section and are
        // tracked per variable in phantom_plus_one_of_var (0 = none, else
        // right offset + 1, only populated when there are excluded values).
        std::vector<std::pair<Left, Right>> edges;
        std::vector<std::size_t> var_edges_begin;
        std::vector<std::size_t> phantom_plus_one_of_var;
        std::vector<uint8_t> left_covered;
        std::vector<std::optional<Right>> matching;

        // value -> index-into-vals lookup (plus one, with zero meaning not a
        // value of this constraint), dense over [val_lookup_min, val_lookup_min
        // + size). Built on the first wake -- vals is fixed for an installed
        // propagator -- and left empty when the value range is too sparse for
        // a dense table, in which case edge building falls back to probing
        // every (var, val) pair with in_domain.
        bool val_lookup_initialised = false;
        Integer val_lookup_min{0};
        std::vector<uint32_t> val_to_idx_plus_one;
        std::vector<uint8_t> vals_in_domain;

        // augmenting-path search inside build_matching
        std::vector<uint8_t> reached_on_the_left, reached_on_the_right;
        std::vector<Left> how_we_got_to_on_the_right;
        std::vector<Right> how_we_got_to_on_the_left;
        std::vector<Left> bfs_queue;

        // The directed matching graph is implicit in edges + the matching:
        // a variable's out-neighbours are its unmatched edges (walked via
        // var_edges_begin and phantom_plus_one_of_var), a value's single
        // out-neighbour is inverse_matching, and a variable's single
        // in-neighbour is matching. Only the unmatched value -> variables
        // transpose needs materialising, for the backwards used-edge sweep.
        std::vector<std::vector<Left>> edges_in_to_value;

        // Tarjan's algorithm
        std::vector<int> indices, lowlinks, components;
        std::vector<std::size_t> tarjan_stack;
        std::vector<std::pair<std::size_t, std::size_t>> tarjan_frames;
        std::vector<uint8_t> enstackinated;

        // value -> its matched variable, rebuilt alongside the matching each
        // wake; the implicit adjacency above depends on it
        std::vector<std::optional<Left>> inverse_matching;

        // reachability sweeps: the used-edge marking pass, and Hall set
        // extraction in the prove_* helpers
        std::vector<Vertex> to_explore;
        std::vector<uint8_t> in_to_explore, explored;
        std::vector<uint8_t> hall_left, hall_right;
        std::vector<uint8_t> n_of_hall_variables;

        // flat vars.size() * vals.size() bitmap; phantom rights never appear
        std::vector<uint8_t> used_edges;

        // grouping deletions by the SCC that justifies them
        std::vector<std::vector<Literal>> deletions_by_scc;
        std::vector<std::optional<Right>> representatives_for_scc;
    };

    auto make_gac_all_different_scratch() -> std::shared_ptr<GacAllDifferentScratch>
    {
        return make_shared<GacAllDifferentScratch>();
    }
}

namespace
{
    using Left = GacAllDifferentScratch::Left;
    using Right = GacAllDifferentScratch::Right;

    // The edges build can either probe every (var, val) pair with in_domain,
    // or sweep each variable's actual domain and map values through a dense
    // value -> index table. The sweep pays a fixed per-variable cost (bitmap
    // reset, domain iteration, bitmap scan) to avoid a vals.size() in_domain
    // probe per variable, so it only wins when vals is wide enough. Measured,
    // interleaved, whole-program: 1% slower at 10 values (QWH quasigroup7 axiom
    // instances), but 16% faster at 30 values (order-30 balanced latin square
    // completion, where the edge build was 28% of the profile and the sweep
    // cut its cycles by 37%) and 2% faster at 33 (langford --size=11) -- so
    // the crossover is somewhere in 11..29, and this cutoff takes the widest
    // slice of the win that the measurements support.
    constexpr std::size_t min_vals_for_domain_sweep = 24;

    // The dense table has one slot per value in [min(vals), max(vals)], so it
    // only makes sense if the values aren't too spread out. Allow a fixed
    // number of (mostly-empty) slots per distinct value, plus some slack so
    // that a small value set spanning a modest range still qualifies. With 4
    // bytes per slot this also bounds the table's memory at ~256 bytes per
    // distinct value.
    constexpr std::size_t dense_value_table_slots_per_value = 64;
    constexpr std::size_t dense_value_table_slots_slack = 1024;

    // Clear (not deallocate) the first n inner vectors, growing the outer
    // vector with fresh empties if this wake needs more than any previous one.
    // Anything past n is stale from an earlier wake and is never read.
    template <typename T_>
    auto clear_inners_to_size(vector<vector<T_>> & vec, size_t n) -> void
    {
        if (vec.size() < n)
            vec.resize(n);
        for (size_t i = 0; i != n; ++i)
            vec[i].clear();
    }

    // The out-neighbours of a left (variable) vertex in the directed matching
    // graph: its unmatched real edges in value order, then its phantom edge
    // (if any, and unmatched). This is exactly the order the old materialised
    // edges_out_from / edges_out_from_variable lists were built in -- real
    // edges are var-major in edges, phantoms follow the real section -- so
    // everything downstream (Tarjan numbering, Hall set exploration, and
    // hence proof output) is unchanged.
    template <typename F_>
    auto for_each_unmatched_edge_of_var(const GacAllDifferentScratch & scratch, vector<IntegerVariableID>::size_type i, F_ && f) -> void
    {
        const auto & matched = scratch.matching[i];
        for (auto e = scratch.var_edges_begin[i], e_end = scratch.var_edges_begin[i + 1]; e != e_end; ++e) {
            const auto & t = scratch.edges[e].second;
            if (matched != t)
                f(t);
        }
        if (! scratch.phantom_plus_one_of_var.empty())
            if (auto p = scratch.phantom_plus_one_of_var[i]; 0 != p) {
                Right t{p - 1};
                if (matched != t)
                    f(t);
            }
    }

    // Breadth-first search for an augmenting path from an uncovered variable,
    // over the implicit graph: a variable's candidate edges are walked in
    // place, and a covered value leads to its matched variable via
    // inverse_matching. Returns whether it augmented (flipping the matching
    // along the path); scratch.left_covered is updated for the start.
    auto augment_from(size_t n_right, vector<IntegerVariableID>::size_type start, GacAllDifferentScratch & scratch) -> bool
    {
        auto & matching = scratch.matching;
        auto & inverse_matching = scratch.inverse_matching;
        auto & reached_on_the_left = scratch.reached_on_the_left;
        auto & reached_on_the_right = scratch.reached_on_the_right;
        auto & how_we_got_to_on_the_right = scratch.how_we_got_to_on_the_right;
        auto & how_we_got_to_on_the_left = scratch.how_we_got_to_on_the_left;
        auto & queue = scratch.bfs_queue;

        reached_on_the_left.assign(matching.size(), 0);
        reached_on_the_right.assign(n_right, 0);
        how_we_got_to_on_the_right.assign(n_right, Left{});
        how_we_got_to_on_the_left.assign(matching.size(), Right{});

        queue.clear();
        queue.push_back(Left{start});
        reached_on_the_left[start] = 1;

        optional<Right> path_endpoint;
        for (size_t head = 0; head != queue.size() && ! path_endpoint; ++head) {
            const auto l = queue[head];
            for_each_unmatched_edge_of_var(scratch, l.offset, [&](const Right & t) {
                if (path_endpoint || reached_on_the_right[t.offset])
                    return;
                reached_on_the_right[t.offset] = 1;
                how_we_got_to_on_the_right[t.offset] = l;
                if (const auto & nl = inverse_matching[t.offset]) {
                    if (! reached_on_the_left[nl->offset]) {
                        reached_on_the_left[nl->offset] = 1;
                        how_we_got_to_on_the_left[nl->offset] = t;
                        queue.push_back(*nl);
                    }
                }
                else
                    path_endpoint = t;
            });
        }

        if (! path_endpoint)
            return false;

        // flip the matching along the path, walking backwards
        auto t = *path_endpoint;
        while (true) {
            auto l = how_we_got_to_on_the_right[t.offset];
            matching[l.offset] = t;
            inverse_matching[t.offset] = l;
            if (l.offset == start)
                break;
            t = how_we_got_to_on_the_left[l.offset];
        }
        scratch.left_covered[start] = 1;
        return true;
    }

    // Complete scratch.matching into a maximum matching of the current edges,
    // reusing whatever survives from the previous wake when the caller allows
    // it. Any set of matched pairs whose edges still exist is a valid partial
    // matching regardless of what search state it came from -- domains may
    // have changed arbitrarily since, including by backtracking -- because
    // validity only depends on the current graph, so a stale entry is either
    // filtered out here or still usable. Repair is per uncovered variable, in
    // variable order: greedy first (the first uncovered value, in value
    // order, then the phantom), then a breadth-first augmenting-path search.
    // Augmenting for a later variable never creates a path for an earlier one
    // that had none (the standard augmenting-path lemma), so a single pass
    // reaches maximum cardinality. The matching this produces can differ from
    // what a from-scratch rebuild would have found, but the set of edges in
    // no maximum matching -- the deletions -- is matching-independent, so
    // what the propagator infers is unchanged; only proof shape and inference
    // order within a wake can differ.
    auto build_matching(const vector<IntegerVariableID> & vars, size_t n_right, bool reuse_previous, GacAllDifferentScratch & scratch) -> void
    {
        auto & matching = scratch.matching;
        auto & inverse_matching = scratch.inverse_matching;
        auto & left_covered = scratch.left_covered;

        // revalidate the previous wake's matching against the current edges
        if (reuse_previous && matching.size() == vars.size()) {
            for (vector<IntegerVariableID>::size_type i = 0; i != vars.size(); ++i)
                if (matching[i]) {
                    // is (i, *matching[i]) still an edge? the variable's edges
                    // are sorted by value offset
                    const auto b = scratch.edges.begin() + static_cast<std::ptrdiff_t>(scratch.var_edges_begin[i]);
                    const auto e = scratch.edges.begin() + static_cast<std::ptrdiff_t>(scratch.var_edges_begin[i + 1]);
                    const auto it = lower_bound(b, e, matching[i]->offset,
                        [](const pair<Left, Right> & edge, vector<Integer>::size_type off) { return edge.second.offset < off; });
                    if (it == e || it->second.offset != matching[i]->offset)
                        matching[i] = nullopt;
                }
        }
        else
            matching.assign(vars.size(), nullopt);

        left_covered.assign(vars.size(), 0);
        inverse_matching.assign(n_right, nullopt);
        for (const auto & [i, m] : enumerate(matching))
            if (m) {
                left_covered[i] = 1;
                inverse_matching[m->offset] = Left{i};
            }

        for (vector<IntegerVariableID>::size_type i = 0; i != vars.size(); ++i) {
            if (left_covered[i])
                continue;

            // greedy: the first uncovered value, in value order, then the
            // phantom. matching[i] is empty here, so every edge of i is a
            // candidate.
            for (auto e = scratch.var_edges_begin[i], e_end = scratch.var_edges_begin[i + 1]; e != e_end; ++e) {
                const auto & t = scratch.edges[e].second;
                if (! inverse_matching[t.offset]) {
                    matching[i] = t;
                    inverse_matching[t.offset] = Left{i};
                    left_covered[i] = 1;
                    break;
                }
            }
            if (! left_covered[i] && ! scratch.phantom_plus_one_of_var.empty())
                if (auto p = scratch.phantom_plus_one_of_var[i]; 0 != p && ! inverse_matching[p - 1]) {
                    matching[i] = Right{p - 1};
                    inverse_matching[p - 1] = Left{i};
                    left_covered[i] = 1;
                }
            if (left_covered[i])
                continue;

            // no free value: search for an augmenting path (which may leave i
            // uncovered, making the matching too small -- the caller detects
            // that)
            augment_from(n_right, i, scratch);
        }
    }

    auto prove_matching_is_too_small(const ConstraintID & constraint_id, const vector<IntegerVariableID> & vars, const vector<Integer> & vals,
        const vector<Integer> & excluded, size_t n_right, map<Integer, ProofLine> & value_am1_constraint_numbers, const State &, ProofLogger * const,
        GacAllDifferentScratch & scratch) -> std::tuple<hints::AllDifferentHall, Reason>
    {
        // build_matching maintains inverse_matching alongside the matching,
        // so it is already current here
        const auto & inverse_matching = scratch.inverse_matching;

        auto & hall_variables = scratch.hall_left;
        auto & hall_values = scratch.hall_right;
        hall_variables.assign(vars.size(), 0);
        hall_values.assign(n_right, 0);

        // there must be at least one thing uncovered, and this will
        // necessarily participate in a hall violator
        for (Left v{0}; v.offset != vars.size(); ++v.offset)
            if (! scratch.left_covered[v.offset]) {
                hall_variables[v.offset] = 1;
                break;
            }

        // either we have found a hall violator, or we have a spare value
        // on the right
        while (true) {
            auto & n_of_hall_variables = scratch.n_of_hall_variables;
            n_of_hall_variables.assign(n_right, 0);
            for (const auto & [l, r] : scratch.edges)
                if (hall_variables[l.offset])
                    n_of_hall_variables[r.offset] = 1;

            bool is_subset = true;
            Right not_subset_witness;
            for (Right v{0}; v.offset != n_right; ++v.offset)
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

        // these escape into the returned hint and lazy reason, so they are
        // deliberately fresh vectors, not scratch
        vector<IntegerVariableID> hall_variable_ids;
        for (Left v{0}; v.offset != vars.size(); ++v.offset)
            if (hall_variables[v.offset] && ! is_constant_variable(vars[v.offset]))
                hall_variable_ids.push_back(vars[v.offset]);

        vector<Integer> hall_value_nrs;
        for (Right v{0}; v.offset != vals.size(); ++v.offset)
            if (hall_values[v.offset])
                hall_value_nrs.push_back(vals[v.offset]);

        return tuple{hints::AllDifferentHall{{constraint_id}, hall_variable_ids, hall_value_nrs, &vars, &value_am1_constraint_numbers},
            Reason{LazyReasonOver{hall_variable_ids, //
                [hall_variable_ids, excluded](const State & st, ReasonLiterals & out) {
                    out = materialise(generic_reason(hall_variable_ids), st);
                    for (const auto & v : hall_variable_ids)
                        for (const auto & s : excluded)
                            out.emplace_back(v != s);
                }}}};
    }

    using Vertex = GacAllDifferentScratch::Vertex;

    // The two justification shapes a single SCC deletion can take: a Hall set (real
    // explicit steps) or a single forced value (pure RUP). A typed variant rather
    // than an optional, so each shape names itself and carries its own assertion
    // hint — there is no separate annotation channel.
    using DeletionJustification = variant<hints::AllDifferent, hints::AllDifferentHall>;

    // The concrete overloads let statically-typed call sites (which is most of
    // them) skip building a Vertex and dispatching on it; the Vertex overload
    // is only for genuinely variant vertices.
    auto vertex_to_offset(const vector<IntegerVariableID> &, const vector<Integer> &, const Left & l) -> std::size_t
    {
        return l.offset;
    }

    auto vertex_to_offset(const vector<IntegerVariableID> & vars, const vector<Integer> &, const Right & r) -> std::size_t
    {
        return vars.size() + r.offset;
    }

    auto vertex_to_offset(const vector<IntegerVariableID> & vars, const vector<Integer> & vals, const Vertex & v) -> std::size_t
    {
        return overloaded{
            [&](const Left & l) { return vertex_to_offset(vars, vals, l); }, //
            [&](const Right & r) { return vertex_to_offset(vars, vals, r); } //
        }
            .visit(v);
    }

    auto prove_deletion_using_sccs(const ConstraintID & constraint_id, const vector<IntegerVariableID> & vars, const vector<Integer> & vals,
        const vector<Integer> & excluded, size_t n_right, map<Integer, ProofLine> & value_am1_constraint_numbers, const State &, ProofLogger * const,
        const Right delete_value, GacAllDifferentScratch & scratch) -> tuple<DeletionJustification, Reason>
    {
        const auto & components = scratch.components;

        // we know a hall set exists, but we have to find it. starting
        // from but not including the end of the edge we're deleting,
        // everything reachable forms a hall set.
        auto & in_to_explore = scratch.in_to_explore;
        auto & to_explore = scratch.to_explore;
        auto & explored = scratch.explored;
        auto & hall_left = scratch.hall_left;
        auto & hall_right = scratch.hall_right;
        in_to_explore.assign(vars.size() + n_right, 0);
        to_explore.clear();
        explored.assign(vars.size() + n_right, 0);
        hall_left.assign(vars.size(), 0);
        hall_right.assign(n_right, 0);

        in_to_explore[vertex_to_offset(vars, vals, delete_value)] = 1;
        to_explore.push_back(delete_value);
        int care_about_scc = components[vertex_to_offset(vars, vals, delete_value)];
        while (! to_explore.empty()) {
            Vertex n = to_explore.back();
            to_explore.pop_back();
            auto n_offset = vertex_to_offset(vars, vals, n);
            in_to_explore[n_offset] = 0;
            explored[n_offset] = 1;

            visit(
                [&](const auto & x) -> void {
                    if constexpr (is_same_v<decay_t<decltype(x)>, Left>) {
                        hall_left[x.offset] = 1;
                        for_each_unmatched_edge_of_var(scratch, x.offset, [&](const Right & t) {
                            auto t_offset = vertex_to_offset(vars, vals, t);
                            if (care_about_scc == components[t_offset] && ! explored[t_offset]) {
                                if (0 == in_to_explore[t_offset]) {
                                    to_explore.push_back(t);
                                    in_to_explore[t_offset] = 1;
                                }
                            }
                        });
                    }
                    else {
                        hall_right[x.offset] = 1;
                        // a value's only out-edge is to its matched variable
                        if (const auto & t = scratch.inverse_matching[x.offset]) {
                            auto t_offset = vertex_to_offset(vars, vals, *t);
                            if (care_about_scc == components[t_offset] && ! explored[t_offset]) {
                                if (0 == in_to_explore[t_offset]) {
                                    to_explore.push_back(*t);
                                    in_to_explore[t_offset] = 1;
                                }
                            }
                        }
                    }
                },
                n);
        }

        // these escape into the returned hint and lazy reason, so they are
        // deliberately fresh vectors, not scratch
        vector<IntegerVariableID> hall_variable_ids;
        for (Left v{0}; v.offset != vars.size(); ++v.offset)
            if (hall_left[v.offset] && ! is_constant_variable(vars[v.offset]))
                hall_variable_ids.push_back(vars[v.offset]);

        if (hall_variable_ids.empty()) {
            // some other variable has been given this value
            if (! scratch.inverse_matching[delete_value.offset])
                throw UnexpectedException{"missing edge out from value in trivial scc"};

            return tuple{DeletionJustification{hints::AllDifferent{constraint_id}},
                Reason{ExplicitReason{ReasonLiterals{{vars[scratch.inverse_matching[delete_value.offset]->offset] == vals[delete_value.offset]}}}}};
        }
        else {
            // a hall set is at work
            vector<Integer> hall_value_nrs;
            for (Right v{0}; v.offset != vals.size(); ++v.offset)
                if (hall_right[v.offset])
                    hall_value_nrs.push_back(vals[v.offset]);

            return tuple{DeletionJustification{
                             hints::AllDifferentHall{{constraint_id}, hall_variable_ids, hall_value_nrs, &vars, &value_am1_constraint_numbers}},
                Reason{LazyReasonOver{hall_variable_ids, //
                    [hall_variable_ids, excluded](const State & st, ReasonLiterals & out) {
                        out = materialise(generic_reason(hall_variable_ids), st);
                        for (const auto & v : hall_variable_ids)
                            for (const auto & s : excluded)
                                out.emplace_back(v != s);
                    }}}};
        }
    }

    // Tarjan's algorithm, with an explicit stack of (vertex, resume position)
    // frames instead of a recursive std::function: no closure allocation, no
    // type-erased call per visit, and no deep native recursion on big graphs.
    // Successors are implicit: a left (variable) vertex walks its unmatched
    // edges -- the resume position indexes into edges, with
    // var_edges_begin[i + 1] standing for the phantom slot -- and a right
    // (value) vertex has just its matched variable (position 0 or 1). The
    // visit order matches what the old materialised adjacency produced, and
    // the numbering reproduces the recursive formulation exactly (including
    // taking min with the lowlink, not the index, of an on-stack target), so
    // component identifiers -- and hence everything downstream -- are
    // unchanged.
    auto find_strongly_connected_components(size_t vars_count, size_t n_vertices, GacAllDifferentScratch & scratch) -> int
    {
        auto & indices = scratch.indices;
        auto & lowlinks = scratch.lowlinks;
        auto & components = scratch.components;
        auto & stack = scratch.tarjan_stack;
        auto & enstackinated = scratch.enstackinated;
        auto & frames = scratch.tarjan_frames;

        indices.assign(n_vertices, 0);
        lowlinks.assign(n_vertices, 0);
        components.assign(n_vertices, 0);
        enstackinated.assign(n_vertices, 0);
        stack.clear();
        frames.clear();

        const auto start_pos = [&](size_t o) -> size_t { return o < vars_count ? scratch.var_edges_begin[o] : 0; };

        int next_index = 1, number_of_components = 0;

        for (size_t root = 0; root != n_vertices; ++root) {
            if (0 != indices[root])
                continue;

            frames.emplace_back(root, start_pos(root));
            while (! frames.empty()) {
                auto [v, pos] = frames.back();

                if (0 == indices[v]) {
                    // first arrival at v
                    indices[v] = next_index;
                    lowlinks[v] = next_index;
                    ++next_index;
                    stack.push_back(v);
                    enstackinated[v] = 1;
                }

                bool descended = false;
                if (v < vars_count) {
                    const auto & matched = scratch.matching[v];
                    const auto real_end = scratch.var_edges_begin[v + 1];
                    while (pos <= real_end) {
                        Right t{};
                        if (pos != real_end) {
                            t = scratch.edges[pos].second;
                            ++pos;
                            if (matched == t)
                                continue;
                        }
                        else {
                            // the phantom slot
                            ++pos;
                            if (scratch.phantom_plus_one_of_var.empty())
                                break;
                            auto p = scratch.phantom_plus_one_of_var[v];
                            if (0 == p)
                                break;
                            t = Right{p - 1};
                            if (matched == t)
                                break;
                        }
                        auto w = vars_count + t.offset;
                        if (0 == indices[w]) {
                            // descend into w; the min with w's lowlink happens
                            // when w's frame is popped, below
                            frames.back().second = pos;
                            frames.emplace_back(w, 0);
                            descended = true;
                            break;
                        }
                        else if (enstackinated[w])
                            lowlinks[v] = min(lowlinks[v], lowlinks[w]);
                    }
                }
                else if (0 == pos) {
                    ++pos;
                    if (auto l = scratch.inverse_matching[v - vars_count]) {
                        auto w = l->offset;
                        if (0 == indices[w]) {
                            frames.back().second = pos;
                            frames.emplace_back(w, start_pos(w));
                            descended = true;
                        }
                        else if (enstackinated[w])
                            lowlinks[v] = min(lowlinks[v], lowlinks[w]);
                    }
                }

                if (descended)
                    continue;

                frames.pop_back();
                if (lowlinks[v] == indices[v]) {
                    size_t w;
                    do {
                        w = stack.back();
                        stack.pop_back();
                        enstackinated[w] = 0;
                        components[w] = number_of_components;
                    } while (w != v);
                    ++number_of_components;
                }

                if (! frames.empty())
                    lowlinks[frames.back().first] = min(lowlinks[frames.back().first], lowlinks[v]);
            }
        }

        return number_of_components;
    }
}

auto gcs::innards::propagate_gac_all_different(const ConstraintID & constraint_id, const vector<IntegerVariableID> & vars,
    const vector<Integer> & vals, const vector<Integer> & excluded, map<Integer, ProofLine> & value_am1_constraint_numbers,
    GacAllDifferentScratch & scratch, const State & state, auto & tracker, ProofLogger * const logger) -> void
{
    // find a matching to check feasibility
    auto & edges = scratch.edges;
    edges.clear();

    if (! scratch.val_lookup_initialised) {
        // vals is fixed for an installed propagator, so decide once whether
        // to build the value -> index lookup. If the value set is too narrow
        // for the sweep to pay off, or too sparse for a dense table (see the
        // constants for both trade-offs), the lookup stays empty and every
        // wake takes the probe loop below instead.
        scratch.val_lookup_initialised = true;
        if (vals.size() >= min_vals_for_domain_sweep) {
            auto [min_it, max_it] = minmax_element(vals);
            auto span = (*max_it - *min_it).as_index() + 1;
            if (span <= dense_value_table_slots_per_value * vals.size() + dense_value_table_slots_slack) {
                scratch.val_lookup_min = *min_it;
                scratch.val_to_idx_plus_one.assign(span, 0);
                for (const auto & [val_idx, val] : enumerate(vals))
                    scratch.val_to_idx_plus_one[(val - *min_it).as_index()] = val_idx + 1;
            }
        }
    }

    auto & var_edges_begin = scratch.var_edges_begin;
    var_edges_begin.assign(vars.size() + 1, 0);

    if (! scratch.val_to_idx_plus_one.empty()) {
        // one sweep over each variable's actual domain marks which vals are
        // present, then edges are emitted in val-index order: the same edges
        // in the same order as the probe loop below, without paying a
        // vals.size() in_domain probe per variable. Domain values that aren't
        // in vals (all_different_except's excluded values) mark nothing.
        const auto min_val = scratch.val_lookup_min;
        const auto span = scratch.val_to_idx_plus_one.size();
        auto & vals_in_domain = scratch.vals_in_domain;
        for (const auto & [var_idx, var] : enumerate(vars)) {
            var_edges_begin[var_idx] = edges.size();
            vals_in_domain.assign(vals.size(), 0);
            state.for_each_value_immutable(var, [&](Integer val) -> void {
                if (val < min_val)
                    return;
                if (auto offset = (val - min_val).as_index(); offset < span)
                    if (auto val_idx_plus_one = scratch.val_to_idx_plus_one[offset]; 0 != val_idx_plus_one)
                        vals_in_domain[val_idx_plus_one - 1] = 1;
            });
            for (vector<Integer>::size_type val_idx = 0; val_idx != vals.size(); ++val_idx)
                if (vals_in_domain[val_idx])
                    edges.emplace_back(Left{var_idx}, Right{val_idx});
        }
    }
    else {
        for (const auto & [var_idx, var] : enumerate(vars)) {
            var_edges_begin[var_idx] = edges.size();
            for (const auto & [val_idx, val] : enumerate(vals))
                if (state.in_domain(var, val))
                    edges.emplace_back(Left{var_idx}, Right{val_idx});
        }
    }
    var_edges_begin[vars.size()] = edges.size();

    // Add a private phantom right-vertex per variable that has any excluded
    // value still in its current domain. The phantom edge represents "this
    // variable opts out of the alldifferent by taking an excluded value", so
    // it can absorb any one variable freely. Phantom right offsets live past
    // vals.size(); they sit after the var-major real section of edges, so
    // per-variable ownership is tracked separately for the implicit
    // adjacency.
    auto n_right = vals.size();
    if (! excluded.empty()) {
        scratch.phantom_plus_one_of_var.assign(vars.size(), 0);
        for (const auto & [var_idx, var] : enumerate(vars))
            for (const auto & s : excluded)
                if (state.in_domain(var, s)) {
                    edges.emplace_back(Left{var_idx}, Right{n_right});
                    scratch.phantom_plus_one_of_var[var_idx] = n_right + 1;
                    ++n_right;
                    break;
                }
    }
    else
        scratch.phantom_plus_one_of_var.clear();

    // Reuse the previous wake's matching (after revalidation) except when
    // there are excluded values: phantom right offsets are renumbered per
    // wake, so a stale phantom match would be meaningless.
    build_matching(vars, n_right, excluded.empty(), scratch);

    const auto & matching = scratch.matching;

    if (cmp_not_equal(count(scratch.left_covered.begin(), scratch.left_covered.end(), 1), vars.size())) {
        // nope. we've got a maximum cardinality matching that leaves at least
        // one thing on the left uncovered.
        auto [hall, reason] =
            prove_matching_is_too_small(constraint_id, vars, vals, excluded, n_right, value_am1_constraint_numbers, state, logger, scratch);
        return tracker.infer(logger, FalseLiteral{},
            JustifyExplicitly{[&logger, w = hall](const ReasonLiterals & r) { emit_justification(*logger, w, r); }, ThenRUP::Yes, move(hall)},
            reason);
    }

    // we have a matching that uses every variable. however, some edges may
    // not occur in any maximum cardinality matching, and we can delete these.
    // The directed matching graph is implicit in edges + the matching; only
    // the unmatched value -> variables transpose is materialised, for the
    // backwards used-edge sweep, along with value -> matched variable.
    auto & edges_in_to_value = scratch.edges_in_to_value;
    clear_inners_to_size(edges_in_to_value, n_right);
    for (auto & [f, t] : edges)
        if (matching[f.offset] != t)
            edges_in_to_value[t.offset].push_back(f);

    // now we need to find strongly connected components...
    const auto number_of_components = find_strongly_connected_components(vars.size(), vars.size() + n_right, scratch);
    const auto & components = scratch.components;

    // every edge in the original matching is used, and so cannot be
    // deleted. used_edges only tracks real (non-phantom) right offsets;
    // phantom edges are never deletable and are skipped below.
    auto & used_edges = scratch.used_edges;
    used_edges.assign(vars.size() * vals.size(), 0);
    const auto used_edge_idx = [&](size_t l, size_t r) { return l * vals.size() + r; };
    for (const auto & [l, r] : enumerate(matching))
        if (r && r->offset < vals.size())
            used_edges[used_edge_idx(l, r->offset)] = 1;

    // for each unmatched vertex, bring in everything that could be updated
    // to take it. Phantom rights participate too (when their owner is
    // matched to a real value, the phantom is unmatched and its presence
    // here marks the owner's edges as redirectable).
    {
        auto & to_explore = scratch.to_explore;
        auto & in_to_explore = scratch.in_to_explore;
        auto & explored = scratch.explored;
        to_explore.clear();
        in_to_explore.assign(vars.size() + n_right, 0);
        explored.assign(vars.size() + n_right, 0);

        for (Right v{0}; v.offset != n_right; ++v.offset)
            in_to_explore[vertex_to_offset(vars, vals, v)] = 1;

        for (auto & t : matching)
            if (t)
                in_to_explore[vertex_to_offset(vars, vals, *t)] = 0;

        for (Left v{0}; v.offset != vars.size(); ++v.offset)
            if (in_to_explore[vertex_to_offset(vars, vals, v)])
                to_explore.push_back(v);

        for (Right v{0}; v.offset != n_right; ++v.offset)
            if (in_to_explore[vertex_to_offset(vars, vals, v)])
                to_explore.push_back(v);

        while (! to_explore.empty()) {
            Vertex v = to_explore.back();
            to_explore.pop_back();
            auto v_offset = vertex_to_offset(vars, vals, v);
            in_to_explore[v_offset] = 0;
            explored[v_offset] = 1;

            visit(
                [&](const auto & x) {
                    if constexpr (is_same_v<decay_t<decltype(x)>, Left>) {
                        // a variable's only in-edge is from its matched value
                        if (const auto & t = matching[x.offset]) {
                            if (t->offset < vals.size())
                                used_edges[used_edge_idx(x.offset, t->offset)] = 1;
                            auto t_offset = vertex_to_offset(vars, vals, *t);
                            if (! explored[t_offset]) {
                                if (! in_to_explore[t_offset]) {
                                    to_explore.push_back(*t);
                                    in_to_explore[t_offset] = 1;
                                }
                            }
                        }
                    }
                    else {
                        for (auto & t : edges_in_to_value[x.offset]) {
                            if (x.offset < vals.size())
                                used_edges[used_edge_idx(t.offset, x.offset)] = 1;
                            auto t_offset = vertex_to_offset(vars, vals, t);
                            if (! explored[t_offset]) {
                                if (! in_to_explore[t_offset]) {
                                    to_explore.push_back(t);
                                    in_to_explore[t_offset] = 1;
                                }
                            }
                        }
                    }
                },
                v);
        }
    }

    // every edge that starts and ends in the same component is also used
    // (skipping phantom edges, which never appear in used_edges)
    for (auto & [f, t] : edges)
        if (t.offset < vals.size() && components[vertex_to_offset(vars, vals, f)] == components[vertex_to_offset(vars, vals, t)])
            used_edges[used_edge_idx(f.offset, t.offset)] = 1;

    // anything left can be deleted. need to do all of these together if we're doing
    // justifications, to avoid having to figure out an ordering for nested Hall sets.
    // Phantom edges are skipped: they're never deletable.
    auto & deletions_by_scc = scratch.deletions_by_scc;
    auto & representatives_for_scc = scratch.representatives_for_scc;
    clear_inners_to_size(deletions_by_scc, number_of_components);
    representatives_for_scc.assign(number_of_components, nullopt);
    for (auto & [delete_var_name, delete_value] : edges) {
        if (delete_value.offset >= vals.size())
            continue;
        if (used_edges[used_edge_idx(delete_var_name.offset, delete_value.offset)])
            continue;
        auto scc = components[vertex_to_offset(vars, vals, delete_value)];
        deletions_by_scc[scc].emplace_back(vars[delete_var_name.offset] != vals[delete_value.offset]);
        representatives_for_scc[scc] = delete_value;
    }

    for (int scc = 0; scc < number_of_components; ++scc) {
        if (! representatives_for_scc[scc])
            continue;

        auto [justification, reason] = prove_deletion_using_sccs(
            constraint_id, vars, vals, excluded, n_right, value_am1_constraint_numbers, state, logger, *representatives_for_scc[scc], scratch);
        visit(
            overloaded{
                [&](hints::AllDifferent & w) { tracker.infer_all(logger, deletions_by_scc[scc], JustifyUsingRUP{w}, reason); }, //
                [&](hints::AllDifferentHall & w) {
                    tracker.infer_all(logger, deletions_by_scc[scc],
                        JustifyExplicitly{[&logger, wc = w](const ReasonLiterals & r) { emit_justification(*logger, wc, r); }, ThenRUP::Yes, move(w)},
                        reason);
                } //
            },
            justification);
    }
}

template auto gcs::innards::propagate_gac_all_different(const ConstraintID & constraint_id, const std::vector<IntegerVariableID> & vars,
    const std::vector<Integer> & vals, const std::vector<Integer> & excluded, std::map<Integer, ProofLine> & value_am1_constraint_numbers,
    GacAllDifferentScratch & scratch, const State & state, SimpleInferenceTracker & inference_tracker, ProofLogger * const logger) -> void;

template auto gcs::innards::propagate_gac_all_different(const ConstraintID & constraint_id, const std::vector<IntegerVariableID> & vars,
    const std::vector<Integer> & vals, const std::vector<Integer> & excluded, std::map<Integer, ProofLine> & value_am1_constraint_numbers,
    GacAllDifferentScratch & scratch, const State & state, EagerProofLoggingInferenceTracker & inference_tracker, ProofLogger * const logger) -> void;
