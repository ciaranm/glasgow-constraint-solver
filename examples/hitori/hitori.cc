#include <gcs/constraints/all_different.hh>
#include <gcs/constraints/element.hh>
#include <gcs/constraints/equals.hh>
#include <gcs/constraints/linear.hh>
#include <gcs/constraints/logical.hh>
#include <gcs/constraints/reachable.hh>
#include <gcs/problem.hh>
#include <gcs/search_heuristics.hh>
#include <gcs/solve.hh>

#include <examples/benchmark_cli.hh>
#include <examples/dzn.hh>

#include <algorithm>
#include <cstddef>
#include <cstdlib>
#include <exception>
#include <iostream>
#include <memory>
#include <optional>
#include <random>
#include <string>
#include <utility>
#include <vector>

#include <cxxopts.hpp>

#include <version>

#if defined(__cpp_lib_print) && defined(__cpp_lib_format)
#include <format>
#include <print>
#else
#include <fmt/core.h>
#include <fmt/ostream.h>
#endif

using namespace gcs;

using gcs::innards::Literals;
using gcs::innards::TrueLiteral;

using std::cerr;
using std::cout;
using std::endl;
using std::make_optional;
using std::make_shared;
using std::mt19937;
using std::nullopt;
using std::optional;
using std::pair;
using std::random_device;
using std::size_t;
using std::string;
using std::swap;
using std::uniform_int_distribution;
using std::vector;
using std::ranges::find;

#if defined(__cpp_lib_print) && defined(__cpp_lib_format)
using std::format;
using std::print;
using std::println;
#else
using fmt::format;
using fmt::print;
using fmt::println;
#endif

// Hitori (https://www.puzzle-hitori.com/): shade cells of an n-by-n grid of
// clues so that no value repeats among the unshaded cells of any row or
// column, no two shaded cells are orthogonally adjacent, and the unshaded
// cells stay orthogonally connected. Here the shading is scored, and we
// maximise the total clue value of the shaded cells.
//
// This is a port of the MiniZinc Challenge 2025 `hitori` model
// (2025/hitori/hitori.mzn), posted natively so the proof-benchmark set does
// not have to go through the MiniZinc frontend to reach a realistic model that
// writes a gigabyte of proof (issue #634). What the flattened model actually
// asks the solver for is:
//
//   * `x[r][c]`, the "value seen at this cell", which is 0 when the cell is
//     shaded and the clue otherwise, with `alldifferent_except_0` over each
//     row and column of `x` -- AllDifferentExceptZero here;
//   * a clause per orthogonally adjacent pair forbidding both being shaded;
//   * `connected(from, to, ns, es)` from `globals.mzn` over the grid graph,
//     with node `ns[i]` in the subgraph iff cell `i` is unshaded and edge
//     `es[e]` in iff both its endpoints are;
//   * a batch of implied and symmetry-breaking constraints that are decided
//     entirely by the clues, so they only fix cells (see forced_cells);
//   * `maximize sum(r, c)(filled[r][c] * clue[r][c])`.
//
// The model's commented-out `count` block is not part of it, so `Count` never
// appears; `arg_max` is used at parameter level only, at model-build time.
//
// Connectivity is the interesting part, because gcs has no `connected`
// propagator, and the point of this example is to reproduce the proof that the
// MiniZinc route produces rather than to find a better encoding. So we
// reproduce the stdlib decomposition that `fzn-glasgow` is handed, which is
// `connected` -> `fzn_connected` -> `reachable` (from a variable root, over
// the edge set doubled into both directions) -> `fzn_dreachable`, i.e. a
// spanning-tree-with-distances encoding over the selected nodes:
//
//   * a root node `root`, which must be unshaded and at distance 0;
//   * `dist[i]` in 0..n*n-1 and `parent[i]` in 1..n*n per node, where
//     `parent[i] = i` encodes "no parent" (this is how the flattener spells
//     `fzn_dreachable`'s `parent[i] = 0`, having folded away the partial array
//     accesses `ns[parent[i]]` and `dist[parent[i]]`);
//   * a shaded node has no parent and distance 0; an unshaded node is the root
//     or has a parent; a node with a parent is unshaded, has an unshaded
//     parent, is one deeper than its parent, and its parent is one of its grid
//     neighbours.
//
// The `subgraph` half of `fzn_dreachable` is vacuous for this model, because
// `es[e]` is defined as the conjunction of its endpoints' `ns`, so it is not
// posted. The flattener also posts `parent[root] = root`, which is implied
// (the root is at distance 0 and a child is one deeper than its parent) but
// which we post too, to keep the same propagation.
//
// That encoding lives behind `--connectivity`, following the `--variant` seam
// of examples/p_dispersion. `--connectivity decomposition` is the default and
// is what the benchmark entry measures. `--connectivity propagator` posts the
// same requirement through the native `Reachable` propagator of issue #637
// instead, so one binary can run the same instance through a decomposition and
// through a global propagator. `--connectivity none` is a *relaxation*, not a
// solving mode: it drops the connectivity requirement altogether, so it does
// not solve hitori and generally reports a larger objective. It is here for
// proof attribution --- running with and without it and diffing the proofs
// says how much of the proof the connectivity decomposition is responsible
// for, which is what sized #637.
//
// gcs minimises, so `maximise` negates: a VeriPB verdict of
// `s VERIFIED BOUNDS -17 <= obj <= -17` means an optimum of 17.
//
// Instances come either from `--dzn` (a MiniZinc Challenge `h*.dzn` file, so
// the exact Challenge instances stay reproducible) or, by default, from the
// built-in generator reached by `--size` and `--seed`. NOTE: the generator is
// not a puzzle generator. It produces a grid that is guaranteed to admit at
// least one valid shading, but makes no attempt at a unique solution, which a
// human hitori puzzle would have; uniqueness is irrelevant here, since this is
// an optimisation problem over all valid shadings.

namespace
{
    struct Instance
    {
        string name;
        int n;
        vector<vector<int>> clue; // clue[r][c], values in 1..n, zero-based
    };

    auto print_grid_of(const Instance & instance) -> void
    {
        println("% {}", instance.name);
        for (int r = 0; r < instance.n; ++r) {
            for (int c = 0; c < instance.n; ++c)
                print("{}{}", c == 0 ? "" : ",", instance.clue[r][c]);
            println("");
        }
    }

    // Build a grid that is guaranteed to admit at least one valid shading, in
    // the spirit of the nonogram example's picture-then-clues generator: pick a
    // shading first, then clue the grid so that the shading works.
    //
    // The shading is a random independent set in the grid graph whose
    // complement is connected (built by growing the shaded set one cell at a
    // time and keeping only cells that leave the rest connected). The unshaded
    // cells are then clued from a random Latin square, so they are
    // automatically distinct within every row and column, and the shaded cells
    // are clued afterwards. `duplicates` is the probability that a shaded cell
    // repeats a value already in its row or column rather than taking a uniform
    // value: repeated values are what forces shading, so this is the knob for
    // how constrained the instance is.
    auto random_instance(int n, unsigned seed, double density, double duplicates) -> Instance
    {
        mt19937 rng(seed);
        auto coin = [&](double p) { return uniform_int_distribution<int>(1, 1000000)(rng) <= static_cast<int>(p * 1000000); };
        auto num_nodes = n * n;

        vector<bool> shaded(num_nodes, false);

        // Is the unshaded set connected, if `extra` were also shaded?
        auto unshaded_connected = [&](int extra) {
            vector<bool> seen(num_nodes, false);
            int start = -1, want = 0;
            for (int i = 0; i < num_nodes; ++i)
                if (! shaded[i] && i != extra) {
                    ++want;
                    if (start == -1)
                        start = i;
                }
            if (start == -1)
                return true;
            vector<int> stack{start};
            seen[start] = true;
            int found = 0;
            while (! stack.empty()) {
                auto i = stack.back();
                stack.pop_back();
                ++found;
                auto r = i / n, c = i % n;
                auto push = [&](int rr, int cc) {
                    auto j = rr * n + cc;
                    if (rr >= 0 && rr < n && cc >= 0 && cc < n && ! shaded[j] && j != extra && ! seen[j]) {
                        seen[j] = true;
                        stack.push_back(j);
                    }
                };
                push(r, c - 1);
                push(r - 1, c);
                push(r, c + 1);
                push(r + 1, c);
            }
            return found == want;
        };

        vector<int> order(num_nodes);
        for (int i = 0; i < num_nodes; ++i)
            order[i] = i;
        for (int i = num_nodes - 1; i > 0; --i)
            swap(order[i], order[uniform_int_distribution<int>(0, i)(rng)]);

        for (auto i : order) {
            if (! coin(density))
                continue;
            auto r = i / n, c = i % n;
            auto adjacent_shaded =
                (c > 0 && shaded[i - 1]) || (c + 1 < n && shaded[i + 1]) || (r > 0 && shaded[i - n]) || (r + 1 < n && shaded[i + n]);
            if (adjacent_shaded || ! unshaded_connected(i))
                continue;
            shaded[i] = true;
        }

        // A random Latin square, by randomised row-at-a-time completion with a
        // restart if a row cannot be finished. Every row and column of it holds
        // each of 1..n exactly once, so any set of cells is row- and
        // column-distinct.
        vector<vector<int>> latin;
        for (bool built = false; ! built;) {
            latin.assign(n, vector<int>(n, 0));
            built = true;
            for (int r = 0; r < n && built; ++r) {
                vector<int> values(n);
                for (int v = 0; v < n; ++v)
                    values[v] = v + 1;
                for (int c = 0; c < n; ++c) {
                    vector<int> usable;
                    for (auto v : values) {
                        bool clash = false;
                        for (int rr = 0; rr < r; ++rr)
                            clash = clash || latin[rr][c] == v;
                        if (! clash)
                            usable.push_back(v);
                    }
                    if (usable.empty()) {
                        built = false;
                        break;
                    }
                    auto v = usable[uniform_int_distribution<size_t>(0, usable.size() - 1)(rng)];
                    latin[r][c] = v;
                    values.erase(find(values, v));
                }
            }
        }

        vector<vector<int>> clue(n, vector<int>(n, 0));
        for (int r = 0; r < n; ++r)
            for (int c = 0; c < n; ++c)
                if (! shaded[r * n + c])
                    clue[r][c] = latin[r][c];

        for (int r = 0; r < n; ++r)
            for (int c = 0; c < n; ++c) {
                if (! shaded[r * n + c])
                    continue;
                vector<int> nearby;
                for (int k = 0; k < n; ++k) {
                    if (k != c && clue[r][k] != 0)
                        nearby.push_back(clue[r][k]);
                    if (k != r && clue[k][c] != 0)
                        nearby.push_back(clue[k][c]);
                }
                clue[r][c] = (nearby.empty() || ! coin(duplicates)) ? uniform_int_distribution<int>(1, n)(rng)
                                                                    : nearby[uniform_int_distribution<size_t>(0, nearby.size() - 1)(rng)];
            }

        return Instance{format("random-{}-{}", n, seed), n, clue};
    }

    // Read a MiniZinc Challenge hitori data file: `n = N;` and a `clue` matrix
    // written in dzn's `[| a, b | c, d |]` form.
    auto read_dzn(const string & path) -> optional<Instance>
    {
        try {
            auto data = dzn::read(path);

            auto n = static_cast<int>(data.integer("n"));
            if (n <= 0) {
                cerr << "dzn file gives n = " << n << ", which is not a grid size: " << path << endl;
                return nullopt;
            }

            // Reading the matrix as a matrix rather than flat is what makes the
            // shape check below possible: a clue array of the wrong size used
            // to be taken n * n entries at a time regardless.
            auto rows = data.matrix("clue");
            if (static_cast<int>(rows.size()) != n) {
                cerr << "dzn file gives a clue grid of " << rows.size() << " rows for n = " << n << ": " << path << endl;
                return nullopt;
            }

            // One width check covers every row, because matrix() has already
            // refused a literal whose rows are not all the same length.
            if (static_cast<int>(rows.front().size()) != n) {
                cerr << "dzn file gives " << rows.front().size() << " clues per row for n = " << n << ": " << path << endl;
                return nullopt;
            }

            vector<vector<int>> clue(n, vector<int>(n, 0));
            for (int r = 0; r < n; ++r)
                for (int c = 0; c < n; ++c)
                    clue[r][c] = static_cast<int>(rows[r][c]);
            return Instance{path, n, clue};
        }
        catch (const std::exception & e) {
            cerr << "Error reading the instance: " << e.what() << endl;
            return nullopt;
        }
    }

    // The model's implied and symmetry-breaking constraints. Every one of them
    // is decided by the clues alone, so each either fixes a cell or does
    // nothing; the MiniZinc flattener resolves them the same way, before the
    // solver ever sees the model.
    //
    //   * if two horizontally or vertically adjacent clues are equal then
    //     exactly one of the pair is shaded (adjacency forbids both, and
    //     alldifferent-except-0 forbids neither), so every *other* cell of that
    //     line holding the same value must be shaded. The model reads the
    //     first such pair off with `arg_max`;
    //   * if the clues either side of a cell in a line are equal then one of
    //     them is shaded, so the cell between them cannot be;
    //   * in each corner, three equal clues in an L force the corner to be
    //     shaded, else the corner would be cut off from the rest.
    // Which cells the clues alone decide. Kept as two independent grids rather
    // than one tri-state, because a clue grid can force a cell both ways: that
    // means it admits no valid shading at all, and posting both constraints is
    // what makes the model say so, exactly as the MiniZinc one does.
    struct ForcedCells
    {
        vector<vector<bool>> shade;
        vector<vector<bool>> leave;
    };

    auto forced_cells(const Instance & instance) -> ForcedCells
    {
        auto n = instance.n;
        const auto & clue = instance.clue;
        ForcedCells forced{vector<vector<bool>>(n, vector<bool>(n, false)), vector<vector<bool>>(n, vector<bool>(n, false))};

        for (int r = 0; r < n; ++r) {
            int first = n - 1;
            for (int c = 0; c + 1 < n; ++c)
                if (clue[r][c] == clue[r][c + 1]) {
                    first = c;
                    break;
                }
            if (first + 1 < n)
                for (int c = 0; c < n; ++c)
                    if (c != first && c != first + 1 && clue[r][c] == clue[r][first])
                        forced.shade[r][c] = true;
        }

        for (int c = 0; c < n; ++c) {
            int first = n - 1;
            for (int r = 0; r + 1 < n; ++r)
                if (clue[r][c] == clue[r + 1][c]) {
                    first = r;
                    break;
                }
            if (first + 1 < n)
                for (int r = 0; r < n; ++r)
                    if (r != first && r != first + 1 && clue[r][c] == clue[first][c])
                        forced.shade[r][c] = true;
        }

        for (int r = 1; r + 1 < n; ++r)
            for (int c = 0; c < n; ++c)
                if (clue[r - 1][c] == clue[r + 1][c])
                    forced.leave[r][c] = true;

        for (int r = 0; r < n; ++r)
            for (int c = 1; c + 1 < n; ++c)
                if (clue[r][c - 1] == clue[r][c + 1])
                    forced.leave[r][c] = true;

        if (n >= 2) {
            if (clue[0][0] == clue[0][1] && clue[0][0] == clue[1][0])
                forced.shade[0][0] = true;
            if (clue[0][n - 1] == clue[0][n - 2] && clue[0][n - 1] == clue[1][n - 1])
                forced.shade[0][n - 1] = true;
            if (clue[n - 1][0] == clue[n - 1][1] && clue[n - 1][0] == clue[n - 2][0])
                forced.shade[n - 1][0] = true;
            if (clue[n - 1][n - 1] == clue[n - 2][n - 1] && clue[n - 1][n - 1] == clue[n - 1][n - 2])
                forced.shade[n - 1][n - 1] = true;
        }

        return forced;
    }

    // How the "the unshaded cells stay connected" requirement is posted: the
    // mznlib decomposition, the native Reachable propagator of issue #637, or
    // nothing at all. Both real encodings stay reachable from here, so the
    // decomposition-versus-propagator comparison can be made on one instance in
    // one binary --- see the `--variant` seam of examples/p_dispersion.
    enum class Connectivity
    {
        Decomposition,    // the mznlib decomposition; the default, and the one the benchmark entry is about
        Propagator,       // the native Reachable propagator from issue #637, at its default strength
        PropagatorNoCuts, // the same propagator with its cut-vertex and bridge forcing turned off
        None              // a relaxation: solves a different problem, for proof attribution only
    };

    // Constrain the unshaded cells --- node i is unshaded iff `ns[i]` is 1,
    // over the n-by-n grid graph in row-major order --- to be connected.
    // Returns the variables the encoding introduces that the model's search
    // should treat as its own, i.e. that FlatZinc would not mark
    // `is_defined_var`.
    auto post_connectivity(Problem & p, int n, const vector<IntegerVariableID> & ns, Connectivity variant) -> vector<IntegerVariableID>
    {
        auto num_nodes = n * n;
        vector<IntegerVariableID> introduced;

        switch (variant) {
            using enum Connectivity;
        case None:
            // Deliberately post nothing: the relaxation.
            return introduced;

        case Propagator:
        case PropagatorNoCuts: {
            // The same `connected` requirement, handed to the native Reachable
            // propagator instead of being flattened. `connected` is `reachable`
            // with the root existentially quantified, so the root variable is
            // created here exactly as `fzn_connected`'s `let` does; edges run
            // right and down out of each cell, and `es[e]` is the conjunction of
            // its endpoints, as in the MiniZinc model.
            vector<pair<size_t, size_t>> edges;
            for (int i = 0; i < num_nodes; ++i) {
                auto r = i / n, c = i % n;
                if (c + 1 < n)
                    edges.emplace_back(i, i + 1);
                if (r + 1 < n)
                    edges.emplace_back(i, i + n);
            }

            vector<IntegerVariableID> es;
            for (const auto & [u, v] : edges) {
                auto edge_in = p.create_integer_variable(0_i, 1_i, format("edge[{}_{}]", u, v));
                p.post(And{Literals{{ns[u] == 1_i, ns[v] == 1_i}}, edge_in == 1_i});
                es.push_back(edge_in);
            }

            auto root = p.create_integer_variable(0_i, Integer{num_nodes - 1}, "root");
            // The forcing is what makes Reachable GAC, and it cuts this search by
            // about two and a half times --- but `connected` leaves the root
            // existentially quantified, and a forcing made before search has
            // decided the root costs one proof line per candidate root. On h11-1
            // that is 7x the proof for 2.5x the search, so the two settings are
            // both kept measurable rather than one being chosen here.
            p.post(Reachable{move(edges), root, ns, move(es)}.with_cut_forcing(variant == Connectivity::Propagator));

            // The root is the only variable here that search has to decide: the
            // edges follow from their endpoints, as `is_defined_var` would say.
            introduced.push_back(root);
            return introduced;
        }

        case Decomposition: break;
        }

        // Nodes are numbered 1..n*n in row-major order, matching the MiniZinc
        // model, so every array index below starts at 1.
        auto root = p.create_integer_variable(1_i, Integer{num_nodes}, "root");
        auto dist = p.create_integer_variable_vector(num_nodes, 0_i, Integer{num_nodes - 1}, "dist");
        auto parent = p.create_integer_variable_vector(num_nodes, 1_i, Integer{num_nodes}, "parent");

        auto ns_array = make_shared<const vector<IntegerVariableID>>(ns);
        auto dist_array = make_shared<const vector<IntegerVariableID>>(dist);
        auto parent_array = make_shared<const vector<IntegerVariableID>>(parent);

        // the root is unshaded, is at distance 0, and has no parent
        p.post(Element{1_c, pair{root, 1_i}, ns_array});
        p.post(Element{0_c, pair{root, 1_i}, dist_array});
        p.post(Element{root, pair{root, 1_i}, parent_array});

        for (int i = 0; i < num_nodes; ++i) {
            auto node = Integer{i + 1};
            auto r = i / n, c = i % n;

            auto no_parent = p.create_integer_variable(0_i, 1_i, format("no_parent[{}]", i + 1));
            p.post(EqualsIff{parent[i], constant_variable(node), no_parent == 1_i});
            auto is_root = p.create_integer_variable(0_i, 1_i, format("is_root[{}]", i + 1));
            p.post(EqualsIff{root, constant_variable(node), is_root == 1_i});

            // a shaded node is out of the subgraph, so has no parent and no distance
            p.post(Or{Literals{{no_parent == 1_i, ns[i] == 1_i}}, TrueLiteral{}});
            p.post(EqualsIf{dist[i], 0_c, ns[i] == 0_i});

            // an unshaded node is the root, or has a parent
            p.post(Or{Literals{{no_parent == 0_i, is_root == 1_i, ns[i] == 0_i}}, TrueLiteral{}});

            // a node with a parent is unshaded, and so is its parent
            auto parent_unshaded = p.create_integer_variable(0_i, 1_i, format("parent_unshaded[{}]", i + 1));
            p.post(Element{parent_unshaded, pair{parent[i], 1_i}, ns_array});
            auto both_unshaded = p.create_integer_variable(0_i, 1_i, format("both_unshaded[{}]", i + 1));
            p.post(And{Literals{{parent_unshaded == 1_i, ns[i] == 1_i}}, both_unshaded == 1_i});
            p.post(Or{Literals{{both_unshaded == 1_i, no_parent == 1_i}}, TrueLiteral{}});

            // a node with a parent is one deeper than its parent
            auto parent_dist = p.create_integer_variable(0_i, Integer{num_nodes - 1}, format("parent_dist[{}]", i + 1));
            p.post(Element{parent_dist, pair{parent[i], 1_i}, dist_array});
            auto one_deeper = p.create_integer_variable(0_i, 1_i, format("one_deeper[{}]", i + 1));
            p.post(LinearEqualityIff{WeightedSum{} + 1_i * dist[i] + -1_i * parent_dist, 1_i, one_deeper == 1_i});
            p.post(Or{Literals{{one_deeper == 1_i, no_parent == 1_i}}, TrueLiteral{}});

            // a node with a parent reaches it along an edge of the subgraph,
            // i.e. its parent is an unshaded grid neighbour. Neighbours are
            // taken left, up, right, down, which is the order the doubled edge
            // array of `fzn_reachable` puts them in.
            Literals from_neighbour;
            for (auto [nr, nc] : {pair{r, c - 1}, pair{r - 1, c}, pair{r, c + 1}, pair{r + 1, c}}) {
                if (nr < 0 || nr >= n || nc < 0 || nc >= n)
                    continue;
                auto neighbour = nr * n + nc;
                auto parent_is = p.create_integer_variable(0_i, 1_i, format("parent[{}]_is_{}", i + 1, neighbour + 1));
                p.post(EqualsIff{parent[i], constant_variable(Integer{neighbour + 1}), parent_is == 1_i});
                auto edge_in = p.create_integer_variable(0_i, 1_i, format("edge_{}_{}", neighbour + 1, i + 1));
                p.post(And{Literals{{parent_is == 1_i, ns[i] == 1_i, ns[neighbour] == 1_i}}, edge_in == 1_i});
                from_neighbour.push_back(edge_in == 1_i);
            }
            from_neighbour.push_back(no_parent == 1_i);
            p.post(Or{from_neighbour, TrueLiteral{}});
        }

        introduced.push_back(root);
        introduced.insert(introduced.end(), dist.begin(), dist.end());
        introduced.insert(introduced.end(), parent.begin(), parent.end());
        return introduced;
    }

    auto solve_hitori(const Instance & instance, Connectivity connectivity, bool print_solutions, double timeout,
        const optional<string> & proof_basename) -> pair<Stats, optional<long long>>
    {
        auto n = instance.n;
        const auto & clue = instance.clue;

        Problem p;

        // filled[r][c] is 1 iff the cell is shaded, and unfilled[r][c] is its
        // negation, which is `ns`, the node-in-subgraph array of `connected`.
        vector<vector<IntegerVariableID>> filled, unfilled, x;
        for (int r = 0; r < n; ++r) {
            filled.emplace_back(p.create_integer_variable_vector(n, 0_i, 1_i, format("filled[{}]", r)));
            unfilled.emplace_back(p.create_integer_variable_vector(n, 0_i, 1_i, format("unfilled[{}]", r)));
            x.emplace_back();
            for (int c = 0; c < n; ++c)
                x.back().push_back(p.create_integer_variable(0_i, Integer{clue[r][c]}, format("x[{}][{}]", r, c)));
        }

        auto forced = forced_cells(instance);
        for (int r = 0; r < n; ++r)
            for (int c = 0; c < n; ++c) {
                p.post(NotEquals{filled[r][c], unfilled[r][c]});
                // x is 0 where the cell is shaded, and the clue where it is not
                p.post(EqualsIf{x[r][c], 0_c, filled[r][c] == 1_i});
                p.post(EqualsIf{x[r][c], constant_variable(Integer{clue[r][c]}), filled[r][c] == 0_i});
                if (forced.shade[r][c])
                    p.post(Equals{filled[r][c], 1_c});
                if (forced.leave[r][c])
                    p.post(Equals{filled[r][c], 0_c});
            }

        // no value repeats among the unshaded cells of a row or column
        for (int r = 0; r < n; ++r)
            p.post(AllDifferentExceptZero{x[r]});
        for (int c = 0; c < n; ++c) {
            vector<IntegerVariableID> column;
            for (int r = 0; r < n; ++r)
                column.push_back(x[r][c]);
            p.post(AllDifferentExceptZero{column});
        }

        // no two shaded cells are adjacent
        for (int r = 0; r < n; ++r)
            for (int c = 0; c < n; ++c) {
                if (c + 1 < n)
                    p.post(Or{Literals{{filled[r][c] == 0_i, filled[r][c + 1] == 0_i}}, TrueLiteral{}});
                if (r + 1 < n)
                    p.post(Or{Literals{{filled[r][c] == 0_i, filled[r + 1][c] == 0_i}}, TrueLiteral{}});
            }

        // the unshaded cells stay connected (see post_connectivity)
        vector<IntegerVariableID> ns;
        for (int r = 0; r < n; ++r)
            for (int c = 0; c < n; ++c)
                ns.push_back(unfilled[r][c]);
        auto connectivity_vars = post_connectivity(p, n, ns, connectivity);

        // maximise the total clue value of the shaded cells
        long long total_clue = 0;
        WeightedSum objective;
        for (int r = 0; r < n; ++r)
            for (int c = 0; c < n; ++c) {
                total_clue += clue[r][c];
                objective += Integer{clue[r][c]} * filled[r][c];
            }
        auto obj = p.create_integer_variable(0_i, Integer{total_clue}, "obj");
        objective += -1_i * obj;
        p.post(LinearEquality{objective, 0_i});
        p.maximise(obj);

        // Branch the way the model's `bool_search(filled, input_order,
        // indomain_max)` annotation asks: shade-first, in reading order. Then
        // fall back to dom-then-deg, first over the variables the model itself
        // declares and then over the ones the decompositions introduced, which
        // is what fzn-glasgow does with FlatZinc's `is_defined_var`.
        vector<IntegerVariableID> shading, model_vars;
        for (int r = 0; r < n; ++r)
            for (int c = 0; c < n; ++c)
                shading.push_back(filled[r][c]);
        model_vars = shading;
        for (int r = 0; r < n; ++r)
            for (int c = 0; c < n; ++c)
                model_vars.push_back(x[r][c]);
        model_vars.insert(model_vars.end(), connectivity_vars.begin(), connectivity_vars.end());

        auto brancher = branch_sequence(                                               //
            branch_with(variable_order::in_order(shading), value_order::largest_in()), //
            branch_sequence(                                                           //
                branch_with(variable_order::dom_then_deg(model_vars), value_order::smallest_first()),
                branch_with(variable_order::dom_then_deg(p), value_order::smallest_first())));

        optional<long long> best;
        auto stats = bench::solve_with_timeout(timeout, p,
            SolveCallbacks{.solution = [&](const CurrentState & s) -> bool {
                               best = s(obj).raw_value;
                               if (print_solutions) {
                                   for (int r = 0; r < n; ++r) {
                                       for (int c = 0; c < n; ++c)
                                           print("{}{}", c == 0 ? "" : ",", s(filled[r][c]) == 1_i ? string{"#"} : format("{}", clue[r][c]));
                                       println("");
                                   }
                                   println("obj = {}", *best);
                                   println("");
                               }
                               // an optimisation problem: keep going until optimality is proven
                               return true;
                           },
                .branch = brancher},
            proof_basename ? make_optional(ProofOptions{*proof_basename}) : nullopt);

        return pair{stats, best};
    }
}

auto main(int argc, char * argv[]) -> int
{
    cxxopts::Options options("Hitori Example");
    cxxopts::ParseResult options_vars;

    try {
        options.add_options("Program Options")                                                                   //
            ("help", "Display help information")                                                                 //
            ("prove", "Create a proof")                                                                          //
            ("proof-files-basename", "Basename for the .opb and .pbp files",                                     //
                cxxopts::value<string>()->default_value("hitori"))                                               //
            ("size", "Solve a generated size-by-size instance", cxxopts::value<int>()->default_value("4"))       //
            ("seed", "Seed for the generator (-1 for a random seed)", cxxopts::value<int>()->default_value("0")) //
            ("density", "Probability that the generator tries to shade a cell",                                  //
                cxxopts::value<double>()->default_value("0.3"))                                                  //
            ("duplicates", "Probability that a generated shaded cell repeats a value from its row or column",    //
                cxxopts::value<double>()->default_value("0.8"))                                                  //
            ("dzn", "Solve a MiniZinc Challenge hitori instance instead", cxxopts::value<string>())              //
            ("connectivity",
                "How to require the unshaded cells to be connected: decomposition (the mznlib "               //
                "encoding, the default), propagator (the native Reachable propagator), "                      //
                "propagator-no-cuts (the same without its cut-vertex and bridge forcing), or none "           //
                "(a relaxation that does not solve hitori, for proof attribution only)",                      //
                cxxopts::value<string>()->default_value("decomposition"))                                     //
            ("show-clues", "Print the clue grid before solving")                                              //
            ("quiet", "Do not print the improving solutions")                                                 //
            ("timeout", "Abort search after this many seconds", cxxopts::value<double>()->default_value("0")) //
            ("stats", "Print solve statistics");

        options_vars = options.parse(argc, argv);
    }
    catch (const cxxopts::exceptions::exception & e) {
        cerr << "Error: " << e.what() << endl;
        cerr << "Try " << argv[0] << " --help" << endl;
        return EXIT_FAILURE;
    }

    if (options_vars.contains("help")) {
        cout << options.help() << endl;
        return EXIT_SUCCESS;
    }

    auto connectivity_name = options_vars["connectivity"].as<string>();
    Connectivity connectivity;
    if (connectivity_name == "decomposition")
        connectivity = Connectivity::Decomposition;
    else if (connectivity_name == "propagator")
        connectivity = Connectivity::Propagator;
    else if (connectivity_name == "propagator-no-cuts")
        connectivity = Connectivity::PropagatorNoCuts;
    else if (connectivity_name == "none")
        connectivity = Connectivity::None;
    else {
        cerr << "Error: unknown --connectivity '" << connectivity_name << "', try decomposition, propagator, propagator-no-cuts or none" << endl;
        return EXIT_FAILURE;
    }

    optional<Instance> instance;
    if (options_vars.contains("dzn")) {
        instance = read_dzn(options_vars["dzn"].as<string>());
        if (! instance)
            return EXIT_FAILURE;
    }
    else {
        auto size = options_vars["size"].as<int>();
        if (size < 2) {
            cerr << "Error: --size must be at least 2" << endl;
            return EXIT_FAILURE;
        }
        auto seed = options_vars["seed"].as<int>();
        if (seed == -1) {
            seed = static_cast<int>(random_device{}());
            println("% drew seed {}", seed);
        }
        instance = random_instance(size, static_cast<unsigned>(seed), //
            options_vars["density"].as<double>(), options_vars["duplicates"].as<double>());
    }

    if (options_vars.contains("show-clues"))
        print_grid_of(*instance);

    auto [stats, best] = solve_hitori(*instance, connectivity, //
        ! options_vars.contains("quiet"),                      //
        options_vars["timeout"].as<double>(),                  //
        options_vars.contains("prove")                         //
            ? make_optional(options_vars["proof-files-basename"].as<string>())
            : nullopt);

    if (! best)
        println("no valid shading");

    if (options_vars.contains("stats"))
        print("{}", stats);

    return EXIT_SUCCESS;
}
