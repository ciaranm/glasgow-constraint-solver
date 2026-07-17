#include <gcs/constraints/innards/constraints_test_utils.hh>
#include <gcs/constraints/min_distance.hh>
#include <gcs/problem.hh>
#include <gcs/solve.hh>

#include <algorithm>
#include <cstdlib>
#include <iostream>
#include <limits>
#include <optional>
#include <random>
#include <set>
#include <stdexcept>
#include <tuple>
#include <utility>
#include <variant>
#include <vector>
#include <version>

#if defined(__cpp_lib_print) && defined(__cpp_lib_format)
#include <print>
#else
#include <fmt/core.h>
#include <fmt/ostream.h>
#include <fmt/ranges.h>
#endif

using std::cerr;
using std::flush;
using std::make_optional;
using std::min;
using std::mt19937;
using std::nullopt;
using std::optional;
using std::pair;
using std::set;
using std::tuple;
using std::uniform_int_distribution;
using std::variant;
using std::vector;
using std::visit;

#if defined(__cpp_lib_print) && defined(__cpp_lib_format)
using std::print;
using std::println;
#else
using fmt::print;
using fmt::println;
#endif

using namespace gcs;
using namespace gcs::test_innards;

namespace
{
    using DomainSpec = variant<int, pair<int, int>, vector<int>>;
    using IntMatrix = vector<vector<int>>;

    // The visible values a domain spec offers, clipped to the site range
    // [0, n-1] (matching the constraint's own site-range restriction).
    auto site_values(const DomainSpec & spec, int n) -> vector<int>
    {
        vector<int> vs;
        visit(
            [&](const auto & s) {
                using T = std::decay_t<decltype(s)>;
                if constexpr (std::is_same_v<T, int>)
                    vs.push_back(s);
                else if constexpr (std::is_same_v<T, pair<int, int>>) {
                    for (int v = s.first; v <= s.second; ++v)
                        vs.push_back(v);
                }
                else
                    vs = s;
            },
            spec);
        vector<int> clipped;
        for (auto v : vs)
            if (v >= 0 && v < n)
                clipped.push_back(v);
        return clipped;
    }

    // The visible values a z domain spec offers (no clipping: z is not a site).
    auto plain_values(const DomainSpec & spec) -> vector<int>
    {
        vector<int> vs;
        visit(
            [&](const auto & s) {
                using T = std::decay_t<decltype(s)>;
                if constexpr (std::is_same_v<T, int>)
                    vs.push_back(s);
                else if constexpr (std::is_same_v<T, pair<int, int>>) {
                    for (int v = s.first; v <= s.second; ++v)
                        vs.push_back(v);
                }
                else
                    vs = s;
            },
            spec);
        return vs;
    }

    auto min_pairwise(const vector<int> & xs, const IntMatrix & d) -> int
    {
        int mu = std::numeric_limits<int>::max();
        for (std::size_t i = 0; i < xs.size(); ++i)
            for (std::size_t j = i + 1; j < xs.size(); ++j)
                mu = min(mu, d[xs[i]][xs[j]]);
        return mu;
    }

    auto requirements_ok(const vector<int> & xs, const optional<IntMatrix> & r, const IntMatrix & d) -> bool
    {
        if (! r)
            return true;
        for (std::size_t i = 0; i < xs.size(); ++i)
            for (std::size_t j = i + 1; j < xs.size(); ++j)
                if (d[xs[i]][xs[j]] < (*r)[i][j])
                    return false;
        return true;
    }

    auto to_integer_matrix(const IntMatrix & m) -> MinDistance::Matrix
    {
        MinDistance::Matrix result;
        for (const auto & row : m) {
            vector<Integer> r;
            for (auto e : row)
                r.push_back(Integer(e));
            result.push_back(std::move(r));
        }
        return result;
    }

    auto mode_label(MinDistancePropagation mode) -> const char *
    {
        switch (mode) {
            using enum MinDistancePropagation;
        case CheckOnly: return "check";
        case ForwardBound: return "fb";
        case PairSupport: return "ps";
        case ForwardBoundMatch: return "fbm";
        case PairSupportMatch: return "psm";
        }
        return "?";
    }

    // The pair-support invariant (paper Section 4.2), checked at every search node
    // once PairSupport propagation has reached fixpoint: for every ordered pair
    // (i, j) and every site a still in dom(x_i), some site b in dom(x_j) has
    // D[a,b] >= max(R_ij, z_min). This is deliberately weaker than joint GAC. The
    // logical (post-view) values of the variables are the site indices, so reading
    // them via the CurrentState is view-safe.
    auto check_pair_support(
        const CurrentState & s, const vector<IntegerVariableID> & xs, IntegerVariableID z, const IntMatrix & d, const optional<IntMatrix> & r) -> void
    {
        const int p = static_cast<int>(xs.size());
        const int zmin = s.lower_bound(z).raw_value;
        for (int i = 0; i < p; ++i)
            for (int j = 0; j < p; ++j) {
                if (i == j)
                    continue;
                const int rij = r ? (*r)[std::min(i, j)][std::max(i, j)] : 0;
                const int t = std::max(rij, zmin);
                for (auto a : s.each_value(xs[i])) {
                    bool supported = false;
                    for (auto b : s.each_value(xs[j]))
                        if (d[a.raw_value][b.raw_value] >= t) {
                            supported = true;
                            break;
                        }
                    if (! supported) {
                        println(cerr, "pair-support invariant violated: position {} value {} has no partner in position {} at threshold {}", i,
                            a.raw_value, j, t);
                        throw std::runtime_error{"pair-support invariant violated"};
                    }
                }
            }
    }
}

auto run_min_distance_test(bool proofs, MinDistancePropagation mode, const ViewWrapConfig & view_cfg, const vector<DomainSpec> & x_specs,
    const DomainSpec & z_spec, const IntMatrix & d, const optional<IntMatrix> & r) -> void
{
    const int n = static_cast<int>(d.size());
    const int p = static_cast<int>(x_specs.size());
    // Positions 0..p-1 are the selected-point variables; position p is z.
    auto wraps = wraps_for_positions(view_cfg, p + 1);

    print(cerr, "min_distance [{}/{}] p={} n={} x={} z={} r={}{}", mode_label(mode), view_wrap_config_label(view_cfg), p, n, x_specs, z_spec,
        r.has_value(), proofs ? " with proofs:" : ":");
    cerr << flush;

    // Brute-force the expected (x-assignment, z) solution set directly from the
    // definition: z is the minimum pairwise distance, and every requirement holds.
    vector<vector<int>> x_domains;
    for (const auto & s : x_specs)
        x_domains.push_back(site_values(s, n));
    auto z_domain = plain_values(z_spec);

    set<tuple<vector<int>, int>> expected, actual;
    {
        vector<int> xs(p);
        auto recurse = [&](auto && self, int pos) -> void {
            if (pos == p) {
                if (! requirements_ok(xs, r, d))
                    return;
                auto mu = min_pairwise(xs, d);
                for (auto z : z_domain)
                    if (z == mu)
                        expected.emplace(xs, z);
                return;
            }
            for (auto v : x_domains[pos]) {
                xs[pos] = v;
                self(self, pos + 1);
            }
        };
        recurse(recurse, 0);
    }
    println(cerr, " expecting {} solutions", expected.size());

    Problem problem;
    vector<IntegerVariableID> xs;
    for (int i = 0; i < p; ++i)
        xs.push_back(visit([&](const auto & s) { return create_integer_variable_or_constant_with_view(problem, s, wraps.at(i)); }, x_specs[i]));
    auto z = visit([&](const auto & s) { return create_integer_variable_or_constant_with_view(problem, s, wraps.at(p)); }, z_spec);

    if (r)
        problem.post(MinDistance{xs, z, to_integer_matrix(d), ArrayParam<MinDistance::Matrix>{to_integer_matrix(*r)}, mode});
    else
        problem.post(MinDistance{xs, z, to_integer_matrix(d), nullopt, mode});

    auto proof_name = proofs ? make_optional("min_distance_test_" + std::string{mode_label(mode)} + "_" + view_wrap_config_label(view_cfg)) : nullopt;

    if (mode == MinDistancePropagation::PairSupport || mode == MinDistancePropagation::PairSupportMatch) {
        // Same solution collection as solve_for_tests, plus a per-node check that
        // the pair-support kernel really reaches pair-support fixpoint at every node
        // (the matching variant adds only the z upper-bound propagator on top).
        solve_for_tests_with_callbacks(
            problem, proof_name,
            [&](const CurrentState & s) -> bool {
                actual.emplace(extract_from_state(s, xs), extract_from_state(s, z));
                return true;
            },
            [&](const CurrentState & s) -> bool {
                check_pair_support(s, xs, z, d, r);
                return true;
            });
    }
    else
        solve_for_tests(problem, proof_name, actual, tuple{xs, z});
    check_results(proof_name, expected, actual);
}

// The propagation modes every data-driven spec is run under: the three base
// strengths plus the two conflict-matching variants (which add the separate
// upper-bound propagator and must yield the identical solution set).
constexpr MinDistancePropagation all_modes[] = {MinDistancePropagation::CheckOnly, MinDistancePropagation::ForwardBound,
    MinDistancePropagation::PairSupport, MinDistancePropagation::ForwardBoundMatch, MinDistancePropagation::PairSupportMatch};

auto run_all_tests(bool proofs, const ViewWrapConfig & view_cfg) -> void
{
    // Run each spec under all three propagation modes: identical solution sets,
    // proofs verified for each.
    auto go = [&](const vector<DomainSpec> & x_specs, const DomainSpec & z_spec, const IntMatrix & d, const optional<IntMatrix> & r) {
        for (auto mode : all_modes)
            run_min_distance_test(proofs, mode, view_cfg, x_specs, z_spec, d, r);
    };

    // A handful of small symmetric distance matrices to draw on.
    const IntMatrix d2{{0, 3}, {3, 0}};
    const IntMatrix d3{{0, 2, 5}, {2, 0, 4}, {5, 4, 0}};
    const IntMatrix d3_ties{{0, 3, 3}, {3, 0, 3}, {3, 3, 0}}; // all off-diagonal distances tied
    const IntMatrix d3_zero{{0, 0, 4}, {0, 0, 4}, {4, 4, 0}}; // an off-diagonal zero (sites 0,1)
    const IntMatrix d4{{0, 2, 5, 9}, {2, 0, 4, 6}, {5, 4, 0, 3}, {9, 6, 3, 0}};
    const IntMatrix d4_ties{{0, 4, 4, 7}, {4, 0, 7, 4}, {4, 7, 0, 4}, {7, 4, 4, 0}};

    // p = 2, basic.
    go({pair{0, 1}, pair{0, 1}}, pair{0, 5}, d2, nullopt);
    // p = 2, z domain excludes 0 (duplicates ruled out by z >= 1).
    go({pair{0, 1}, pair{0, 1}}, pair{1, 5}, d2, nullopt);
    // p = 2, z domain forces a small window (BC through a hole is exercised by the harness).
    go({pair{0, 2}, pair{0, 2}}, pair{0, 6}, d3, nullopt);

    // p = 3, duplicates possible (z can be 0), full domains.
    go({pair{0, 2}, pair{0, 2}, pair{0, 2}}, pair{0, 6}, d3, nullopt);
    // p = 3, duplicates excluded (z >= 1), so this is effectively all-different sites.
    go({pair{0, 2}, pair{0, 2}, pair{0, 2}}, pair{1, 6}, d3, nullopt);
    // p = 3, all distances tied.
    go({pair{0, 2}, pair{0, 2}, pair{0, 2}}, pair{0, 4}, d3_ties, nullopt);
    // p = 3, matrix with an off-diagonal zero (sites 0 and 1 are distance 0 apart).
    go({pair{0, 2}, pair{0, 2}, pair{0, 2}}, pair{0, 5}, d3_zero, nullopt);

    // z domain with a hole: {0, 2, 4} (offset/holes tested together elsewhere).
    go({pair{0, 2}, pair{0, 2}, pair{0, 2}}, vector<int>{0, 2, 4}, d3, nullopt);
    // z domain offset above zero: [2, 6].
    go({pair{0, 2}, pair{0, 2}, pair{0, 2}}, pair{2, 6}, d3, nullopt);
    // z domain including negatives: forces z >= 0 via the ladder base clause.
    go({pair{0, 2}, pair{0, 2}, pair{0, 2}}, pair{-2, 6}, d3, nullopt);

    // x domains with holes / not covering all sites.
    go({vector<int>{0, 2}, pair{0, 2}, vector<int>{1, 2}}, pair{0, 6}, d3, nullopt);
    go({pair{0, 1}, pair{1, 2}, pair{0, 2}}, pair{0, 6}, d3, nullopt);
    // One position pinned to a constant site.
    go({0, pair{0, 2}, pair{0, 2}}, pair{0, 6}, d3, nullopt);

    // p = 4.
    go({pair{0, 3}, pair{0, 3}, pair{0, 3}, pair{0, 3}}, pair{0, 10}, d4, nullopt);
    go({pair{0, 3}, pair{0, 3}, pair{0, 3}, pair{0, 3}}, pair{1, 10}, d4_ties, nullopt);

    // With requirements R (only i<j entries read).
    // Feasible requirement: every selected pair at least distance 3 apart.
    const IntMatrix r3_feasible{{0, 3, 3}, {0, 0, 3}, {0, 0, 0}};
    go({pair{0, 2}, pair{0, 2}, pair{0, 2}}, pair{0, 6}, d3, r3_feasible);
    // Requirement forbids duplicates (R_ij > 0 rules out same-site pairs).
    go({pair{0, 2}, pair{0, 2}, pair{0, 2}}, pair{0, 6}, d3_ties, r3_feasible);
    // Infeasible requirement: demand distance >= 6 where the max distance is 5.
    const IntMatrix r3_infeasible{{0, 6, 6}, {0, 0, 6}, {0, 0, 0}};
    go({pair{0, 2}, pair{0, 2}, pair{0, 2}}, pair{0, 6}, d3, r3_infeasible);
    // Heterogeneous requirement per position pair.
    const IntMatrix r4_mixed{{0, 2, 4, 5}, {0, 0, 3, 4}, {0, 0, 0, 3}, {0, 0, 0, 0}};
    go({pair{0, 3}, pair{0, 3}, pair{0, 3}, pair{0, 3}}, pair{0, 10}, d4, r4_mixed);
}

// Random symmetric distance matrix: zero diagonal, non-negative, entries in
// [0, max_d].
auto random_distance_matrix(mt19937 & rand, int n, int max_d) -> IntMatrix
{
    IntMatrix d(n, vector<int>(n, 0));
    uniform_int_distribution<int> dist{0, max_d};
    for (int a = 0; a < n; ++a)
        for (int b = a + 1; b < n; ++b) {
            int v = dist(rand);
            d[a][b] = v;
            d[b][a] = v;
        }
    return d;
}

auto random_site_domain(mt19937 & rand, int n) -> DomainSpec
{
    // Either a contiguous range or an explicit (possibly holey) subset of [0, n-1].
    uniform_int_distribution<int> choice{0, 2};
    if (choice(rand) == 0) {
        // constant
        uniform_int_distribution<int> v{0, n - 1};
        return v(rand);
    }
    if (choice(rand) == 1) {
        uniform_int_distribution<int> lo{0, n - 1};
        int a = lo(rand);
        uniform_int_distribution<int> hi{a, n - 1};
        return pair{a, hi(rand)};
    }
    vector<int> subset;
    for (int a = 0; a < n; ++a) {
        uniform_int_distribution<int> keep{0, 1};
        if (keep(rand))
            subset.push_back(a);
    }
    if (subset.empty())
        subset.push_back(uniform_int_distribution<int>{0, n - 1}(rand));
    return subset;
}

auto main(int argc, char * argv[]) -> int
{
    establish_and_announce_seed(argc, argv);

    auto view_cfg = parse_view_wrap_config_from_argv(argc, argv);

    // Largest instance below wraps 5 selected points + z.
    constexpr int n_positions = 6;
    if (view_cfg.single_position && (*view_cfg.single_position < 0 || *view_cfg.single_position >= n_positions)) {
        println(cerr, "min_distance view sweep: position {} out of range for n_positions = {}; skipping", *view_cfg.single_position, n_positions);
        return EXIT_SUCCESS;
    }

    mt19937 rand(*get_seed());

    for (bool proofs : {false, true}) {
        if (proofs && ! can_run_veripb())
            continue;

        run_all_tests(proofs, view_cfg);

        // Random sweep: small symmetric matrices, small p, random site domains,
        // random z domains, half of them with a random feasible-ish requirement.
        for (int iter = 0; iter < 8; ++iter) {
            uniform_int_distribution<int> n_dist{2, 5};
            uniform_int_distribution<int> p_dist{2, 4};
            int n = n_dist(rand);
            int p = p_dist(rand);
            auto d = random_distance_matrix(rand, n, 4);

            vector<DomainSpec> x_specs;
            for (int i = 0; i < p; ++i)
                x_specs.push_back(random_site_domain(rand, n));

            // z domain: a random window that sometimes dips below zero and
            // sometimes starts above it, wide enough to admit the true minimum.
            uniform_int_distribution<int> zlo{-1, 2};
            uniform_int_distribution<int> zwidth{2, 6};
            int lo = zlo(rand);
            DomainSpec z_spec = pair{lo, lo + zwidth(rand)};

            optional<IntMatrix> r;
            uniform_int_distribution<int> want_r{0, 1};
            if (want_r(rand)) {
                IntMatrix rr(p, vector<int>(p, 0));
                uniform_int_distribution<int> rq{0, 3};
                for (int i = 0; i < p; ++i)
                    for (int j = i + 1; j < p; ++j)
                        rr[i][j] = rq(rand);
                r = rr;
            }

            // Same random instance under all three propagation modes.
            for (auto mode : all_modes)
                run_min_distance_test(proofs, mode, view_cfg, x_specs, z_spec, d, r);
        }
    }

    return EXIT_SUCCESS;
}
