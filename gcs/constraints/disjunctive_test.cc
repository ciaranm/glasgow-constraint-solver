#include <gcs/constraints/disjunctive.hh>
#include <gcs/constraints/innards/constraints_test_utils.hh>
#include <gcs/exception.hh>
#include <gcs/problem.hh>
#include <gcs/solve.hh>

#include <cstdlib>
#include <iostream>
#include <optional>
#include <random>
#include <set>
#include <string>
#include <tuple>
#include <utility>
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
using std::pair;
using std::random_device;
using std::set;
using std::string;
using std::tuple;
using std::uniform_int_distribution;
using std::vector;

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
    // Dup-variable test: Disjunctive with the same start handle for two
    // tasks. Two positive-length tasks sharing a start ⇒ UNSAT (they
    // overlap by construction). Consistency isn't checked on dup runs;
    // see tmp/duplicate_var_audit.md.
    auto run_dup_disjunctive_test(bool proofs, const string & mode, bool strict,
        const vector<pair<int, int>> & unique_start_ranges,
        const vector<int> & positions, const vector<int> & lengths) -> void
    {
        print(cerr, "disjunctive{} dup unique_starts={} positions={} lens={}{}",
            strict ? "_strict" : "", unique_start_ranges, positions, lengths,
            proofs ? " with proofs:" : ":");
        cerr << flush;

        auto n = positions.size();

        auto is_satisfying = [&](const vector<int> & unique_starts) {
            for (size_t i = 0; i < n; ++i)
                for (size_t j = i + 1; j < n; ++j) {
                    if (! strict && (lengths[i] == 0 || lengths[j] == 0))
                        continue;
                    int si = unique_starts.at(positions.at(i));
                    int sj = unique_starts.at(positions.at(j));
                    bool i_before_j = si + lengths[i] <= sj;
                    bool j_before_i = sj + lengths[j] <= si;
                    if (! i_before_j && ! j_before_i)
                        return false;
                }
            return true;
        };

        set<vector<int>> expected, actual;
        build_expected(expected, is_satisfying, unique_start_ranges);
        println(cerr, " expecting {} solutions", expected.size());

        Problem p;
        vector<IntegerVariableID> unique_starts;
        for (auto & [lo, hi] : unique_start_ranges)
            unique_starts.push_back(p.create_integer_variable(Integer{lo}, Integer{hi}));
        vector<IntegerVariableID> starts;
        for (auto pos : positions)
            starts.push_back(unique_starts.at(pos));

        vector<Integer> lengths_i;
        for (auto l : lengths)
            lengths_i.push_back(Integer{l});

        p.post(Disjunctive{starts, lengths_i, strict});

        auto proof_name = proofs ? make_optional("disjunctive_test_" + mode + "_dup") : nullopt;
        solve_for_tests(p, proof_name, actual, tuple{unique_starts});
        check_results(proof_name, expected, actual);
    }

    auto run_disjunctive_test(bool proofs, const string & mode, bool strict, const ViewWrapConfig & view_cfg,
        const vector<pair<int, int>> & start_ranges, const vector<int> & lengths) -> void
    {
        auto wraps = wraps_for_positions(view_cfg, static_cast<int>(start_ranges.size()));
        print(cerr, "disjunctive{} [{}] {} {}{}", strict ? "_strict" : "",
            view_wrap_config_label(view_cfg), start_ranges, lengths, proofs ? " with proofs:" : ":");
        cerr << flush;

        auto n = start_ranges.size();

        auto is_satisfying = [&](const vector<int> & starts) {
            for (size_t i = 0; i < n; ++i)
                for (size_t j = i + 1; j < n; ++j) {
                    // Non-strict: pairs involving a zero-length task float freely.
                    if (! strict && (lengths[i] == 0 || lengths[j] == 0))
                        continue;
                    bool i_before_j = starts[i] + lengths[i] <= starts[j];
                    bool j_before_i = starts[j] + lengths[j] <= starts[i];
                    if (! i_before_j && ! j_before_i)
                        return false;
                }
            return true;
        };

        set<vector<int>> expected, actual;
        build_expected(expected, is_satisfying, start_ranges);
        println(cerr, " expecting {} solutions", expected.size());

        Problem p;
        vector<IntegerVariableID> starts;
        for (size_t i = 0; i < start_ranges.size(); ++i)
            starts.push_back(create_integer_variable_or_constant_with_view(p, start_ranges.at(i), wraps.at(i)));

        vector<Integer> lengths_i;
        for (auto l : lengths)
            lengths_i.push_back(Integer{l});

        p.post(Disjunctive{starts, lengths_i, strict});

        auto proof_name = proofs ? make_optional("disjunctive_test_" + mode + "_" + view_wrap_config_label(view_cfg)) : nullopt;
        solve_for_tests(p, proof_name, actual, tuple{starts});

        check_results(proof_name, expected, actual);
    }
}

auto main(int argc, char * argv[]) -> int
{
    if (argc < 2)
        throw UnimplementedException{};

    string mode{argv[1]};
    bool strict;
    if (mode == "strict")
        strict = true;
    else if (mode == "nonstrict")
        strict = false;
    else
        throw UnimplementedException{};

    auto view_cfg = parse_view_wrap_config_from_argv(argc, argv);

    // Start-variable positions wrapped by the single-position sweep. The
    // fixed and random data top out at 4 tasks, so a single-position index
    // beyond this would wrap nothing on any test; detect and skip rather
    // than emit a duplicate bare run. mixed/uniform wrap every position.
    constexpr int n_positions = 4;
    if (view_cfg.single_position && (*view_cfg.single_position < 0 || *view_cfg.single_position >= n_positions)) {
        println(cerr, "disjunctive view sweep: position {} out of range for n_positions = {}; skipping",
            *view_cfg.single_position, n_positions);
        return EXIT_SUCCESS;
    }

    bool run_dup = view_wrap_config_is_effectively_bare(view_cfg, n_positions);

    // Each test: { start_ranges, lengths }
    // Kept small because stage-1 propagation is a pure checker: the solver
    // brute-forces through every assignment.
    vector<pair<vector<pair<int, int>>, vector<int>>> data = {
        // Two tasks must not overlap.
        {{{0, 3}, {0, 3}}, {2, 2}},
        // Asymmetric lengths.
        {{{0, 3}, {0, 3}}, {1, 2}},
        // Three tasks, tight horizon, must serialise to fit.
        {{{0, 2}, {0, 2}, {0, 2}}, {1, 1, 1}},
        // Three tasks of varying lengths.
        {{{0, 3}, {0, 3}, {0, 3}}, {1, 1, 2}},
        // Single task — vacuously satisfiable, filtered to < 2 active.
        {{{0, 4}}, {3}},
        // Trivially unsatisfiable: two length-2 tasks pinned to time 0.
        {{{0, 0}, {0, 0}}, {2, 2}},
        // One zero-length task alongside a non-zero one.
        {{{0, 2}, {0, 2}}, {0, 2}},
        // Two zero-length tasks.
        {{{0, 2}, {0, 2}}, {0, 0}},
    };

    // Random instances for breadth.
    random_device rand_dev;
    mt19937 rand(rand_dev());

    auto random_instance = [&](int n, int max_start, int max_length)
        -> pair<vector<pair<int, int>>, vector<int>> {
        uniform_int_distribution<> lo_dist(0, max_start), span_dist(0, max_start),
            len_dist(0, max_length);
        vector<pair<int, int>> sr;
        vector<int> lens;
        for (int i = 0; i < n; ++i) {
            auto lo = lo_dist(rand), span = span_dist(rand);
            sr.emplace_back(lo, min(lo + span, max_start));
            lens.push_back(len_dist(rand));
        }
        return {sr, lens};
    };

    // 25 small random cases (n=2 or 3, narrow horizons).
    for (int k = 0; k < 25; ++k) {
        uniform_int_distribution<> n_dist(2, 3);
        data.emplace_back(random_instance(n_dist(rand), 3, 3));
    }

    // 15 medium random cases (n=3 or 4, wider domains).
    for (int k = 0; k < 15; ++k) {
        uniform_int_distribution<> n_dist(3, 4);
        data.emplace_back(random_instance(n_dist(rand), 4, 3));
    }

    for (bool proofs : {false, true}) {
        if (proofs && ! can_run_veripb())
            continue;
        for (auto & [sr, lens] : data)
            run_disjunctive_test(proofs, mode, strict, view_cfg, sr, lens);

        // Dup tests use bare variables (the harness duplicates a handle into
        // several task positions); only run them when no wrapping is in
        // effect, to avoid duplicating the bare coverage under every wrap.
        if (run_dup) {
            // Two tasks sharing a start var: positive lengths ⇒ UNSAT,
            // zero lengths ⇒ depends on strict.
            run_dup_disjunctive_test(proofs, mode, strict, {{0, 3}}, {0, 0}, {2, 2});
            // {x, x, y} — first two share, third independent.
            run_dup_disjunctive_test(proofs, mode, strict, {{0, 3}, {0, 3}}, {0, 0, 1},
                {1, 1, 2});
            // Zero-length dup pair — non-strict OK, strict edge case.
            run_dup_disjunctive_test(proofs, mode, strict, {{0, 2}}, {0, 0}, {0, 0});
        }
    }

    return EXIT_SUCCESS;
}
