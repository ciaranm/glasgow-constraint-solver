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
    auto run_dup_disjunctive_test(bool proofs, const string & mode, bool strict, const vector<pair<int, int>> & unique_start_ranges,
        const vector<int> & positions, const vector<int> & lengths) -> void
    {
        print(cerr, "disjunctive{} dup unique_starts={} positions={} lens={}{}", strict ? "_strict" : "", unique_start_ranges, positions, lengths,
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

        p.post(Disjunctive{starts, lengths_i}.with_strict(strict));

        auto proof_name = proofs ? make_optional("disjunctive_test_" + mode + "_dup") : nullopt;
        solve_for_tests(p, proof_name, actual, tuple{unique_starts});
        check_results(proof_name, expected, actual);
    }

    auto run_disjunctive_test(bool proofs, const string & mode, bool strict, const ViewWrapConfig & view_cfg,
        const vector<pair<int, int>> & start_ranges, const vector<int> & lengths) -> void
    {
        auto wraps = wraps_for_positions(view_cfg, static_cast<int>(start_ranges.size()));
        print(cerr, "disjunctive{} [{}] {} {}{}", strict ? "_strict" : "", view_wrap_config_label(view_cfg), start_ranges, lengths,
            proofs ? " with proofs:" : ":");
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

        p.post(Disjunctive{starts, lengths_i}.with_strict(strict));

        auto proof_name = proofs ? make_optional("disjunctive_test_" + mode + "_" + view_wrap_config_label(view_cfg)) : nullopt;
        solve_for_tests(p, proof_name, actual, tuple{starts});

        check_results(proof_name, expected, actual);
    }

    // Variable-duration test (strict only — non-strict variable durations are
    // rejected in prepare for now). Each task has a start range and a duration
    // spec {lo, hi}; lo == hi is a constant duration, lo < hi a variable one.
    // Enumerated variables appear in every solution vector as: starts (task
    // order), then the variable durations (task order).
    auto run_var_disjunctive_test(bool proofs, const string & mode, bool strict, const vector<pair<int, int>> & start_ranges,
        const vector<pair<int, int>> & length_specs) -> void
    {
        auto n = start_ranges.size();
        vector<bool> lvar(n);
        for (size_t i = 0; i < n; ++i)
            lvar[i] = length_specs[i].first != length_specs[i].second;

        print(cerr, "disjunctive{} var starts={} lspecs={}{}", strict ? "_strict" : "", start_ranges, length_specs, proofs ? " with proofs:" : ":");
        cerr << flush;

        auto is_satisfying = [&](const vector<int> & vals) {
            vector<int> l(n);
            size_t k = n;
            for (size_t i = 0; i < n; ++i)
                l[i] = lvar[i] ? vals.at(k++) : length_specs[i].first;
            for (size_t i = 0; i < n; ++i)
                for (size_t j = i + 1; j < n; ++j) {
                    // Non-strict: a pair involving a zero-length task floats.
                    if (! strict && (l[i] == 0 || l[j] == 0))
                        continue;
                    bool i_before_j = vals[i] + l[i] <= vals[j];
                    bool j_before_i = vals[j] + l[j] <= vals[i];
                    if (! i_before_j && ! j_before_i)
                        return false;
                }
            return true;
        };

        vector<pair<int, int>> all_ranges = start_ranges;
        for (size_t i = 0; i < n; ++i)
            if (lvar[i])
                all_ranges.push_back(length_specs[i]);

        set<vector<int>> expected, actual;
        build_expected(expected, is_satisfying, all_ranges);
        println(cerr, " expecting {} solutions", expected.size());

        Problem p;
        vector<IntegerVariableID> starts, lengths_v, all_vars;
        for (auto & [lo, hi] : start_ranges) {
            auto v = p.create_integer_variable(Integer{lo}, Integer{hi});
            starts.push_back(v);
            all_vars.push_back(v);
        }
        for (size_t i = 0; i < n; ++i) {
            if (lvar[i]) {
                auto lv = p.create_integer_variable(Integer{length_specs[i].first}, Integer{length_specs[i].second});
                lengths_v.push_back(lv);
                all_vars.push_back(lv);
            }
            else
                lengths_v.push_back(constant_variable(Integer{length_specs[i].first}));
        }

        p.post(Disjunctive{starts, lengths_v}.with_strict(strict));

        auto proof_name = proofs ? make_optional("disjunctive_test_" + mode + "_var") : nullopt;
        solve_for_tests(p, proof_name, actual, tuple{all_vars});
        check_results(proof_name, expected, actual);
    }

    // Constant-start variable-duration test: every start is a true
    // ConstantIntegerVariableID (not a singleton variable), exercising the
    // constant-start branch of the end-proxy materialisation (a constant start
    // contributes no order-literal to the pol — it is folded into end_ge). Only
    // the variable durations are enumerated; the fixed starts feed the checker.
    auto run_const_start_var_len_test(
        bool proofs, const string & mode, bool strict, const vector<int> & const_starts, const vector<pair<int, int>> & length_specs) -> void
    {
        auto n = const_starts.size();
        vector<bool> lvar(n);
        for (size_t i = 0; i < n; ++i)
            lvar[i] = length_specs[i].first != length_specs[i].second;

        print(cerr, "disjunctive{} const-start starts={} lspecs={}{}", strict ? "_strict" : "", const_starts, length_specs,
            proofs ? " with proofs:" : ":");
        cerr << flush;

        auto is_satisfying = [&](const vector<int> & vals) {
            vector<int> l(n);
            size_t k = 0;
            for (size_t i = 0; i < n; ++i)
                l[i] = lvar[i] ? vals.at(k++) : length_specs[i].first;
            for (size_t i = 0; i < n; ++i)
                for (size_t j = i + 1; j < n; ++j) {
                    // Non-strict: a pair involving a zero-length task floats.
                    if (! strict && (l[i] == 0 || l[j] == 0))
                        continue;
                    bool i_before_j = const_starts[i] + l[i] <= const_starts[j];
                    bool j_before_i = const_starts[j] + l[j] <= const_starts[i];
                    if (! i_before_j && ! j_before_i)
                        return false;
                }
            return true;
        };

        vector<pair<int, int>> all_ranges;
        for (size_t i = 0; i < n; ++i)
            if (lvar[i])
                all_ranges.push_back(length_specs[i]);

        set<vector<int>> expected, actual;
        build_expected(expected, is_satisfying, all_ranges);
        println(cerr, " expecting {} solutions", expected.size());

        Problem p;
        vector<IntegerVariableID> starts, lengths_v, all_vars;
        for (size_t i = 0; i < n; ++i)
            starts.push_back(constant_variable(Integer{const_starts[i]}));
        for (size_t i = 0; i < n; ++i) {
            if (lvar[i]) {
                auto lv = p.create_integer_variable(Integer{length_specs[i].first}, Integer{length_specs[i].second});
                lengths_v.push_back(lv);
                all_vars.push_back(lv);
            }
            else
                lengths_v.push_back(constant_variable(Integer{length_specs[i].first}));
        }

        p.post(Disjunctive{starts, lengths_v}.with_strict(strict));

        auto proof_name = proofs ? make_optional("disjunctive_test_" + mode + "_cstart") : nullopt;
        solve_for_tests(p, proof_name, actual, tuple{all_vars});
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
        println(cerr, "disjunctive view sweep: position {} out of range for n_positions = {}; skipping", *view_cfg.single_position, n_positions);
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
        // Degenerate cases (issue #254).
        // Empty task list: vacuously satisfiable (no propagator installed).
        {{}, {}},
        // All-fixed starts, abutting but not overlapping: [0,1) then [1,2).
        {{{0, 0}, {1, 1}}, {1, 1}},
        // All-fixed starts that overlap: both span [0,2) (contradiction).
        {{{0, 0}, {1, 1}}, {2, 2}},
    };

    // Random instances for breadth.
    random_device rand_dev;
    mt19937 rand(rand_dev());

    auto random_instance = [&](int n, int max_start, int max_length) -> pair<vector<pair<int, int>>, vector<int>> {
        uniform_int_distribution<> lo_dist(0, max_start), span_dist(0, max_start), len_dist(0, max_length);
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

    // Variable-duration instances, run in both strict and non-strict mode. Each
    // entry: { start_ranges, length_specs }, where a length spec {lo, hi} is
    // constant when lo == hi, variable when lo < hi.
    vector<pair<vector<pair<int, int>>, vector<pair<int, int>>>> var_data = {
        // Two tasks, both variable durations.
        {{{0, 3}, {0, 3}}, {{1, 2}, {1, 2}}},
        // Mixed: one variable, one constant duration.
        {{{0, 3}, {0, 3}}, {{1, 3}, {2, 2}}},
        // Three tasks, variable durations, tight horizon.
        {{{0, 3}, {0, 3}, {0, 3}}, {{1, 2}, {1, 2}, {1, 2}}},
        // A duration that can be zero: strict forbids it strictly inside
        // another's interval; non-strict lets the zero-length task float.
        {{{0, 2}, {0, 2}}, {{0, 2}, {1, 1}}},
        // Forced overlap at the root: starts pinned, minimum durations collide.
        {{{0, 1}, {0, 1}}, {{2, 3}, {2, 3}}},
        // Wider domains so variable-duration tasks get bound-PUSHED, not just
        // contradiction-pruned (exercises emit_chain_step's end-proxy).
        {{{0, 6}, {0, 6}}, {{2, 3}, {2, 3}}},
        {{{0, 6}, {0, 6}, {0, 6}}, {{1, 3}, {1, 3}, {1, 3}}},
    };

    // Variable-duration random cases (n=2 or 3, narrow horizons, durations 0-2).
    auto random_var_instance = [&](int nn) -> pair<vector<pair<int, int>>, vector<pair<int, int>>> {
        uniform_int_distribution<> lo_dist(0, 3), span_dist(0, 3), llo_dist(0, 2), lspan_dist(0, 2);
        vector<pair<int, int>> sr, ls;
        for (int i = 0; i < nn; ++i) {
            auto lo = lo_dist(rand), span = span_dist(rand);
            sr.emplace_back(lo, min(lo + span, 3));
            auto llo = llo_dist(rand), lspan = lspan_dist(rand);
            ls.emplace_back(llo, min(llo + lspan, 2));
        }
        return {sr, ls};
    };
    for (int k = 0; k < 20; ++k) {
        uniform_int_distribution<> n_dist(2, 3);
        var_data.emplace_back(random_var_instance(n_dist(rand)));
    }

    // Constant-start variable-duration instances, run in both modes. Each
    // entry: { const_start_values, length_specs }.
    vector<pair<vector<int>, vector<pair<int, int>>>> cstart_data = {
        // Two constant-start tasks, variable durations; the gap forces shortness.
        {{0, 1}, {{1, 2}, {1, 2}}},
        // Mixed: variable + constant duration on constant starts.
        {{0, 2}, {{1, 3}, {2, 2}}},
        // Three constant starts, variable durations.
        {{0, 2, 4}, {{1, 2}, {1, 2}, {1, 2}}},
        // Forced overlap: pinned starts, minimum durations collide.
        {{0, 1}, {{2, 3}, {2, 3}}},
        // A duration that can be zero on a constant start (strict zero-inside).
        {{1, 0}, {{0, 2}, {2, 2}}},
    };

    for (bool proofs : {false, true}) {
        if (proofs && ! can_run_veripb())
            continue;
        for (auto & [sr, lens] : data)
            run_disjunctive_test(proofs, mode, strict, view_cfg, sr, lens);

        // Variable-duration cases run in both modes, only when not view-wrapping
        // (these runners create bare variables), to avoid duplicating coverage
        // under every wrap.
        if (run_dup) {
            for (auto & [sr, ls] : var_data)
                run_var_disjunctive_test(proofs, mode, strict, sr, ls);
            for (auto & [cs, ls] : cstart_data)
                run_const_start_var_len_test(proofs, mode, strict, cs, ls);
        }

        // Dup tests use bare variables (the harness duplicates a handle into
        // several task positions); only run them when no wrapping is in
        // effect, to avoid duplicating the bare coverage under every wrap.
        if (run_dup) {
            // Two tasks sharing a start var: positive lengths ⇒ UNSAT,
            // zero lengths ⇒ depends on strict.
            run_dup_disjunctive_test(proofs, mode, strict, {{0, 3}}, {0, 0}, {2, 2});
            // {x, x, y} — first two share, third independent.
            run_dup_disjunctive_test(proofs, mode, strict, {{0, 3}, {0, 3}}, {0, 0, 1}, {1, 1, 2});
            // Zero-length dup pair — non-strict OK, strict edge case.
            run_dup_disjunctive_test(proofs, mode, strict, {{0, 2}}, {0, 0}, {0, 0});
        }
    }

    return EXIT_SUCCESS;
}
