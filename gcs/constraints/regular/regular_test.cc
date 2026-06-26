#include <gcs/constraints/innards/constraints_test_utils.hh>
#include <gcs/constraints/regular/regex.hh>
#include <gcs/constraints/regular/regular.hh>
#include <gcs/problem.hh>
#include <gcs/solve.hh>

#include <cstddef>
#include <cstdlib>
#include <iostream>
#include <set>
#include <string>
#include <tuple>
#include <unordered_map>
#include <utility>
#include <vector>
#include <version>

#if defined(__cpp_lib_print) && defined(__cpp_lib_format)
#include <print>
#else
#include <fmt/core.h>
#include <fmt/ostream.h>
#endif

using std::cerr;
using std::flush;
using std::make_optional;
using std::nullopt;
using std::pair;
using std::set;
using std::string;
using std::tuple;
using std::unordered_map;
using std::vector;
using std::ranges::find;

#if defined(__cpp_lib_print) && defined(__cpp_lib_format)
using std::print;
using std::println;
#else
using fmt::print;
using fmt::println;
#endif

using namespace gcs;
using namespace gcs::test_innards;

auto run_regular_test(bool proofs, const ViewWrapConfig & view_cfg, const string & desc, vector<pair<int, int>> var_ranges, long num_states,
    vector<unordered_map<Integer, long>> transitions, vector<long> final_states) -> void
{
    auto wraps = wraps_for_positions(view_cfg, static_cast<int>(var_ranges.size()));
    print(cerr, "regular [{}] {} {} vars{}", view_wrap_config_label(view_cfg), desc, var_ranges.size(), proofs ? " with proofs:" : ":");
    cerr << flush;

    auto dfa_accepts = [&](const vector<int> & seq) -> bool {
        long state = 0;
        for (int val : seq) {
            auto it = transitions[state].find(Integer(val));
            if (it == transitions[state].end() || it->second == -1L)
                return false;
            state = it->second;
        }
        return find(final_states, state) != final_states.end();
    };

    set<tuple<vector<int>>> expected, actual;
    build_expected(expected, [&](vector<int> seq) { return dfa_accepts(seq); }, var_ranges);
    println(cerr, " expecting {} solutions", expected.size());

    Problem p;
    vector<IntegerVariableID> vars;
    for (std::size_t i = 0; i < var_ranges.size(); ++i)
        vars.push_back(create_integer_variable_or_constant_with_view(p, var_ranges.at(i), wraps.at(i)));
    p.post(Regular{vars, num_states, transitions, final_states});

    auto proof_name = proofs ? make_optional("regular_test_" + view_wrap_config_label(view_cfg)) : nullopt;
    solve_for_tests_checking_gac(p, proof_name, expected, actual, tuple{vars});
    check_results(proof_name, expected, actual);
}

// Dup-variable test: Regular with the same handle at several positions.
// Each position is processed independently by the DFA; aliasing forces
// those positions to take the same letter. Consistency isn't checked
// on dup runs; see tmp/duplicate_var_audit.md.
auto run_dup_regular_test(bool proofs, const string & label, const vector<pair<int, int>> & unique_domains, const vector<int> & positions,
    long num_states, vector<unordered_map<Integer, long>> transitions, vector<long> final_states) -> void
{
    print(cerr, "regular dup {} unique_doms={} positions={}{}", label, unique_domains, positions, proofs ? " with proofs:" : ":");
    cerr << flush;

    auto dfa_accepts = [&](const vector<int> & seq) -> bool {
        long state = 0;
        for (int val : seq) {
            auto it = transitions[state].find(Integer(val));
            if (it == transitions[state].end() || it->second == -1L)
                return false;
            state = it->second;
        }
        return find(final_states, state) != final_states.end();
    };

    set<tuple<vector<int>>> expected, actual;
    build_expected(
        expected,
        [&](const vector<int> & unique_vals) -> bool {
            vector<int> seq;
            for (auto pos : positions)
                seq.push_back(unique_vals.at(pos));
            return dfa_accepts(seq);
        },
        unique_domains);
    println(cerr, " expecting {} solutions", expected.size());

    Problem p;
    vector<IntegerVariableID> unique_vars;
    for (const auto & [lo, hi] : unique_domains)
        unique_vars.push_back(p.create_integer_variable(Integer(lo), Integer(hi)));
    vector<IntegerVariableID> vars;
    for (auto pos : positions)
        vars.push_back(unique_vars.at(pos));
    p.post(Regular{vars, num_states, transitions, final_states});

    auto proof_name = proofs ? make_optional("regular_test_dup_" + label) : nullopt;
    solve_for_tests(p, proof_name, actual, tuple{unique_vars});
    check_results(proof_name, expected, actual);
}

// Regex-string form of the constraint. The oracle is the independent reference
// matcher from regular/regex.hh, given the same contiguous min..max alphabet
// that Regular::prepare derives from the variable domains.
auto run_regular_regex_test(bool proofs, const string & label, const string & regex, const vector<pair<int, int>> & var_ranges) -> void
{
    print(cerr, "regular regex {} \"{}\" {} vars{}", label, regex, var_ranges.size(), proofs ? " with proofs:" : ":");
    cerr << flush;

    int lo = var_ranges.front().first, hi = var_ranges.front().second;
    for (const auto & [a, b] : var_ranges) {
        lo = a < lo ? a : lo;
        hi = b > hi ? b : hi;
    }
    vector<Integer> alphabet;
    for (int v = lo; v <= hi; ++v)
        alphabet.push_back(Integer(v));

    auto accepts = [&](const vector<int> & seq) -> bool {
        vector<Integer> as_integers;
        for (int v : seq)
            as_integers.push_back(Integer(v));
        return gcs::innards::regex_reference_accepts(regex, alphabet, as_integers);
    };

    set<tuple<vector<int>>> expected, actual;
    build_expected(expected, [&](vector<int> seq) { return accepts(seq); }, var_ranges);
    println(cerr, " expecting {} solutions", expected.size());

    Problem p;
    vector<IntegerVariableID> vars;
    for (const auto & [a, b] : var_ranges)
        vars.push_back(p.create_integer_variable(Integer(a), Integer(b)));
    p.post(Regular{vars, regex});

    auto proof_name = proofs ? make_optional("regular_regex_test_" + label) : nullopt;
    solve_for_tests_checking_gac(p, proof_name, expected, actual, tuple{vars});
    check_results(proof_name, expected, actual);
}

auto run_all_regex_tests(bool proofs) -> void
{
    // Deterministic: a fixed sequence.
    run_regular_regex_test(proofs, "concat", "0 1 0", {{0, 1}, {0, 1}, {0, 1}});
    // The 0*11*0* language from the Pesant example.
    run_regular_regex_test(proofs, "star", "0* 1 1* 0*", {{0, 1}, {0, 1}, {0, 1}, {0, 1}});
    // Genuine non-determinism: after reading a 1 the NFA can be in two states,
    // exercising the disjunctive transition clause in the proof model.
    run_regular_regex_test(proofs, "nfa_fanout", "1 2|1 3", {{1, 3}, {1, 3}});
    // Wildcard expands to the domain's min..max.
    run_regular_regex_test(proofs, "wildcard", "0 . 0", {{0, 1}, {0, 1}, {0, 1}});
    // Counted quantifier with a trailing star.
    run_regular_regex_test(proofs, "counted", "0{1,2} 1*", {{0, 1}, {0, 1}, {0, 1}});
    // Negated class over an alphabet with a hole at the top of the range.
    run_regular_regex_test(proofs, "negclass", "[^0] [^0]", {{0, 2}, {0, 2}});
}

auto run_all_tests(bool proofs, const ViewWrapConfig & view_cfg, bool run_dup) -> void
{
    // DFA: even number of 0s, binary alphabet {0,1}
    // State 0 (initial, final): 0->1, 1->0
    // State 1: 0->0, 1->1
    run_regular_test(proofs, view_cfg, "even zeros", {{0, 1}, {0, 1}, {0, 1}}, 2, {{{0_i, 1}, {1_i, 0}}, {{0_i, 0}, {1_i, 1}}}, {0});

    // DFA: no two consecutive 0s, binary alphabet {0,1}
    // State 0 (initial, final): 0->1, 1->0
    // State 1 (final, last was 0): 0->dead (absent), 1->0
    run_regular_test(proofs, view_cfg, "no consecutive 0s", {{0, 1}, {0, 1}, {0, 1}, {0, 1}}, 2, {{{0_i, 1}, {1_i, 0}}, {{1_i, 0}}}, {0, 1});

    // DFA: sequence contains at least one 2, ternary alphabet {0,1,2}
    // State 0: 0->0, 1->0, 2->1
    // State 1 (final): all symbols -> 1
    run_regular_test(
        proofs, view_cfg, "contains 2", {{0, 2}, {0, 2}, {0, 2}}, 2, {{{0_i, 0}, {1_i, 0}, {2_i, 1}}, {{0_i, 1}, {1_i, 1}, {2_i, 1}}}, {1});

    // Same DFA: first two variables restricted to {0,1}, last to {0,1,2}.
    // GAC must prune the last variable's domain to {2} at the root, since
    // no accepting path exists unless some variable carries the value 2.
    run_regular_test(proofs, view_cfg, "contains 2, last forced to 2", {{0, 1}, {0, 1}, {0, 2}}, 2,
        {{{0_i, 0}, {1_i, 0}, {2_i, 1}}, {{0_i, 1}, {1_i, 1}, {2_i, 1}}}, {1});

    // DFA: all symbols in the sequence must be identical, binary alphabet {0,1}
    // State 0 (initial): 0->1, 1->2
    // State 1 (all 0s so far, final): 0->1, 1->dead (absent)
    // State 2 (all 1s so far, final): 0->dead (absent), 1->2
    run_regular_test(proofs, view_cfg, "all same", {{0, 1}, {0, 1}, {0, 1}, {0, 1}}, 4, {{{0_i, 1}, {1_i, 2}}, {{0_i, 1}}, {{1_i, 2}}, {}}, {1, 2});

    // Unsatisfiable: no final states
    run_regular_test(proofs, view_cfg, "no final states", {{0, 1}, {0, 1}, {0, 1}}, 2, {{{0_i, 1}, {1_i, 0}}, {{0_i, 0}, {1_i, 1}}}, {});

    // Unsatisfiable: variable domains exclude all accepting paths.
    // "Contains 2" DFA with all variables restricted to {0,1} — 2 is never reachable.
    run_regular_test(proofs, view_cfg, "domain excludes accepting paths", {{0, 1}, {0, 1}, {0, 1}}, 2,
        {{{0_i, 0}, {1_i, 0}, {2_i, 1}}, {{0_i, 1}, {1_i, 1}, {2_i, 1}}}, {1});

    // Degenerate cases (issue #254). The even-zeros DFA: state 0 (initial) is
    // the "even count of 0s" state; 0 toggles state, 1 keeps it.
    // Empty sequence with the initial state accepting -> the empty word is
    // accepted (zero 0s is even).
    run_regular_test(proofs, view_cfg, "empty seq accepted", {}, 2, {{{0_i, 1}, {1_i, 0}}, {{0_i, 0}, {1_i, 1}}}, {0});
    // Empty sequence with only the non-initial state accepting -> the empty
    // word is rejected.
    run_regular_test(proofs, view_cfg, "empty seq rejected", {}, 2, {{{0_i, 1}, {1_i, 0}}, {{0_i, 0}, {1_i, 1}}}, {1});
    // Single fixed symbol, both directions.
    run_regular_test(
        proofs, view_cfg, "single fixed accepted", {{1, 1}}, 2, {{{0_i, 1}, {1_i, 0}}, {{0_i, 0}, {1_i, 1}}}, {0}); // [1] has zero 0s: accepted
    run_regular_test(
        proofs, view_cfg, "single fixed rejected", {{0, 0}}, 2, {{{0_i, 1}, {1_i, 0}}, {{0_i, 0}, {1_i, 1}}}, {0}); // [0] has one 0 (odd): rejected
    // Fully fixed multi-symbol accepted word.
    run_regular_test(proofs, view_cfg, "all fixed accepted", {{1, 1}, {0, 0}, {0, 0}}, 2, {{{0_i, 1}, {1_i, 0}}, {{0_i, 0}, {1_i, 1}}},
        {0}); // two 0s (even): accepted
    // Mixed fixed + variable: only the middle symbol can make the count even.
    run_regular_test(proofs, view_cfg, "mixed fixed and variable", {{0, 0}, {0, 1}, {0, 0}}, 2, {{{0_i, 1}, {1_i, 0}}, {{0_i, 0}, {1_i, 1}}},
        {0}); // accepted only when the middle symbol is 1

    // Regex-string and dup tests use bare variables; only run them when no
    // wrapping is in effect, to avoid duplicating the bare coverage under
    // every wrap.
    if (! run_dup)
        return;

    run_all_regex_tests(proofs);

    // Dup-variable cases: "even zeros" DFA with positions[0] reused.
    // {x, x, y} — two equal letters then y; "even zeros" wants total zeros
    // to be even, so two-of-the-same plus y leaves parity determined by y
    // when x=1, or determined by !y when x=0.
    run_dup_regular_test(proofs, "xxy_even_zeros", {{0, 1}, {0, 1}}, {0, 0, 1}, 2, {{{0_i, 1}, {1_i, 0}}, {{0_i, 0}, {1_i, 1}}}, {0});
    // {x, y, x} — non-adjacent dup.
    run_dup_regular_test(proofs, "xyx_even_zeros", {{0, 1}, {0, 1}}, {0, 1, 0}, 2, {{{0_i, 1}, {1_i, 0}}, {{0_i, 0}, {1_i, 1}}}, {0});
    // {x, x} with "all same" DFA: same handle at two positions ⇒ trivially
    // all-same; this just checks the DFA accepts.
    run_dup_regular_test(proofs, "xx_all_same", {{0, 1}}, {0, 0}, 4, {{{0_i, 1}, {1_i, 2}}, {{0_i, 1}}, {{1_i, 2}}, {}}, {1, 2});
    // {x, x, y, y} with "all same": requires x == y so the sequence is constant.
    run_dup_regular_test(proofs, "xxyy_all_same", {{0, 1}, {0, 1}}, {0, 0, 1, 1}, 4, {{{0_i, 1}, {1_i, 2}}, {{0_i, 1}}, {{1_i, 2}}, {}}, {1, 2});
}

auto main(int argc, char * argv[]) -> int
{
    auto view_cfg = parse_view_wrap_config_from_argv(argc, argv);

    // Sequence positions wrapped by the single-position sweep. The fixed
    // data tops out at 4 vars, so a single-position index beyond this would
    // wrap nothing on any test; detect and skip rather than emit a duplicate
    // bare run. mixed/uniform wrap every position.
    constexpr int n_positions = 4;
    if (view_cfg.single_position && (*view_cfg.single_position < 0 || *view_cfg.single_position >= n_positions)) {
        println(cerr, "regular view sweep: position {} out of range for n_positions = {}; skipping", *view_cfg.single_position, n_positions);
        return EXIT_SUCCESS;
    }

    bool run_dup = view_wrap_config_is_effectively_bare(view_cfg, n_positions);

    for (bool proofs : {false, true}) {
        if (proofs && ! can_run_veripb())
            continue;
        run_all_tests(proofs, view_cfg, run_dup);
    }

    return EXIT_SUCCESS;
}
