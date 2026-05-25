#include <gcs/constraints/innards/constraints_test_utils.hh>
#include <gcs/constraints/logical.hh>
#include <gcs/problem.hh>
#include <gcs/solve.hh>

#include <cstddef>
#include <cstdlib>
#include <functional>
#include <iostream>
#include <optional>
#include <random>
#include <set>
#include <tuple>
#include <utility>
#include <vector>

using std::cerr;
using std::flush;
using std::function;
using std::make_optional;
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

template <typename Logical_>
auto run_logical_test(const string & which, bool proofs, const ViewWrapConfig & view_cfg,
    const vector<pair<int, int>> & vars, pair<int, int> full_reif,
    const function<auto(const vector<int> &, int)->bool> & is_satisfying) -> void
{
    auto wraps = wraps_for_positions(view_cfg, static_cast<int>(vars.size()));
    print(cerr, "logical {} [{}] {} {} {}", which, view_wrap_config_label(view_cfg), vars, full_reif, proofs ? " with proofs:" : ":");
    cerr << flush;

    set<pair<vector<int>, int>> expected, actual;
    build_expected(expected, is_satisfying, vars, full_reif);
    println(cerr, " expecting {} solutions", expected.size());

    Problem p;
    vector<IntegerVariableID> vs;
    for (std::size_t i = 0; i < vars.size(); ++i)
        vs.emplace_back(create_integer_variable_or_constant_with_view(p, vars.at(i), wraps.at(i)));
    // The reification variable stays bare: it is a control var, not an
    // operand position in the view sweep (mirrors lex's cond handling).
    auto r = p.create_integer_variable(Integer(full_reif.first), Integer(full_reif.second));

    if (-1 == full_reif.first && -1 == full_reif.second)
        p.post(Logical_{vs});
    else
        p.post(Logical_{vs, r});

    auto proof_name = proofs ? make_optional("logical_test_" + view_wrap_config_label(view_cfg)) : nullopt;
    solve_for_tests_checking_gac(p, proof_name, expected, actual, tuple{vs, r});

    check_results(proof_name, expected, actual);
}

// Dup-variable test: And/Or with the same handle in several lit
// positions, with full_reif as a distinct variable. Duplicate lits
// are redundant. See run_alias_reif_logical_test below for the
// full_reif-aliases-a-lit case.
template <typename Logical_>
auto run_dup_logical_test(const string & which, bool proofs,
    const vector<pair<int, int>> & unique_domains,
    const vector<int> & positions, pair<int, int> full_reif,
    const function<auto(const vector<int> &, int)->bool> & is_satisfying) -> void
{
    print(cerr, "logical dup {} unique_doms={} positions={} reif={}{}",
        which, unique_domains, positions, full_reif, proofs ? " with proofs:" : ":");
    cerr << flush;

    set<pair<vector<int>, int>> expected, actual;
    build_expected(
        expected, [&](const vector<int> & unique_vals, int r) -> bool {
            vector<int> lits;
            for (auto pos : positions)
                lits.push_back(unique_vals.at(pos));
            return is_satisfying(lits, r);
        },
        unique_domains, full_reif);
    println(cerr, " expecting {} solutions", expected.size());

    Problem p;
    vector<IntegerVariableID> unique_vars;
    for (const auto & [l, u] : unique_domains)
        unique_vars.emplace_back(p.create_integer_variable(Integer(l), Integer(u)));
    vector<IntegerVariableID> vs;
    for (auto pos : positions)
        vs.push_back(unique_vars.at(pos));
    auto r = p.create_integer_variable(Integer(full_reif.first), Integer(full_reif.second));

    if (-1 == full_reif.first && -1 == full_reif.second)
        p.post(Logical_{vs});
    else
        p.post(Logical_{vs, r});

    auto proof_name = proofs ? make_optional("logical_test_dup") : nullopt;
    solve_for_tests(p, proof_name, actual, tuple{unique_vars, r});
    check_results(proof_name, expected, actual);
}

// full_reif aliases one of the lits. For And the constraint reduces
// to a one-sided implication full_reif → ⋀(other lits) (the ↔ direction
// folds to a tautology because full_reif is on both sides). For Or the
// dual: ⋁(other lits) → full_reif.
template <typename Logical_>
auto run_alias_reif_logical_test(const string & which, bool proofs,
    const vector<pair<int, int>> & unique_domains,
    const vector<int> & positions, int reif_position,
    const function<auto(const vector<int> &, int)->bool> & is_satisfying) -> void
{
    print(cerr, "logical alias-reif {} unique_doms={} positions={} reif_pos={}{}",
        which, unique_domains, positions, reif_position, proofs ? " with proofs:" : ":");
    cerr << flush;

    set<vector<int>> expected, actual;
    build_expected(
        expected, [&](const vector<int> & unique_vals) -> bool {
            vector<int> lits;
            for (auto pos : positions)
                lits.push_back(unique_vals.at(pos));
            return is_satisfying(lits, unique_vals.at(reif_position));
        },
        unique_domains);
    println(cerr, " expecting {} solutions", expected.size());

    Problem p;
    vector<IntegerVariableID> unique_vars;
    for (const auto & [l, u] : unique_domains)
        unique_vars.emplace_back(p.create_integer_variable(Integer(l), Integer(u)));
    vector<IntegerVariableID> vs;
    for (auto pos : positions)
        vs.push_back(unique_vars.at(pos));
    auto r = unique_vars.at(reif_position);

    p.post(Logical_{vs, r});

    auto proof_name = proofs ? make_optional("logical_test_alias_reif") : nullopt;
    solve_for_tests(p, proof_name, actual, tuple{unique_vars});
    check_results(proof_name, expected, actual);
}

auto main(int argc, char * argv[]) -> int
{
    auto view_cfg = parse_view_wrap_config_from_argv(argc, argv);

    // Operand positions wrapped by the sweep. The fixed data tops out at 4
    // literals and the random data at 4, so a single-position index beyond
    // this would wrap nothing on any test — detect that and skip rather than
    // emitting a duplicate bare run.
    constexpr int n_positions = 4;
    if (view_cfg.single_position && (*view_cfg.single_position < 0 || *view_cfg.single_position >= n_positions)) {
        println(cerr, "logical view sweep: position {} out of range for n_positions = {}; skipping",
            *view_cfg.single_position, n_positions);
        return EXIT_SUCCESS;
    }

    bool run_dup = view_wrap_config_is_effectively_bare(view_cfg, n_positions);

    vector<tuple<vector<pair<int, int>>, pair<int, int>>> data = {
        {{{0, 1}, {0, 1}, {0, 1}}, {0, 1}},
        {{{0, 1}, {0, 1}, {0, 1}}, {-1, -1}},
        {{{0, 1}, {1, 1}, {0, 1}}, {0, 1}},
        {{{0, 1}, {0, 0}, {0, 1}}, {0, 1}},
        {{{2, 5}, {-2, -1}, {1, 3}, {2, 5}}, {0, 2}},
        {{{2, 5}, {2, 5}}, {0, 0}},
        {{{-2, 1}, {2, 5}, {-2, 1}, {2, 5}}, {-1, 1}},
        {{{}}, {0, 1}}};

    random_device rand_dev;
    mt19937 rand(rand_dev());
    uniform_int_distribution n_values_dist(1, 4);
    for (int x = 0; x < 10; ++x) {
        auto n_values = n_values_dist(rand);
        generate_random_data(rand, data, vector(n_values, random_bounds(-2, 2, 1, 3)), random_bounds(-1, 1, 0, 3));
    }

    for (bool proofs : {false, true}) {
        if (proofs && ! can_run_veripb())
            continue;
        for (auto & [r1d, r2d] : data) {
            auto r1 = r1d; // clang
            auto r2 = r2d;
            run_logical_test<And>("and", proofs, view_cfg, r1, r2, [&](const vector<int> & v, int r) {
                bool result = true;
                for (auto & i : v)
                    result = result && (i != 0);
                if (r2 == pair{-1, -1})
                    return result;
                else
                    return result == (r != 0);
            });
            run_logical_test<Or>("or", proofs, view_cfg, r1, r2, [&](const vector<int> & v, int r) {
                bool result = false;
                for (auto & i : v)
                    result = result || (i != 0);
                if (r2 == pair{-1, -1})
                    return result;
                else
                    return result == (r != 0);
            });
        }

        // Dup-variable cases: full_reif is a separate variable.
        auto and_sat = [](const vector<int> & v, int r) {
            bool result = true;
            for (auto & i : v)
                result = result && (i != 0);
            return result == (r != 0);
        };
        auto or_sat = [](const vector<int> & v, int r) {
            bool result = false;
            for (auto & i : v)
                result = result || (i != 0);
            return result == (r != 0);
        };
        // Dup tests use bare variables (the harness duplicates a handle into
        // several positions); only run them when no wrapping is in effect, to
        // avoid duplicating the bare coverage under every wrap.
        if (run_dup) {
            // {x, x, y} with full_reif distinct.
            run_dup_logical_test<And>("and", proofs, {{0, 1}, {0, 1}}, {0, 0, 1}, {0, 1}, and_sat);
            run_dup_logical_test<Or>("or", proofs, {{0, 1}, {0, 1}}, {0, 0, 1}, {0, 1}, or_sat);
            // {x, y, x} — non-adjacent dup.
            run_dup_logical_test<And>("and", proofs, {{0, 1}, {0, 1}}, {0, 1, 0}, {0, 1}, and_sat);
            run_dup_logical_test<Or>("or", proofs, {{0, 1}, {0, 1}}, {0, 1, 0}, {0, 1}, or_sat);
            // {x, x} alone — And/Or both reduce to x.
            run_dup_logical_test<And>("and", proofs, {{0, 1}}, {0, 0}, {0, 1}, and_sat);
            run_dup_logical_test<Or>("or", proofs, {{0, 1}}, {0, 0}, {0, 1}, or_sat);

            // full_reif aliases a lit. And({x, y, fr}, fr) ≡ fr → x∧y;
            // dually Or({x, y, fr}, fr) ≡ x∨y → fr. The reverse direction
            // of the ↔ collapses to a tautology when fr is on both sides,
            // so the constraint is intrinsically one-sided here.
            auto and_alias_sat = [](const vector<int> & v, int r) {
                // r ↔ AND(v including r) ≡ r → AND(others)
                if (r == 0)
                    return true;
                for (auto i : v)
                    if (i == 0)
                        return false;
                return true;
            };
            auto or_alias_sat = [](const vector<int> & v, int r) {
                // r ↔ OR(v including r) ≡ OR(others) → r
                if (r == 1)
                    return true;
                for (auto i : v)
                    if (i != 0)
                        return false;
                return true;
            };
            // 3-lit: {x, y, fr} with fr at position 2 (the third lit).
            run_alias_reif_logical_test<And>("and", proofs, {{0, 1}, {0, 1}, {0, 1}},
                {0, 1, 2}, 2, and_alias_sat);
            run_alias_reif_logical_test<Or>("or", proofs, {{0, 1}, {0, 1}, {0, 1}},
                {0, 1, 2}, 2, or_alias_sat);
            // Alias at a non-final position: {fr, y, x} with fr at lit 0.
            run_alias_reif_logical_test<And>("and", proofs, {{0, 1}, {0, 1}, {0, 1}},
                {0, 1, 2}, 0, and_alias_sat);
            run_alias_reif_logical_test<Or>("or", proofs, {{0, 1}, {0, 1}, {0, 1}},
                {0, 1, 2}, 0, or_alias_sat);
            // Edge: {fr} alone — constraint is fr ↔ fr, always true.
            run_alias_reif_logical_test<And>("and", proofs, {{0, 1}},
                {0}, 0, and_alias_sat);
            run_alias_reif_logical_test<Or>("or", proofs, {{0, 1}},
                {0}, 0, or_alias_sat);
            // Edge: {fr, fr} — two aliased lits both = fr.
            run_alias_reif_logical_test<And>("and", proofs, {{0, 1}},
                {0, 0}, 0, and_alias_sat);
            run_alias_reif_logical_test<Or>("or", proofs, {{0, 1}},
                {0, 0}, 0, or_alias_sat);
        }
    }

    return EXIT_SUCCESS;
}
