#include <gcs/constraints/abs.hh>
#include <gcs/constraints/all_different.hh>
#include <gcs/constraints/among.hh>
#include <gcs/constraints/comparison.hh>
#include <gcs/constraints/equals.hh>
#include <gcs/constraints/global_cardinality.hh>
#include <gcs/constraints/in.hh>
#include <gcs/constraints/innards/constraints_test_utils.hh>
#include <gcs/constraints/linear.hh>
#include <gcs/constraints/logical.hh>
#include <gcs/problem.hh>
#include <gcs/solve.hh>

#include <cstdlib>
#include <functional>
#include <iostream>
#include <optional>
#include <set>
#include <string>
#include <tuple>
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
using std::function;
using std::make_optional;
using std::nullopt;
using std::optional;
using std::pair;
using std::set;
using std::string;
using std::tuple;
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

// A view gets its own bit vector as soon as a proof uses it, and how a
// constraint's rows spell the view must not depend on whether something else
// used it first. These are the shapes that once did depend on it.

namespace
{
    // GlobalCardinality over {u0, 5 - u1, u2}, with a linear constraint over
    // 5 - u1 posted after it (issue #1200). GlobalCardinality's rows name only
    // the view's eq atoms, which did not register it, so they spelled them
    // through u1; the linear row then registered the view, the proof spelled the
    // atoms over its bits, and the Hall pols stranded.
    auto run_gcc_then_linear_test(bool proofs, bool gac) -> void
    {
        print(cerr, "view registration: GlobalCardinality then a linear row over its view{}{}", gac ? " (GAC)" : " (BC)",
            proofs ? " with proofs:" : ":");
        cerr << flush;

        vector<pair<int, int>> ranges{{0, 3}, {1, 5}, {1, 4}, {0, 3}, {1, 4}};
        auto is_satisfying = [](const vector<int> & u) {
            vector<int> positions{u[0], 5 - u[1], u[2]};
            int ones = 0, threes = 0;
            for (auto v : positions) {
                ones += (v == 1);
                threes += (v == 3);
            }
            return ones == u[3] && threes == u[4] && 5 - u[1] <= 4;
        };
        set<tuple<vector<int>>> expected, actual;
        build_expected(expected, is_satisfying, ranges);
        println(cerr, " expecting {} solutions", expected.size());

        auto post = [&](Problem & p) -> vector<IntegerVariableID> {
            vector<IntegerVariableID> u;
            for (auto & [lo, hi] : ranges)
                u.push_back(p.create_integer_variable(Integer{lo}, Integer{hi}));
            auto view = -u[1] + 5_i;
            GlobalCardinality gcc{{u[0], view, u[2]}, {1_i, 3_i}, {u[3], u[4]}};
            if (gac)
                gcc.with_consistency(consistency::GAC{});
            p.post(gcc);
            p.post(WeightedSum{} + 1_i * view <= 4_i);
            return u;
        };

        // Under the harness's random branching and then under the default
        // branching: whether a Hall pol meets the rows written before the
        // linear row depends on the search path, and the default one does.
        auto proof_name = proofs ? make_optional<string>(string{"view_registration_gcc_"} + (gac ? "gac" : "bc")) : nullopt;
        {
            Problem p;
            auto u = post(p);
            solve_for_tests(p, proof_name, actual, tuple{u});
            check_results(proof_name, expected, actual);
        }
        {
            Problem p;
            auto u = post(p);
            actual.clear();
            last_run_truncated() = false;
            solve_with(p,
                SolveCallbacks{
                    .solution = [&](const CurrentState & s) -> bool { return actual.emplace(extract_from_state(s, u)), true; }, //
                    .stats_report = silent_stats_report()                                                                       //
                },
                proof_name ? make_optional<ProofOptions>(ProofFileNames{*proof_name}) : nullopt);
            check_results(proof_name, expected, actual);
        }
    }

    // A view too wide for a bit vector of its own, x + c with x unbounded and c
    // near -2^61, used only through its literals. Nothing can register such a
    // view, so its literals stay spelled through x; registering it on literal
    // use, as every other view now is, would overflow sizing the bit vector.
    auto run_wide_view_literal_test(bool proofs) -> void
    {
        println(cerr, "view registration: literals on a view too wide for a bit vector{}", proofs ? " with proofs" : "");
        Problem p;
        auto x = p.create_integer_variable(Integer::min_bounded_value(), Integer::max_bounded_value(), "x");
        auto b = p.create_integer_variable(0_i, 1_i, "b");
        auto c = Integer{-2305843009213693962LL};
        auto v = x + c;
        p.post(Or{{v >= c, b == 1_i}, innards::TrueLiteral{}});
        p.post(Or{{v < c, b == 0_i}, innards::TrueLiteral{}});
        p.post(Equals{x, ConstantIntegerVariableID{0_i}});

        long long solutions = 0;
        string proof_name = "view_registration_wide";
        solve_with(p,
            SolveCallbacks{
                .solution = [&](const CurrentState &) -> bool {
                    ++solutions;
                    return true;
                },
                .stats_report = silent_stats_report() //
            },
            proofs ? make_optional<ProofOptions>(ProofFileNames{proof_name}) : nullopt);
        if (solutions != 1) // x = 0, so v = c, which forces b = 0
            throw UnexpectedException{"wrong number of solutions"};
        if (proofs)
            verify_proof_and_clean_up(proof_name);
    }

    // Maximising x (or minimising -x) while another constraint uses -x (issue
    // #1206). `min:` is written over x's own bits, deliberately, so that it
    // matches what cake_pb_cp derives from `(maximize x)`; the `e` line after
    // each `soli` restates it, and used to spell -x over the view's bits once a
    // constraint had registered the view. Some of these constraints name the
    // view as an integer term and some only name its literals, which now
    // registers it as well.
    auto run_objective_test(bool proofs, const string & which, bool minimise_negation) -> void
    {
        print(cerr, "view registration: {} -x, then {}{}", which, minimise_negation ? "minimise(-x)" : "maximise(x)", proofs ? " with proofs:" : ":");
        cerr << flush;

        Problem p;
        auto x = p.create_integer_variable(0_i, 3_i, "x");
        auto y = p.create_integer_variable(-3_i, 3_i, "y");
        auto z = p.create_integer_variable(-3_i, 3_i, "z");
        function<bool(int, int, int)> holds;
        if (which == "less_than") {
            p.post(LessThan{-x, y});
            holds = [](int x, int y, int) { return -x < y; };
        }
        else if (which == "in") {
            p.post(In{-x, vector<Integer>{-3_i, -1_i, 0_i}});
            holds = [](int x, int, int) { return x == 3 || x == 1 || x == 0; };
        }
        else if (which == "among") {
            p.post(Among{{-x, y}, {-2_i, 0_i}, z});
            holds = [](int x, int y, int z) { return ((-x == -2 || -x == 0) + (y == -2 || y == 0)) == z; };
        }
        else if (which == "all_different") {
            p.post(AllDifferent{{-x, y}});
            holds = [](int x, int y, int) { return -x != y; };
        }
        else {
            p.post(Abs{-x, z});
            holds = [](int x, int, int z) { return z == x; };
        }
        if (minimise_negation)
            p.minimise(-x);
        else
            p.maximise(x);

        optional<int> expected;
        for (int xv = 0; xv <= 3; ++xv)
            for (int yv = -3; yv <= 3; ++yv)
                for (int zv = -3; zv <= 3; ++zv)
                    if (holds(xv, yv, zv) && (! expected || xv > *expected))
                        expected = xv;

        optional<int> best;
        auto proof_name = string{"view_registration_objective_"} + which + (minimise_negation ? "_min" : "_max");
        solve_with(p,
            SolveCallbacks{
                .solution = [&](const CurrentState & s) -> bool {
                    best = s(x).raw_value;
                    return true;
                },
                .stats_report = silent_stats_report() //
            },
            proofs ? make_optional<ProofOptions>(ProofFileNames{proof_name}) : nullopt);
        println(cerr, " optimum x = {}, expected {}", best ? std::to_string(*best) : "none", expected ? std::to_string(*expected) : "none");
        if (best != expected)
            throw UnexpectedException{"wrong optimum"};
        if (proofs)
            verify_proof_and_clean_up(proof_name);
    }
}

auto main(int argc, char * argv[]) -> int
{
    establish_and_announce_seed(argc, argv);

    for (bool proofs : {false, true}) {
        if (proofs && ! can_run_veripb())
            continue;
        for (bool gac : {false, true})
            run_gcc_then_linear_test(proofs, gac);
        run_wide_view_literal_test(proofs);
        for (const auto & which : {"less_than", "in", "among", "all_different", "abs"})
            for (bool minimise_negation : {false, true})
                run_objective_test(proofs, which, minimise_negation);
    }

    return EXIT_SUCCESS;
}
