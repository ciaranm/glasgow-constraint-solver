#include <gcs/constraints/all_different.hh>
#include <gcs/constraints/constraints_test_utils.hh>
#include <gcs/constraints/global_cardinality.hh>
#include <gcs/constraints/not_equals.hh>

#include <gcs/problem.hh>
#include <gcs/solve.hh>

#include <cstdlib>
#include <functional>
#include <iostream>
#include <random>
#include <set>
#include <tuple>
#include <utility>
#include <vector>

#include <fmt/core.h>
#include <fmt/ostream.h>
#include <fmt/ranges.h>

using std::cerr;
using std::flush;
using std::function;
using std::iota;
using std::make_optional;
using std::mt19937;
using std::nullopt;
using std::pair;
using std::random_device;
using std::set;
using std::string;
using std::to_string;
using std::tuple;
using std::variant;
using std::vector;

using fmt::print;
using fmt::println;

using namespace gcs;
using namespace gcs::test_innards;

struct GCCTestInstance
{
    int num_vars;
    int num_vals;
    vector<pair<int, int>> var_ranges;
    vector<pair<int, int>> count_ranges;
};

auto run_gcc_test(GCCTestInstance data, bool proof)
{
    Problem p{};
    vector<IntegerVariableID> vars;
    vector<Integer> vals;
    vector<IntegerVariableID> counts;
    for (int i = 0; i < data.num_vars; i++) {
        vars.emplace_back(p.create_integer_variable(Integer{data.var_ranges[i].first}, Integer{data.var_ranges[i].second}));
    }

    for (int i = 0; i < data.num_vals; i++) {
        vals.emplace_back(i);
        counts.emplace_back(p.create_integer_variable(Integer{data.count_ranges[i].first}, Integer{data.count_ranges[i].second}));
    }

    p.post(GlobalCardinality{vars, &vals, counts});

    solve_with(p, SolveCallbacks{.solution = [&](const CurrentState & s) -> bool {
        return false;
    }},
        proof ? make_optional(ProofOptions{"gcc_test"}) : nullopt);

    if (proof) {
        system("veripb --progressBar gcc_test.opb gcc_test.pbp");
    }
}
auto main(int, char *[]) -> int
{
    auto MAX_NUM_VARS = 20;

    auto test0 = GCCTestInstance{};
    test0.num_vars = 3;
    test0.num_vals = 3;
    test0.var_ranges = {pair{0, 2}, pair{0, 2}, {0, 2}};
    test0.count_ranges = {pair{0, 2}, pair{0, 2}, pair{0, 2}};

    auto test1 = GCCTestInstance{};
    test1.num_vars = 6;
    test1.num_vals = 4;
    test1.var_ranges = {pair{0, 3}, pair{0, 3}, pair{0, 3}, pair{0, 3}, pair{0, 3}, pair{0, 3}};
    test1.count_ranges = {pair{0, 6}, pair{0, 6}, pair{0, 6}, pair{0, 6}};

    run_gcc_test(test0, true);
    run_gcc_test(test1, true);

    for (int num_vars = 3; num_vars < MAX_NUM_VARS; num_vars++) {
        for (int num_vals = 2; num_vals < num_vars; num_vals++) {

            auto test = GCCTestInstance{num_vars, num_vals, vector<pair<int, int>>(num_vars, pair{0, num_vals - 1}), vector<pair<int, int>>(num_vals, pair{0, num_vars})};
            run_gcc_test(test, true);
        }
    }
    return EXIT_SUCCESS;
}
