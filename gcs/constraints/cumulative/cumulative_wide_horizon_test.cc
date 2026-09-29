#include <gcs/constraints/cumulative.hh>
#include <gcs/constraints/disjunctive_2d.hh>
#include <gcs/constraints/innards/constraints_test_utils.hh>
#include <gcs/presolvers/cumulative_strengthening.hh>
#include <gcs/presolvers/inferred_cumulative.hh>
#include <gcs/presolvers/inferred_disjunctive.hh>
#include <gcs/problem.hh>
#include <gcs/solve.hh>

#include <cstdlib>
#include <fstream>
#include <iostream>
#include <string>
#include <vector>
#include <version>

#if defined(__cpp_lib_print) && defined(__cpp_lib_format)
#include <print>
#else
#include <fmt/core.h>
#include <fmt/ostream.h>
#endif

using std::cerr;
using std::ifstream;
using std::make_optional;
using std::make_shared;
using std::string;
using std::vector;

#if defined(__cpp_lib_print) && defined(__cpp_lib_format)
using std::println;
#else
using fmt::println;
#endif

using namespace gcs;
using namespace gcs::test_innards;

// Cumulative's per-(task, time) flags are named when something first looks one
// up, not per time point of every task's window with the model (#1111), and a
// derived Cumulative asks for its donor's flags and rows the same way (#1130). Named
// up front, three unit tasks free across a horizon of 10^5 wrote about 900,000
// names into the variables map before search started, for a solve that cites a
// handful of them. The variables map has one entry per name, so counting the
// per-time families in it is the direct test.
namespace
{
    constexpr long long horizon = 100'000;

    // The most per-time names either solve below may write. Both find their
    // first solution in a few nodes and cite flags only at the few time points
    // their rules look at, so this is generous, and still four orders of
    // magnitude below naming the horizon.
    constexpr long long most_names = 200;

    auto fail(const string & message) -> void
    {
        println(cerr, "cumulative wide horizon test failure: {}", message);
        std::exit(EXIT_FAILURE);
    }

    auto per_time_names(const string & proof_name) -> long long
    {
        ifstream varmap{proof_name + ".varmap"};
        if (! varmap)
            fail("could not read " + proof_name + ".varmap");
        long long count = 0;
        string line;
        while (getline(varmap, line))
            for (const auto * family : {"][cb]\"", "][ca]\"", "][cact]\"", "][cc]\""})
                if (line.find(family) != string::npos)
                    ++count;
        return count;
    }

    auto check(Problem & p, const string & proof_name) -> void
    {
        long long solutions = 0;
        solve_with(p, SolveCallbacks{.solution = [&](const CurrentState &) -> bool {
            ++solutions;
            return false;
        }},
            make_optional<ProofOptions>(ProofFileNames{proof_name}));
        if (solutions != 1)
            fail(proof_name + ": expected a solution");

        auto names = per_time_names(proof_name);
        println(cerr, "{}: {} per-time flag names over a horizon of {}", proof_name, names, horizon);
        if (names > most_names)
            fail(proof_name + ": " + std::to_string(names) + " per-time flags named, so they are being named up front again");

        if (can_run_veripb())
            verify_proof_and_clean_up(proof_name);
    }
}

auto main(int argc, char * argv[]) -> int
{
    establish_and_announce_seed(argc, argv);

    // Three unit tasks, two at a time, free across the horizon.
    {
        Problem p;
        vector<IntegerVariableID> starts;
        for (int i = 0; i < 3; ++i)
            starts.push_back(p.create_integer_variable(0_i, Integer{horizon}));
        p.post(Cumulative{starts, vector<Integer>(3, 1_i), vector<Integer>(3, 1_i), 2_i});
        check(p, "cumulative_wide_horizon");
    }

    // The same through Disjunctive2D's projection, which keys its flags by
    // Cumulative's scheme and names them the same way: unit squares free across
    // the horizon in x, in a y window of four.
    {
        Problem p;
        vector<IntegerVariableID> xs, ys;
        for (int i = 0; i < 3; ++i) {
            xs.push_back(p.create_integer_variable(0_i, Integer{horizon}));
            ys.push_back(p.create_integer_variable(0_i, 3_i));
        }
        p.post(Disjunctive2D{xs, ys, vector<Integer>(3, 1_i), vector<Integer>(3, 1_i)}.with_rules(
            Disjunctive2DRules{.cumulative_projection = CumulativeRules{}}));
        check(p, "cumulative_wide_horizon_projection");
    }

    // A derived Cumulative over the same kind of donor, one per presolver
    // that installs one (#1130). Each derives its rows from the donor's and
    // pins the donor's flags, and did both for every time point of every
    // window at install, which named the donor's flags over the horizon and
    // wrote a proof linear in it. Heights of two on a capacity of three make
    // every pair conflict, which is a clique and a cover; on a capacity of
    // five, two fit and three do not, which strengthening rounds down to four.
    {
        auto three_tasks = [](Problem & p, Integer capacity) {
            vector<IntegerVariableID> starts;
            for (int i = 0; i < 3; ++i)
                starts.push_back(p.create_integer_variable(0_i, Integer{horizon}));
            p.post(Cumulative{starts, vector<Integer>(3, 2_i), vector<Integer>(3, 2_i), capacity});
        };

        {
            auto stats = make_shared<InferredDisjunctiveStats>();
            Problem p;
            three_tasks(p, 3_i);
            p.add_presolver(InferredDisjunctive{stats});
            check(p, "cumulative_wide_horizon_inferred_disjunctive");
            if (0 == stats->cliques_posted)
                fail("inferred disjunctive posted no clique, so nothing was derived");
        }

        {
            auto stats = make_shared<InferredCumulativeStats>();
            Problem p;
            three_tasks(p, 3_i);
            p.add_presolver(InferredCumulative{stats});
            check(p, "cumulative_wide_horizon_inferred_cumulative");
            if (0 == stats->cuts_posted)
                fail("inferred cumulative posted no cut, so nothing was derived");
        }

        {
            auto stats = make_shared<CumulativeStrengtheningStats>();
            Problem p;
            three_tasks(p, 5_i);
            p.add_presolver(CumulativeStrengthening{stats});
            check(p, "cumulative_wide_horizon_strengthening");
            if (0 == stats->derived.constraints)
                fail("strengthening installed no derived constraint, so nothing was derived");
            // The rows it derived, which is the other half of what used to
            // be linear in the horizon: one per stretch at install, and one
            // per time point anything cited since.
            println(cerr, "cumulative_wide_horizon_strengthening: {} capacity rows derived", stats->derived.capacity_rows);
            if (stats->derived.capacity_rows > static_cast<std::size_t>(most_names))
                fail("strengthening derived " + std::to_string(stats->derived.capacity_rows) +
                    " capacity rows, so they are being derived up front again");
        }
    }

    return EXIT_SUCCESS;
}
