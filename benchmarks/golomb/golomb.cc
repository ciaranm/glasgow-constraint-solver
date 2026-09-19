/* Optimal Golomb rulers: n marks, starting at zero, whose pairwise
 * differences are all distinct, with the last mark as small as possible.
 *
 * This is the textbook case for a bounds consistent all-different: the
 * differences have domains up to n^2 wide, every other constraint on them is a
 * linear one that reads and writes only bounds, and the search branches on the
 * marks, smallest value first, which never makes a hole either. So under
 * --all-different=bc nothing makes a hole at all, and under gac only the
 * all-different does. The model follows Gecode's golomb-ruler example: the
 * difference between marks i and j is at least the sum of the first j - i
 * integers, and the first difference is smaller than the last to break the
 * mirror symmetry. */

#include <gcs/constraints/all_different.hh>
#include <gcs/constraints/comparison.hh>
#include <gcs/constraints/equals.hh>
#include <gcs/constraints/linear.hh>
#include <gcs/problem.hh>
#include <gcs/search_heuristics.hh>
#include <gcs/solve.hh>

#include <examples/benchmark_cli.hh>

#include <cstdlib>
#include <iostream>
#include <vector>

#include <cxxopts.hpp>

using namespace gcs;

using std::cerr;
using std::cout;
using std::endl;
using std::make_optional;
using std::nullopt;
using std::string;
using std::vector;

auto main(int argc, char * argv[]) -> int
{
    cxxopts::Options options("Golomb Ruler");
    cxxopts::ParseResult options_vars;

    try {
        options.add_options("Program Options")                                              //
            ("help", "Display help information")                                            //
            ("prove", "Create a proof")                                                     //
            ("proof-files-basename", "Basename for the .opb and .pbp files",                //
                cxxopts::value<string>()->default_value("golomb"))                          //
            ("timeout", "Abort the solve after this many seconds (0 = no limit)",           //
                cxxopts::value<double>()->default_value("0"))                               //
            ("all-different", "Consistency for the AllDifferent constraint: 'gac' or 'bc'", //
                cxxopts::value<string>()->default_value("gac"));

        options.add_options()("size", "Number of marks", cxxopts::value<int>()->default_value("10"));

        options.parse_positional({"size"});
        options_vars = options.parse(argc, argv);
    }
    catch (const cxxopts::exceptions::exception & e) {
        cerr << "Error: " << e.what() << endl;
        return EXIT_FAILURE;
    }

    if (options_vars.contains("help")) {
        cout << options.help() << endl;
        return EXIT_SUCCESS;
    }

    const string all_different_mode = options_vars["all-different"].as<string>();
    AllDifferentConsistency all_different_consistency = consistency::GAC{};
    if (all_different_mode == "bc")
        all_different_consistency = consistency::BC{};
    else if (all_different_mode != "gac") {
        cerr << "Error: --all-different must be 'gac' or 'bc'." << endl;
        return EXIT_FAILURE;
    }

    int n = options_vars["size"].as<int>();
    Problem p;

    vector<IntegerVariableID> marks;
    for (int i = 0; i < n; ++i)
        marks.push_back(p.create_integer_variable(0_i, Integer{n * n}));
    p.post(Equals{marks[0], 0_c});
    for (int i = 0; i + 1 < n; ++i)
        p.post(LessThan{marks[i], marks[i + 1]});

    vector<IntegerVariableID> differences;
    IntegerVariableID first_difference = 0_c, last_difference = 0_c;
    for (int i = 0; i < n; ++i)
        for (int j = i + 1; j < n; ++j) {
            auto gap = j - i;
            auto d = p.create_integer_variable(Integer{gap * (gap + 1) / 2}, Integer{n * n});
            p.post(LinearEquality{WeightedSum{} + 1_i * marks[j] + -1_i * marks[i] + -1_i * d, 0_i});
            differences.push_back(d);
            if (i == 0 && j == 1)
                first_difference = d;
            if (i == n - 2 && j == n - 1)
                last_difference = d;
        }
    p.post(AllDifferent{differences}.with_consistency(all_different_consistency));
    p.post(LessThan{first_difference, last_difference});

    p.minimise(marks[n - 1]);

    auto stats = bench::solve_with_timeout(options_vars["timeout"].as<double>(), p,
        SolveCallbacks{.solution = [&](const CurrentState & s) -> bool {
                           cout << "length " << s(marks[n - 1]) << ":";
                           for (const auto & m : marks)
                               cout << " " << s(m);
                           cout << endl;
                           return true;
                       },
            .branch = branch_with(variable_order::in_order(marks), value_order::smallest_first())},
        options_vars.contains("prove") ? make_optional<ProofOptions>(options_vars["proof-files-basename"].as<string>()) : nullopt);

    cout << stats;

    return EXIT_SUCCESS;
}
