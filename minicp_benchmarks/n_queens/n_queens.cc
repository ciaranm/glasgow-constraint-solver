#include <gcs/constraints/arithmetic.hh>
#include <gcs/constraints/not_equals.hh>
#include <gcs/problem.hh>
#include <gcs/search_heuristics.hh>
#include <gcs/solve.hh>

#include <cstdlib>
#include <iostream>
#include <optional>
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
    cxxopts::Options options("N Queens Example");
    cxxopts::ParseResult options_vars;

    try {
        options.add_options("Program Options")
            ("help", "Display help information")
            ("prove", "Create a proof");

        options.add_options()
            ("size", "Size of the problem to solve", cxxopts::value<int>()->default_value("88"))
            ("all", "Find all solutions");

        options.parse_positional({"size"});
        options_vars = options.parse(argc, argv);
    }
    catch (const cxxopts::exceptions::exception & e) {
        cerr << "Error: " << e.what() << endl;
        cerr << "Try " << argv[0] << " --help" << endl;
        return EXIT_FAILURE;
    }

    if (options_vars.contains("help")) {
        cout << "Usage: " << argv[0] << " [options] [size]" << endl;
        cout << endl;
        cout << options.help() << endl;
        return EXIT_SUCCESS;
    }

    cout << "Replicating the n-Queens benchmark." << endl;
    cout << "See Laurent D. Michel, Pierre Schaus, Pascal Van Hentenryck:" << endl;
    cout << "\"MiniCP: a lightweight solver for constraint programming.\"" << endl;
    cout << "Math. Program. Comput. 13(1): 133-184 (2021)." << endl;
    cout << "This should take 49339390 recursions with default options." << endl;
    cout << endl;

    int size = options_vars["size"].as<int>();
    Problem p;

    auto queens = p.create_integer_variable_vector(size, 0_i, Integer{size - 1}, "queen");

    for (int i = 0; i < size; ++i) {
        for (int j = i + 1; j < size; ++j) {
            p.post(NotEquals{queens[i], queens[j]});
            p.post(NotEquals{queens[i] + Integer{j - i}, queens[j]});
            p.post(NotEquals{queens[i] + -Integer{j - i}, queens[j]});
        }
    }

    auto stats = solve_with(p,
        SolveCallbacks{
            .solution = [&](const CurrentState & s) -> bool {
                cout << "solution:";
                for (auto & v : queens)
                    cout << " " << s(v);
                cout << endl;

                return options_vars.contains("all");
            },
            .branch = branch_with(variable_order::dom(queens), value_order::smallest_in())},
        options_vars.contains("prove") ? make_optional<ProofOptions>("n_queens") : nullopt);

    cout << stats;

    return EXIT_SUCCESS;
}
