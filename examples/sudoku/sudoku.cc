#include <gcs/constraints/all_different.hh>
#include <gcs/constraints/all_different/vc_all_different.hh>
#include <gcs/constraints/equals.hh>
#include <gcs/constraints/linear.hh>
#include <gcs/problem.hh>
#include <gcs/solve.hh>

#include <examples/benchmark_cli.hh>

#include <cstdlib>
#include <fstream>
#include <iostream>
#include <sstream>
#include <vector>

#include <cxxopts.hpp>

#include <version>

#if defined(__cpp_lib_print) && defined(__cpp_lib_format)
#include <format>
#include <print>
#else
#include <fmt/core.h>
#include <fmt/ostream.h>
#endif

using namespace gcs;

using std::cerr;
using std::cout;
using std::getline;
using std::ifstream;
using std::istringstream;
using std::make_optional;
using std::nullopt;
using std::string;
using std::vector;

#if defined(__cpp_lib_print) && defined(__cpp_lib_format)
using std::format;
using std::print;
using std::println;
#else
using fmt::format;
using fmt::print;
using fmt::println;
#endif

using namespace std::literals::string_literals;

auto main(int argc, char * argv[]) -> int
{
    cxxopts::Options options("Sudoku Example");
    cxxopts::ParseResult options_vars;

    try {
        options.add_options("Program Options")                                                                             //
            ("help", "Display help information")                                                                           //
            ("prove", "Create a proof")                                                                                    //
            ("proof-files-basename", "Basename for the .opb and .pbp files",                                               //
                cxxopts::value<string>()->default_value("sudoku"))                                                         //
            ("stats", "Print solve statistics")                                                                            //
            ("trace", "Trace progress")                                                                                    //
            ("timeout", "Abort the solve after this many seconds (0 = no limit)",                                          //
                cxxopts::value<double>()->default_value("0"))                                                              //
            ("all-different", "All-different encoding to use: 'gac', 'bc', 'vc', or 'not-equals' (the not-equals clique)", //
                cxxopts::value<string>()->default_value("gac"));

        options.add_options("Extended Options")   //
            ("xv", "Solve the xv puzzle instead") //
            ("puzzle",
                "Solve the puzzle in this file instead: n rows of n whitespace-separated "
                "values, for n = 4, 9, 16, 25, ..., with 0 or . for a blank",
                cxxopts::value<string>()) //
            ("all", "Find all solutions");

        options_vars = options.parse(argc, argv);
    }
    catch (const cxxopts::exceptions::exception & e) {
        println(cerr, "Error: {}", e.what());
        println(cerr, "Try {} --help", argv[0]);
        return EXIT_FAILURE;
    }

    if (options_vars.contains("help")) {
        println("Usage: {} [options]", argv[0]);
        println("");
        cout << options.help() << std::endl;
        return EXIT_SUCCESS;
    }

    const string all_different_mode = options_vars["all-different"].as<string>();
    if (all_different_mode != "gac" && all_different_mode != "bc" && all_different_mode != "vc" && all_different_mode != "not-equals") {
        println(cerr, "Error: --all-different must be 'gac', 'bc', 'vc', or 'not-equals'.");
        return EXIT_FAILURE;
    }

    if (options_vars.contains("xv") && options_vars.contains("puzzle")) {
        println(cerr, "Error: --xv and --puzzle are alternatives.");
        return EXIT_FAILURE;
    }

    Problem p;

    int size = 3;
    int n = size * size;

    enum NXV
    {
        N, // no v or x rule
        V, // must sum to 5
        X, // must sum to 10
        O  // must not sum to 5 or 10
    };

    vector<vector<int>> predef;
    vector<vector<NXV>> horizontal_xvs, vertical_xvs;

    if (options_vars.contains("xv")) {
        // https://www.youtube.com/watch?v=9ATC_uBF8ow
        predef = {
            {0, 0, 0, 0, 0, 0, 0, 0, 0}, //
            {0, 0, 0, 0, 0, 0, 0, 0, 0}, //
            {0, 0, 0, 0, 0, 0, 0, 0, 0}, //
            {0, 0, 0, 0, 0, 0, 0, 0, 0}, //
            {0, 0, 0, 0, 0, 0, 0, 0, 0}, //
            {0, 5, 0, 3, 0, 8, 0, 2, 0}, //
            {2, 0, 5, 0, 3, 0, 6, 0, 9}, //
            {0, 9, 0, 4, 0, 6, 0, 1, 0}, //
            {0, 0, 0, 0, 0, 0, 0, 0, 0}  //
        };

        horizontal_xvs = {
            {O, O, O, O, O, O, O, O}, //
            {O, O, O, O, O, O, O, O}, //
            {O, O, O, O, O, O, O, O}, //
            {O, O, O, O, O, O, O, O}, //
            {O, O, O, O, O, O, O, O}, //
            {O, O, O, O, O, O, O, O}, //
            {O, O, O, O, O, O, O, O}, //
            {O, O, O, O, O, O, O, O}, //
            {O, O, O, O, O, O, O, O}  //
        };

        vertical_xvs = {
            {O, O, O, O, O, O, O, O}, //
            {O, X, O, O, O, O, O, O}, //
            {X, O, X, O, O, O, O, O}, //
            {O, X, O, O, O, O, O, O}, //
            {X, O, X, O, O, O, O, O}, //
            {O, X, O, O, O, O, O, O}, //
            {X, O, X, O, O, O, O, O}, //
            {O, X, O, O, O, O, O, O}, //
            {O, O, O, O, O, O, O, O}  //
        };
    }
    else if (options_vars.contains("puzzle")) {
        ifstream file{options_vars["puzzle"].as<string>()};
        if (! file) {
            println(cerr, "Error: cannot read {}", options_vars["puzzle"].as<string>());
            return EXIT_FAILURE;
        }

        string line;
        while (getline(file, line)) {
            istringstream tokens{line};
            vector<int> row;
            string token;
            while (tokens >> token)
                row.push_back(token == "." ? 0 : std::stoi(token));
            if (! row.empty())
                predef.push_back(move(row));
        }

        n = static_cast<int>(predef.size());
        size = 1;
        while (size * size < n)
            ++size;
        bool ok = n > 0 && size * size == n;
        for (const auto & row : predef)
            for (auto value : row)
                ok = ok && static_cast<int>(row.size()) == n && value >= 0 && value <= n;
        if (! ok) {
            println(cerr, "Error: {} is not an n by n grid of values between 0 and n, for n a square", options_vars["puzzle"].as<string>());
            return EXIT_FAILURE;
        }
    }
    else {
        // https://abcnews.go.com/blogs/headlines/2012/06/can-you-solve-the-hardest-ever-sudoku
        predef = {
            {8, 0, 0, 0, 0, 0, 0, 0, 0}, //
            {0, 0, 3, 6, 0, 0, 0, 0, 0}, //
            {0, 7, 0, 0, 9, 0, 2, 0, 0}, //
            {0, 5, 0, 0, 0, 7, 0, 0, 0}, //
            {0, 0, 0, 0, 4, 5, 7, 0, 0}, //
            {0, 0, 0, 1, 0, 0, 0, 3, 0}, //
            {0, 0, 1, 0, 0, 0, 0, 6, 8}, //
            {0, 0, 8, 5, 0, 0, 0, 1, 0}, //
            {0, 9, 0, 0, 0, 0, 4, 0, 0}  //
        };
    }

    vector<vector<IntegerVariableID>> grid;

    for (int r = 0; r < n; ++r)
        grid.emplace_back(p.create_integer_variable_vector(n, 1_i, Integer{n}, format("grid[{}]", r)));

    auto post_all_different = [&](const vector<IntegerVariableID> & vars) {
        if (all_different_mode == "gac")
            p.post(AllDifferent{vars});
        else if (all_different_mode == "bc")
            p.post(AllDifferent{vars} //
                    .with_consistency(consistency::BC{}));
        else if (all_different_mode == "vc")
            p.post(AllDifferent{vars} //
                    .with_consistency(consistency::VC{}));
        else
            for (unsigned i = 0; i < vars.size(); ++i)
                for (unsigned j = i + 1; j < vars.size(); ++j)
                    p.post(NotEquals{vars[i], vars[j]});
    };

    for (int r = 0; r < n; ++r)
        post_all_different(grid[r]);

    for (int c = 0; c < n; ++c) {
        vector<IntegerVariableID> column;
        for (int r = 0; r < n; ++r)
            column.push_back(grid[r][c]);
        post_all_different(column);
    }

    for (int r = 0; r < size; ++r)
        for (int c = 0; c < size; ++c) {
            vector<IntegerVariableID> box;
            for (int rr = 0; rr < size; ++rr)
                for (int cc = 0; cc < size; ++cc)
                    box.push_back(grid[r * size + rr][c * size + cc]);
            post_all_different(box);
        }

    for (int r = 0; r < n; ++r)
        for (int c = 0; c < n; ++c)
            if (predef[r][c] != 0)
                p.post(Equals{grid[r][c], constant_variable(Integer{predef[r][c]})});

    if (! vertical_xvs.empty()) {
        for (int c = 0; c < n; ++c)
            for (int r = 0; r < n - 1; ++r)
                switch (vertical_xvs[c][r]) {
                case N: break;
                case V:
                    p.post(LinearEquality{WeightedSum{} + 1_i * grid[r][c] + 1_i * grid[r + 1][c], 5_i} //
                            .with_consistency(consistency::Tabulated{}));
                    break;
                case X:
                    p.post(LinearEquality{WeightedSum{} + 1_i * grid[r][c] + 1_i * grid[r + 1][c], 10_i} //
                            .with_consistency(consistency::Tabulated{}));
                    break;
                case O:
                    auto sum = p.create_integer_variable(0_i, Integer{n * 2});
                    p.post(NotEquals{sum, 5_c});
                    p.post(NotEquals{sum, 10_c});
                    p.post(LinearEquality{WeightedSum{} + 1_i * grid[r][c] + 1_i * grid[r + 1][c] + -1_i * sum, 0_i} //
                            .with_consistency(consistency::Tabulated{}));
                    break;
                }

        for (int r = 0; r < n; ++r)
            for (int c = 0; c < n - 1; ++c)
                switch (horizontal_xvs[r][c]) {
                case N: break;
                case V:
                    p.post(LinearEquality{WeightedSum{} + 1_i * grid[r][c] + 1_i * grid[r][c + 1], 5_i} //
                            .with_consistency(consistency::Tabulated{}));
                    break;
                case X:
                    p.post(LinearEquality{WeightedSum{} + 1_i * grid[r][c] + 1_i * grid[r][c + 1], 10_i} //
                            .with_consistency(consistency::Tabulated{}));
                    break;
                case O:
                    auto sum = p.create_integer_variable(0_i, Integer{n * 2});
                    p.post(NotEquals{sum, 5_c});
                    p.post(NotEquals{sum, 10_c});
                    p.post(LinearEquality{WeightedSum{} + 1_i * grid[r][c] + 1_i * grid[r][c + 1] + -1_i * sum, 0_i} //
                            .with_consistency(consistency::Tabulated{}));
                    break;
                }
    }

    auto stats = bench::solve_with_timeout(options_vars["timeout"].as<double>(), p,
        SolveCallbacks{//
            .solution = [&](const CurrentState & s) -> bool {
                for (const auto & row : grid) {
                    bool first = true;
                    for (const auto & box : row) {
                        if (! first)
                            print(" ");
                        print("{}", s(box));
                        first = false;
                    }
                    println("");
                }
                println("");
                return options_vars.contains("all");
            },
            .trace = [&](const CurrentState & s) -> bool {
                if (! options_vars.contains("trace"))
                    return true;

                for (const auto & row : grid) {
                    bool first = true;
                    for (const auto & box : row) {
                        if (! first)
                            print(" ");
                        if (s.has_single_value(box))
                            print("{}", s(box));
                        else
                            print(".");

                        first = false;
                    }
                    println("");
                }
                println("");
                return true;
            }},
        options_vars.contains("prove") ? make_optional<ProofOptions>(options_vars["proof-files-basename"].as<string>()) : nullopt);

    if (options_vars.contains("stats"))
        print("{}", stats);

    return EXIT_SUCCESS;
}
