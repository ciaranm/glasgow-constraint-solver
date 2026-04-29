#include <cxxopts.hpp>
#include <gcs/constraints/mult_bc.hh>
#include <gcs/problem.hh>
#include <gcs/solve.hh>
#include <iostream>
#include <random>
#include <sstream>
#include <string>

using namespace gcs;
using std::cerr;
using std::cout;
using std::endl;
using std::string;
using std::stringstream;

// Source - https://stackoverflow.com/a/9345144
// Posted by Michael Burr, modified by community. See post 'Timeline' for change history
// Retrieved 2026-03-03, License - CC BY-SA 3.0

template <class BidiIter>
BidiIter random_unique(BidiIter begin, BidiIter end, size_t num_random)
{
    size_t left = std::distance(begin, end);
    while (num_random--) {
        BidiIter r = begin;
        std::advance(r, rand() % left);
        std::swap(*begin, *r);
        ++begin;
        --left;
    }
    return begin;
}

auto main(int argc, char * argv[]) -> int
{
    cxxopts::Options options("Random Polynomial (Multiplication) Example");
    cxxopts::ParseResult options_vars;

    try {
        options.add_options("Program Options")                                          //
            ("help", "Display help information")                                        //
            ("prove", "Create a proof")                                                 //
            ("seed", "Seed for random multiplication constraint (-1 for random seed)",  //
                cxxopts::value<int>()->default_value("-1"))                             //
            ("n", "Number of variables", cxxopts::value<int>()->default_value("5"))     //
            ("d", "Max degree of each term", cxxopts::value<int>()->default_value("3")) //
            ("stats", "Print stats")                                                    //
            ("display-problem", "Display problem and solution (if any)")                //
            ("proof-prefix", "Path and name of the opb and pbp files",                  //
                cxxopts::value<string>()->default_value("random_polynomial"));          //

        options_vars = options.parse(argc, argv);
    }
    catch (const cxxopts::exceptions::exception & e) {
        cerr << "Error: " << e.what() << endl;
        cerr << "Try " << argv[0] << " --help" << endl;
        return EXIT_FAILURE;
    }

    if (options_vars.contains("help")) {
        cout << options.help() << endl;
        return EXIT_SUCCESS;
    }

    auto n = options_vars["n"].as<int>();
    auto d = options_vars["d"].as<int>();
    auto seed = options_vars["seed"].as<int>();
    auto proof_prefix = options_vars["proof-prefix"].as<string>();
    auto prove = options_vars.contains("prove");
    auto print_stats = options_vars.contains("stats");
    auto display_problem = options_vars.contains("display-problem");

    if (seed == -1) {
        std::random_device rand_dev;
        seed = rand_dev();
    }

    std::mt19937 rng(seed);
    std::uniform_int_distribution<int> lower_dist{-n, n}, add_dist{0, n}, two_to_n{2, n}, percentage{0, 100};

    Problem p{};
    auto vars = std::vector<SimpleIntegerVariableID>{};
    // Create n variables with random bounds (min -n, max n)
    for (auto i = 0; i < n; ++i) {
        auto var_lower = Integer{lower_dist(rng)};
        auto var_upper = var_lower + Integer{add_dist(rng)};
        vars.emplace_back(p.create_integer_variable(var_lower, var_upper));
    }

    auto num_terms = two_to_n(rng);
    auto sum = WeightedSum{};
    stringstream display_str;
    for (auto i = 0; i < num_terms; ++i) {
        std::vector<std::pair<SimpleIntegerVariableID, int>> indexed;
        indexed.reserve(vars.size());
        for (auto i = 0; i < (int)vars.size(); ++i) {
            indexed.emplace_back(vars[i], i);
        }

        random_unique(indexed.begin(), indexed.end(), d);

        SimpleIntegerVariableID current_prod{0};
        if (percentage(rng) < 50) {
            current_prod = p.create_integer_variable(1_i, 1_i);
            display_str << " + 1";
        }
        else {
            current_prod = p.create_integer_variable(-1_i, -1_i);
            display_str << " - 1";
        }

        auto prod_bounds = n;
        for (auto j = 0; j < d; ++j) {
            prod_bounds *= n;
            auto new_prod = p.create_integer_variable(Integer{-prod_bounds}, Integer{prod_bounds});
            p.post(MultBC{current_prod, indexed.at(j).first, new_prod});
            current_prod = new_prod;
            display_str << " * x[" << indexed.at(j).second << "]";
        }
        sum += 1_i * current_prod;
    }
    auto sum_result = p.create_integer_variable(Integer{-n * n}, Integer{n * n}, "result");
    p.post(sum == 1_i * sum_result);
    p.maximise(sum_result);
    if (display_problem) {
        cout << "Max :" << display_str.str() << endl;
    }

    auto stats = solve(
        p, [&](const CurrentState & s) -> bool {
        if (display_problem) {
            cout << "solution: ";
            for (auto i = 0; i <  n; ++i) {
                cout << "x[" << i << "] = " << s(vars.at(i)) << "; ";
            }
            cout << endl;
            cout << "sum_result = " << s(sum_result) << endl;
        }
        return true; },
        prove ? std::make_optional(ProofOptions{proof_prefix}) : std::nullopt);

    if (print_stats) {
        cout << "seed: " << seed << endl;
        cout << stats << endl;
    }
    return EXIT_SUCCESS;
}
