#include <gcs/constraints/global_cardinality.hh>
#include <gcs/problem.hh>
#include <gcs/solve.hh>

#include <cstdint>
#include <cstdlib>
#include <iostream>
#include <vector>

#include <cxxopts.hpp>

#include <version>

#if defined(__cpp_lib_print) && defined(__cpp_lib_format)
#include <print>
#else
#include <fmt/core.h>
#include <fmt/ostream.h>
#endif

using namespace gcs;

using std::cerr;
using std::cout;
using std::make_optional;
using std::nullopt;
using std::string;
using std::uint64_t;
using std::vector;

#if defined(__cpp_lib_print) && defined(__cpp_lib_format)
using std::print;
using std::println;
#else
using fmt::print;
using fmt::println;
#endif

namespace
{
    // A small deterministic generator (an LCG, not std::mt19937 whose
    // distributions vary between standard libraries), so an instance is
    // identified by (size, lambda, holes, seed) on every platform.
    struct Rng
    {
        uint64_t state;

        explicit Rng(uint64_t seed) : state(seed * 2654435761ull + 1)
        {
        }

        auto below(unsigned n) -> unsigned
        {
            state = state * 6364136223846793005ull + 1442695040888963407ull;
            return static_cast<unsigned>((state >> 33) % n);
        }
    };

    // A uniform-ish random latin square of order n, built row by row: each
    // row is a randomised system of distinct representatives over the values
    // still legal in each column, retrying the row (then the square) on a
    // dead end.
    auto random_latin_square(Rng & rng, unsigned n) -> vector<vector<unsigned>>
    {
        while (true) {
            vector<vector<unsigned>> square;
            vector<vector<unsigned char>> col_used(n, vector<unsigned char>(n + 1, 0));
            bool ok = true;
            for (unsigned r = 0; r < n && ok; ++r) {
                bool row_done = false;
                for (int attempt = 0; attempt < 200 && ! row_done; ++attempt) {
                    vector<unsigned> order(n);
                    for (unsigned j = 0; j < n; ++j)
                        order[j] = j;
                    for (unsigned j = n - 1; j > 0; --j)
                        std::swap(order[j], order[rng.below(j + 1)]);

                    vector<unsigned> row(n, 0);
                    vector<unsigned char> used(n + 1, 0);
                    bool good = true;
                    for (auto j : order) {
                        vector<unsigned> cands;
                        for (unsigned v = 1; v <= n; ++v)
                            if (! col_used[j][v] && ! used[v])
                                cands.push_back(v);
                        if (cands.empty()) {
                            good = false;
                            break;
                        }
                        row[j] = cands[rng.below(static_cast<unsigned>(cands.size()))];
                        used[row[j]] = 1;
                    }
                    if (good) {
                        square.push_back(row);
                        for (unsigned j = 0; j < n; ++j)
                            col_used[j][row[j]] = 1;
                        row_done = true;
                    }
                }
                if (! row_done)
                    ok = false;
            }
            if (ok)
                return square;
        }
    }
}

auto main(int argc, char * argv[]) -> int
{
    cxxopts::Options options("frequency_square");
    cxxopts::ParseResult options_vars;

    try {
        options.add_options()                                                //
            ("help", "Display help information")                             //
            ("prove", "Create a proof")                                      //
            ("proof-files-basename", "Basename for the .opb and .pbp files", //
                cxxopts::value<string>()->default_value("frequency_square")) //
            ("stats", "Print solve statistics")                              //
            ;

        options.add_options()                                                                     //
            ("size", "Order of the square", cxxopts::value<unsigned>()->default_value("12"))      //
            ("lambda", "Occurrences of each value per row and column",                            //
                cxxopts::value<unsigned>()->default_value("2"))                                   //
            ("holes", "Holes per row and column", cxxopts::value<unsigned>()->default_value("5")) //
            ("seed", "Instance seed", cxxopts::value<uint64_t>()->default_value("1"))             //
            ("consistency", "Propagation strength for the cardinality constraints (bc or gac)",   //
                cxxopts::value<string>()->default_value("gac"))                                   //
            ("all", "Find all solutions");

        options.parse_positional({"size"});
        options_vars = options.parse(argc, argv);
    }
    catch (const cxxopts::exceptions::exception & e) {
        println(cerr, "Error: {}", e.what());
        println(cerr, "Try {} --help", argv[0]);
        return EXIT_FAILURE;
    }

    if (options_vars.contains("help")) {
        println("Usage: {} [options] [size]", argv[0]);
        println("");
        println("Frequency square completion: an n x n grid over values 1..n/lambda, each");
        println("value appearing exactly lambda times in every row and column (lambda = 1 is");
        println("a latin square). A deterministic instance is generated by punching balanced");
        println("holes -- the same count per row and per column -- in a random frequency");
        println("square, so the instance is always completable but takes search to complete.");
        println("Pure global_cardinality, no other constraint, which makes this a benchmark");
        println("instrument for the cardinality propagators at both consistency levels.");
        println("");
        cout << options.help() << std::endl;
        return EXIT_SUCCESS;
    }

    auto n = options_vars["size"].as<unsigned>();
    auto lambda = options_vars["lambda"].as<unsigned>();
    auto holes = options_vars["holes"].as<unsigned>();
    auto seed = options_vars["seed"].as<uint64_t>();
    auto consistency_name = options_vars["consistency"].as<string>();

    if (lambda == 0 || n % lambda != 0) {
        println(cerr, "Error: lambda must divide size");
        return EXIT_FAILURE;
    }
    if (holes > n) {
        println(cerr, "Error: at most size holes per row and column");
        return EXIT_FAILURE;
    }
    if (consistency_name != "gac" && consistency_name != "bc") {
        println(cerr, "Error: consistency must be bc or gac");
        return EXIT_FAILURE;
    }

    auto v = n / lambda;

    // The completed square collapses a latin square's symbols into n/lambda
    // groups of lambda; a second, independent latin square supplies the
    // balanced hole pattern (its entries <= holes give exactly that many
    // holes in every row and every column).
    Rng rng(seed);
    auto full = random_latin_square(rng, n);
    auto pattern = random_latin_square(rng, n);

    Problem p;
    vector<vector<IntegerVariableID>> grid(n);
    for (unsigned r = 0; r < n; ++r)
        for (unsigned c = 0; c < n; ++c) {
            if (pattern[r][c] <= holes)
                grid[r].push_back(p.create_integer_variable(1_i, Integer{static_cast<long long>(v)}));
            else {
                auto value = Integer{static_cast<long long>((full[r][c] + lambda - 1) / lambda)};
                grid[r].push_back(p.create_integer_variable(value, value));
            }
        }

    vector<Integer> cover;
    vector<IntegerVariableID> counts;
    for (unsigned k = 1; k <= v; ++k) {
        cover.push_back(Integer{static_cast<long long>(k)});
        counts.push_back(constant_variable(Integer{static_cast<long long>(lambda)}));
    }

    auto post_gcc = [&](const vector<IntegerVariableID> & xs) {
        if (consistency_name == "gac")
            p.post(GlobalCardinality{xs, cover, counts}.with_consistency(consistency::GAC{}));
        else
            p.post(GlobalCardinality{xs, cover, counts}.with_consistency(consistency::BC{}));
    };

    for (unsigned r = 0; r < n; ++r)
        post_gcc(grid[r]);
    for (unsigned c = 0; c < n; ++c) {
        vector<IntegerVariableID> column;
        for (unsigned r = 0; r < n; ++r)
            column.push_back(grid[r][c]);
        post_gcc(column);
    }

    // When enumerating, count rather than print: this binary doubles as a
    // propagator benchmark, and printing every square would dominate it.
    auto stats = solve(
        p,
        [&](const CurrentState & s) -> bool {
            if (! options_vars.contains("all")) {
                for (unsigned r = 0; r < n; ++r) {
                    for (unsigned c = 0; c < n; ++c)
                        print("{} ", s(grid[r][c]).raw_value);
                    println("");
                }
                println("");
            }
            return options_vars.contains("all");
        },
        options_vars.contains("prove") ? make_optional<ProofOptions>(options_vars["proof-files-basename"].as<string>()) : nullopt);

    if (options_vars.contains("stats"))
        print("{}", stats);

    return EXIT_SUCCESS;
}
