#include <gcs/constraints/regular.hh>
#include <gcs/problem.hh>
#include <gcs/solve.hh>

#include <cctype>
#include <cstdlib>
#include <fstream>
#include <iostream>
#include <map>
#include <optional>
#include <random>
#include <sstream>
#include <string>
#include <utility>
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
using std::endl;
using std::ifstream;
using std::make_optional;
using std::map;
using std::mt19937;
using std::nullopt;
using std::optional;
using std::random_device;
using std::string;
using std::stringstream;
using std::uniform_int_distribution;
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

// A nonogram (a.k.a. "paint by numbers" / "griddler"): fill in an X-by-Y grid
// of cells so that, reading each row left-to-right and each column top-to-
// bottom, the maximal runs of filled cells have exactly the lengths given by
// that line's clue. This is the canonical application of the `Regular`
// constraint: each row and column clue is a small deterministic finite
// automaton over the alphabet {empty, filled}, and the picture is the unique
// (or, for under-clued puzzles, some) assignment accepted by every automaton.
//
// The construction of the per-line automaton follows the MiniZinc Challenge
// 2013 `nonogram` model (2013/nonogram/non.mzn): a clue of run lengths
// [c_1, ..., c_k] is expanded to a "cons" string of c_1 ones, a single zero,
// c_2 ones, a single zero, ..., c_k ones (runs are `1`s, mandatory gaps are a
// single `0`), and that string drives the DFA below. Cells take value
// 0 = empty and 1 = filled, so the automaton alphabet lines up with the
// variable domains and the dense `Regular` transition table is indexed
// directly by cell value.

namespace
{
    constexpr long empty_cell = 0;
    constexpr long filled_cell = 1;

    // A single line's automaton in the dense form `Regular` accepts:
    // transitions[state][value] is the next state, or -1 for "no transition"
    // (a dead move). State 0 is the start; there is a single accepting state.
    struct LineDFA
    {
        long num_states;
        vector<vector<long>> transitions;
        vector<long> final_states;
    };

    // Expand a clue of run lengths to the 0/1 "cons" run-with-gap encoding: a
    // run of length k becomes k ones, and consecutive runs are separated by a
    // single zero. An empty clue (a blank line) yields an empty string.
    auto cons_of_clue(const vector<int> & clue) -> vector<int>
    {
        vector<int> cons;
        for (size_t i = 0; i < clue.size(); ++i) {
            if (i > 0)
                cons.push_back(0);
            for (int r = 0; r < clue[i]; ++r)
                cons.push_back(1);
        }
        return cons;
    }

    // Build the line automaton from its cons string. With n = cons.size(),
    // there are n + 1 states 0..n: state j is "j cons symbols matched", the
    // accepting state is n, and the language is
    //     0* 1^{c_1} 0+ 1^{c_2} 0+ ... 0+ 1^{c_k} 0*
    // (leading/trailing empties optional; at least one empty between runs).
    // This is the 0-indexed reading of non.mzn's `consarr`.
    auto dfa_of_cons(const vector<int> & cons) -> LineDFA
    {
        // A blank line (no runs): one state, only empties accepted.
        if (cons.empty()) {
            return LineDFA{1, {{0, -1}}, {0}};
        }

        auto n = static_cast<long>(cons.size());
        vector<vector<long>> t(n + 1, vector<long>(2, -1));
        for (long j = 0; j < n; ++j) {
            if (cons[j] == 1) {
                // Start of a run iff it is the first cons symbol or follows a
                // gap: optional leading/gap empties self-loop here.
                if (j == 0 || cons[j - 1] == 0)
                    t[j][empty_cell] = j;
                t[j][filled_cell] = j + 1; // consume a filled cell
            }
            else {
                // A mandatory single gap: take one empty to advance; a filled
                // cell here is a dead move.
                t[j][empty_cell] = j + 1;
            }
        }
        t[n][empty_cell] = n; // trailing empties self-loop in the accept state
        return LineDFA{n + 1, std::move(t), {n}};
    }

    auto dfa_of_clue(const vector<int> & clue) -> LineDFA
    {
        return dfa_of_cons(cons_of_clue(clue));
    }

    // Post `Regular` over one line of cells with the chosen proof strategy.
    // The three strategies share an OPB encoding and differ only in proof
    // shape, so a single binary can benchmark all of them (see
    // dev_docs/regular.md and dev_docs/proof_strategy.hh).
    auto post_line(Problem & p, const vector<IntegerVariableID> & cells, const LineDFA & dfa, bool legacy, bool bacchus, bool short_reasons) -> void
    {
        auto strategy = legacy ? RegularProofStrategy{proof_strategy::PerCall{}}
            : bacchus          ? RegularProofStrategy{proof_strategy::Bacchus{}}
                               : RegularProofStrategy{proof_strategy::Upfront{}};
        p.post(Regular{cells, dfa.num_states, dfa.transitions, dfa.final_states} //
                .with_short_reasons(short_reasons)
                .with_proof_strategy(strategy));
    }

    struct Puzzle
    {
        string name;
        vector<vector<int>> row_clues; // one clue (run lengths) per row, top to bottom
        vector<vector<int>> col_clues; // one clue per column, left to right
    };

    // Derive the row and column clues from a picture given as rows of '#'
    // (filled) and any other character (empty). This keeps the built-in
    // puzzles trivially consistent: the clues are, by construction, exactly
    // those of the picture drawn below.
    auto puzzle_of_picture(const string & name, const vector<string> & picture) -> Puzzle
    {
        auto height = static_cast<int>(picture.size());
        auto width = height == 0 ? 0 : static_cast<int>(picture.front().size());

        auto runs = [](auto && cell_at, int length) {
            vector<int> clue;
            int run = 0;
            for (int i = 0; i < length; ++i) {
                if (cell_at(i)) {
                    ++run;
                }
                else if (run > 0) {
                    clue.push_back(run);
                    run = 0;
                }
            }
            if (run > 0)
                clue.push_back(run);
            return clue;
        };

        Puzzle puzzle{name, {}, {}};
        for (int r = 0; r < height; ++r)
            puzzle.row_clues.push_back(runs([&](int c) { return picture[r][c] == '#'; }, width));
        for (int c = 0; c < width; ++c)
            puzzle.col_clues.push_back(runs([&](int r) { return picture[r][c] == '#'; }, height));
        return puzzle;
    }

    auto built_in_puzzles() -> map<string, vector<string>>
    {
        return {
            {"plus",
                {
                    "..#..",
                    "..#..",
                    "#####",
                    "..#..",
                    "..#..",
                }},
            {"heart",
                {
                    ".##...##.",
                    "#########",
                    "#########",
                    "#########",
                    ".#######.",
                    "..#####..",
                    "...###...",
                    "....#....",
                }},
            {"duck",
                {
                    "....###...",
                    "...#####..",
                    "...#####..",
                    "....###...",
                    "##..###...",
                    ".######...",
                    "..#####...",
                    "...####...",
                    "...###....",
                }},
        };
    }

    // Build a random solvable puzzle: draw a random size-by-size picture and
    // read off its clues. A generated instance always has at least one
    // solution (the picture itself), though not necessarily a unique one; this
    // gives a scalable Regular benchmark (see dev_docs/benchmarking.md).
    auto random_puzzle(int size, unsigned seed, double density) -> Puzzle
    {
        mt19937 rng(seed);
        uniform_int_distribution<int> coin(1, 1000);
        auto threshold = static_cast<int>(density * 1000);
        vector<string> picture;
        for (int r = 0; r < size; ++r) {
            string line;
            for (int c = 0; c < size; ++c)
                line.push_back(coin(rng) <= threshold ? '#' : '.');
            picture.push_back(line);
        }
        return puzzle_of_picture(format("random-{}-{}", size, seed), picture);
    }

    // Parse the clues out of a MiniZinc Challenge 2013 nonogram data file
    // (2013/nonogram/*.dzn). Those files already store each line as a padded
    // "cons" 0/1 string (negative entries are padding sentinels), so we read
    // the X, Y and maxlen scalars, then the row-major `rows` (Y x maxlen) and
    // `cols` (X x maxlen) integer matrices, dropping the sentinels. The
    // resulting cons strings drive `dfa_of_cons` directly.
    auto read_dzn(const string & path) -> optional<Puzzle>
    {
        ifstream in(path);
        if (! in) {
            cerr << "Could not open dzn file: " << path << endl;
            return nullopt;
        }

        stringstream buffer;
        buffer << in.rdbuf();
        auto text = buffer.str();

        // Strip MiniZinc line comments so stray '%' text can't confuse the scan.
        for (size_t i = 0; i < text.size(); ++i)
            if (text[i] == '%')
                while (i < text.size() && text[i] != '\n')
                    text[i++] = ' ';

        auto scalar = [&](const string & key) -> optional<int> {
            auto at = text.find(key);
            if (at == string::npos)
                return nullopt;
            at = text.find('=', at);
            if (at == string::npos)
                return nullopt;
            auto end = text.find(';', at);
            return std::stoi(text.substr(at + 1, end - at - 1));
        };

        // Pull every integer (including negatives) out of the assignment for a
        // named array, i.e. the text between `key` and the next ';'.
        auto integers = [&](const string & key) -> vector<int> {
            vector<int> values;
            auto at = text.find(key);
            if (at == string::npos)
                return values;
            at = text.find('=', at);
            auto end = text.find(';', at);
            auto body = text.substr(at + 1, end - at - 1);
            stringstream tokens(body);
            string token;
            auto is_int = [](const string & s) {
                if (s.empty())
                    return false;
                size_t k = (s[0] == '-' || s[0] == '+') ? 1 : 0;
                if (k == s.size())
                    return false;
                for (; k < s.size(); ++k)
                    if (! std::isdigit(static_cast<unsigned char>(s[k])))
                        return false;
                return true;
            };
            // Split on the bracketing/separator characters MiniZinc matrices use.
            for (char & c : body)
                if (c == '[' || c == ']' || c == '|' || c == ',')
                    c = ' ';
            stringstream clean(body);
            while (clean >> token)
                if (is_int(token))
                    values.push_back(std::stoi(token));
            return values;
        };

        auto x = scalar("X"), y = scalar("Y"), maxlen = scalar("maxlen");
        if (! x || ! y || ! maxlen) {
            cerr << "dzn file missing X, Y or maxlen: " << path << endl;
            return nullopt;
        }

        auto rows = integers("rows"), cols = integers("cols");
        if (static_cast<int>(rows.size()) < *y * *maxlen || static_cast<int>(cols.size()) < *x * *maxlen) {
            cerr << "dzn file has too few clue entries: " << path << endl;
            return nullopt;
        }

        // The .dzn already stores cons strings, but built-in puzzles carry run
        // lengths; keep the Puzzle uniform by recovering run lengths from each
        // cons string (a maximal run of 1s), which cons_of_clue re-expands.
        auto clues_of = [&](const vector<int> & flat, int count, int stride) {
            vector<vector<int>> clues;
            for (int i = 0; i < count; ++i) {
                vector<int> clue;
                int run = 0;
                for (int j = 0; j < stride; ++j) {
                    auto v = flat[i * stride + j];
                    if (v < 0)
                        continue; // padding sentinel
                    if (v == 1) {
                        ++run;
                    }
                    else { // a gap (0) closes the current run
                        if (run > 0)
                            clue.push_back(run);
                        run = 0;
                    }
                }
                if (run > 0)
                    clue.push_back(run);
                clues.push_back(clue);
            }
            return clues;
        };

        Puzzle puzzle{path, clues_of(rows, *y, *maxlen), clues_of(cols, *x, *maxlen)};
        return puzzle;
    }

    auto solve_puzzle(const Puzzle & puzzle, bool all_solutions, bool legacy, bool bacchus, bool short_reasons, bool print_grid,
        const optional<string> & proof_basename) -> Stats
    {
        auto height = static_cast<int>(puzzle.row_clues.size());
        auto width = static_cast<int>(puzzle.col_clues.size());

        Problem p;
        vector<vector<IntegerVariableID>> grid;
        for (int r = 0; r < height; ++r)
            grid.emplace_back(p.create_integer_variable_vector(width, Integer{empty_cell}, Integer{filled_cell}, format("cell[{}]", r)));

        for (int r = 0; r < height; ++r) {
            vector<IntegerVariableID> line(grid[r].begin(), grid[r].end());
            post_line(p, line, dfa_of_clue(puzzle.row_clues[r]), legacy, bacchus, short_reasons);
        }

        for (int c = 0; c < width; ++c) {
            vector<IntegerVariableID> line;
            for (int r = 0; r < height; ++r)
                line.push_back(grid[r][c]);
            post_line(p, line, dfa_of_clue(puzzle.col_clues[c]), legacy, bacchus, short_reasons);
        }

        return solve_with(p, SolveCallbacks{.solution = [&](const CurrentState & s) -> bool {
            if (print_grid) {
                for (int r = 0; r < height; ++r) {
                    for (int c = 0; c < width; ++c)
                        print("{}", s(grid[r][c]) == Integer{filled_cell} ? "#" : ".");
                    println("");
                }
                println("");
            }
            return all_solutions;
        }},
            proof_basename ? make_optional(ProofOptions{*proof_basename}) : nullopt);
    }
}

auto main(int argc, char * argv[]) -> int
{
    cxxopts::Options options("Nonogram Example");
    cxxopts::ParseResult options_vars;

    try {
        options.add_options("Program Options")                                                              //
            ("help", "Display help information")                                                            //
            ("prove", "Create a proof")                                                                     //
            ("proof-files-basename", "Basename for the .opb and .pbp files",                                //
                cxxopts::value<string>()->default_value("nonogram"))                                        //
            ("puzzle", "Built-in picture to solve (plus, heart, duck)",                                     //
                cxxopts::value<string>()->default_value("plus"))                                            //
            ("dzn", "Solve a MiniZinc Challenge 2013 nonogram instance instead",                            //
                cxxopts::value<string>())                                                                   //
            ("random", "Solve a random size-by-size instance instead", cxxopts::value<int>())               //
            ("seed", "Seed for --random (-1 for a random seed)", cxxopts::value<int>()->default_value("0")) //
            ("density", "Fill probability for --random", cxxopts::value<double>()->default_value("0.5"))    //
            ("all", "Enumerate all solutions instead of stopping at the first")                             //
            ("quiet", "Do not print the solution grid(s)")                                                  //
            ("stats", "Print solve statistics")                                                             //
            ("legacy", "Use the per-call Regular proof strategy (proof_strategy::PerCall)")                 //
            ("bacchus", "Use the Bacchus Regular proof strategy (proof_strategy::Bacchus)")                 //
            ("short-reasons", "Use short reasons (per-call strategy only)");

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

    auto legacy = options_vars.contains("legacy");
    auto bacchus = options_vars.contains("bacchus");
    if (legacy && bacchus) {
        cerr << "Error: --legacy and --bacchus are mutually exclusive" << endl;
        return EXIT_FAILURE;
    }

    optional<Puzzle> puzzle;
    if (options_vars.contains("dzn")) {
        puzzle = read_dzn(options_vars["dzn"].as<string>());
        if (! puzzle)
            return EXIT_FAILURE;
    }
    else if (options_vars.contains("random")) {
        auto seed = options_vars["seed"].as<int>();
        if (seed == -1)
            seed = static_cast<int>(random_device{}());
        puzzle = random_puzzle(options_vars["random"].as<int>(), static_cast<unsigned>(seed), options_vars["density"].as<double>());
    }
    else {
        auto pictures = built_in_puzzles();
        auto name = options_vars["puzzle"].as<string>();
        auto it = pictures.find(name);
        if (it == pictures.end()) {
            cerr << "Unknown puzzle '" << name << "'. Available:";
            for (const auto & [key, _] : pictures)
                cerr << " " << key;
            cerr << endl;
            return EXIT_FAILURE;
        }
        puzzle = puzzle_of_picture(name, it->second);
    }

    auto stats = solve_puzzle(*puzzle,                           //
        options_vars.contains("all"),                            //
        legacy, bacchus, options_vars.contains("short-reasons"), //
        ! options_vars.contains("quiet"),                        //
        options_vars.contains("prove")                           //
            ? make_optional(options_vars["proof-files-basename"].as<string>())
            : nullopt);

    if (options_vars.contains("stats"))
        print("{}", stats);

    return EXIT_SUCCESS;
}
