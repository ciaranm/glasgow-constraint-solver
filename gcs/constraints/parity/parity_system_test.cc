#include <gcs/constraints/innards/constraints_test_utils.hh>
#include <gcs/constraints/parity.hh>
#include <gcs/problem.hh>
#include <gcs/solve.hh>

#include <cstdlib>
#include <iostream>
#include <optional>
#include <random>
#include <set>
#include <tuple>
#include <utility>
#include <variant>
#include <vector>
#include <version>

#if defined(__cpp_lib_print) && defined(__cpp_lib_format)
#include <print>
#else
#include <fmt/core.h>
#include <fmt/ostream.h>
#include <fmt/ranges.h>
#endif

using std::cerr;
using std::flush;
using std::make_optional;
using std::move;
using std::mt19937;
using std::nullopt;
using std::pair;
using std::set;
using std::tuple;
using std::uniform_int_distribution;
using std::variant;
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

// Each row is a list of positions in the variable array, and asserts that an
// odd number of the variables at those positions are non-zero.
using Rows = vector<vector<int>>;

auto run_parity_system_test(bool proofs, const ViewWrapConfig & view_cfg, const vector<variant<int, pair<int, int>>> & array_range, const Rows & rows)
    -> void
{
    auto wraps = wraps_for_positions(view_cfg, static_cast<int>(array_range.size()));
    print(cerr, "parity system [{}] {} rows {} {}", view_wrap_config_label(view_cfg), array_range, rows, proofs ? " with proofs:" : ":");
    cerr << flush;

    auto is_satisfying = [&](const vector<int> & a) {
        for (const auto & row : rows) {
            int trues = 0;
            for (auto pos : row)
                if (a.at(pos) != 0)
                    ++trues;
            if (trues % 2 != 1)
                return false;
        }
        return true;
    };

    set<tuple<vector<int>>> expected, actual;
    build_expected(expected, is_satisfying, array_range);
    println(cerr, " expecting {} solutions", expected.size());

    Problem p;
    vector<IntegerVariableID> array;
    for (std::size_t i = 0; i < array_range.size(); ++i)
        array.push_back(visit([&](const auto & e) { return create_integer_variable_or_constant_with_view(p, e, wraps.at(i)); }, array_range[i]));

    vector<vector<IntegerVariableID>> posted_rows;
    for (const auto & row : rows) {
        vector<IntegerVariableID> vars;
        for (auto pos : row)
            vars.push_back(array.at(pos));
        posted_rows.push_back(move(vars));
    }
    p.post(ParitySystem{posted_rows});

    auto proof_name = proofs ? make_optional("parity_system_test_" + view_wrap_config_label(view_cfg)) : nullopt;
    solve_for_tests_checking_gac(p, proof_name, expected, actual, tuple{array});

    check_results(proof_name, expected, actual);
}

auto main(int argc, char * argv[]) -> int
{
    establish_and_announce_seed(argc, argv);

    auto view_cfg = parse_view_wrap_config_from_argv(argc, argv);

    constexpr int n_positions = 4;
    if (view_cfg.single_position && (*view_cfg.single_position < 0 || *view_cfg.single_position >= n_positions)) {
        println(cerr, "parity system view sweep: position {} out of range for n_positions = {}; skipping", *view_cfg.single_position, n_positions);
        return EXIT_SUCCESS;
    }

    using Entry = variant<int, pair<int, int>>;
    vector<pair<vector<Entry>, Rows>> data = {// No rows at all: everything is a solution.
        {{pair{0, 1}, pair{0, 1}}, {}},
        // One row is just ParityOdd, and must stay so.
        {{pair{0, 1}, pair{0, 1}, pair{0, 1}}, {{0, 1, 2}}},
        // Two rows over disjoint variables: the components do not interact.
        {{pair{0, 1}, pair{0, 1}, pair{0, 1}, pair{0, 1}}, {{0, 1}, {2, 3}}},
        // Two rows sharing one variable. Adding them gives x0 XOR x3 = 0, which
        // is the first thing the system can say that no single row can.
        {{pair{0, 1}, pair{0, 1}, pair{0, 1}, pair{0, 1}}, {{0, 1, 2}, {1, 2, 3}}},
        // Three rows summing to the empty row with an odd right-hand side:
        // unsatisfiable, but no two of them conflict.
        {{pair{0, 1}, pair{0, 1}, pair{0, 1}}, {{0, 1}, {1, 2}, {0, 2}}},
        // The same shape, satisfiable: an even number of odd rows over a cycle.
        {{pair{0, 1}, pair{0, 1}, pair{0, 1}}, {{0, 1}, {1, 2}, {0, 1, 2}}},
        // A row repeated: redundant, and must not become a contradiction.
        {{pair{0, 1}, pair{0, 1}}, {{0, 1}, {0, 1}}},
        // Wider domains: only zero / non-zero matters.
        {{pair{0, 4}, pair{-3, 3}, pair{0, 2}}, {{0, 1}, {1, 2}}},
        // Domains not containing zero, so every literal is fixed true.
        {{pair{1, 5}, pair{1, 5}, pair{0, 1}}, {{0, 1, 2}, {0, 2}}},
        // Constants mixed in, one of each parity contribution.
        {{1, pair{0, 3}, pair{0, 3}}, {{0, 1}, {1, 2}}}, {{0, pair{0, 3}, pair{0, 3}}, {{0, 1}, {0, 1, 2}}},
        // An empty row, which is the even-parity assertion and so unsatisfiable
        // on its own.
        {{pair{0, 1}, pair{0, 1}}, {{0, 1}, {}}},
        // A duplicated position within a row: duplicates XOR-cancel.
        {{pair{0, 1}, pair{0, 1}}, {{0, 0, 1}}},
        // All-constant rows, one satisfiable and one not.
        {{1, 0, 0}, {{0, 1, 2}}}, {{1, 1, 0}, {{0, 1, 2}}}};

    mt19937 rand(*get_seed());
    for (int x = 0; x < 10; ++x) {
        uniform_int_distribution n_values_dist(2, 4);
        uniform_int_distribution n_rows_dist(2, 3);
        uniform_int_distribution include(0, 1);
        auto n_values = n_values_dist(rand);

        vector<Entry> entries;
        for (int i = 0; i < n_values; ++i)
            entries.push_back(pair{0, 1});

        Rows rows;
        for (int r = 0; r < n_rows_dist(rand); ++r) {
            vector<int> row;
            for (int i = 0; i < n_values; ++i)
                if (include(rand))
                    row.push_back(i);
            rows.push_back(move(row));
        }
        data.emplace_back(move(entries), move(rows));
    }

    for (bool proofs : {false, true}) {
        if (proofs && ! can_run_veripb())
            continue;
        for (auto & [entries, rows] : data)
            run_parity_system_test(proofs, view_cfg, entries, rows);
    }

    return EXIT_SUCCESS;
}
