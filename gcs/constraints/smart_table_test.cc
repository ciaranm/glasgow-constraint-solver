#include <gcs/constraints/innards/constraints_test_utils.hh>
#include <gcs/constraints/smart_table.hh>
#include <gcs/exception.hh>
#include <gcs/problem.hh>
#include <gcs/solve.hh>

#include <cstdlib>
#include <iostream>
#include <optional>
#include <string>
#include <vector>

using std::cout;
using std::make_optional;
using std::nullopt;
using std::optional;
using std::pair;
using std::string;
using std::vector;

using namespace gcs;
using namespace gcs::test_innards;

auto check_lex(vector<Integer> & x_sols, vector<Integer> & y_sols, bool or_equal = false) -> bool
{
    if (x_sols.size() != y_sols.size()) cout << "Tuples not same length!";
    if (or_equal ? x_sols[0] >= y_sols[0] : x_sols[0] > y_sols[0]) return true;
    if (or_equal ? y_sols[0] >= x_sols[0] : y_sols[0] > x_sols[0]) return false;
    if (x_sols.size() == 1) return false;

    vector<Integer> x_sols_smaller = {x_sols.begin() + 1, x_sols.end()};
    vector<Integer> y_sols_smaller = {y_sols.begin() + 1, y_sols.end()};
    return check_lex(x_sols_smaller, y_sols_smaller);
}

auto check_at_most_1(vector<Integer> & x_sols, Integer value, bool at_least, bool in_set)
{
    auto count = 0;
    for (const auto & x_val : x_sols) {

        if (in_set) {
            (x_val == 1_i || x_val == value) && count++;
        }
        else {
            (x_val == value) && count++;
        }
    }

    return at_least ? count >= 1 : count <= 1;
}

auto run_lex_test(bool proofs, const string & mode, int length, vector<pair<int, int>> ranges, bool reverse = false, bool or_equal = false, bool fixed_y = false) -> bool
{
    auto proof_basename = "smart_table_test_" + mode;
    vector<IntegerVariableID> x;
    vector<IntegerVariableID> y;
    vector<Integer> fixed_y_vals;
    Problem p;

    for (int i = 0; i < length; i++) {
        x.emplace_back(p.create_integer_variable(Integer(ranges[i].first), Integer(ranges[i].second)));
        if (! fixed_y)
            y.emplace_back(p.create_integer_variable(Integer(ranges[i].first), Integer(ranges[i].second)));
        else
            fixed_y_vals.emplace_back(Integer{i});
    }
    SmartTuples tuples;

    for (int i = 0; i < length; ++i) {
        vector<SmartEntry> tuple;
        for (int j = 0; j < i + 1; ++j) {
            if (! fixed_y) {
                if (j < i) {
                    tuple.emplace_back(SmartTable::equals(x[j], y[j]));
                }
                else if (j == i) {
                    if (reverse) {
                        if (or_equal)
                            tuple.emplace_back(SmartTable::less_than_equal(x[j], y[j]));
                        else
                            tuple.emplace_back(SmartTable::less_than(x[j], y[j]));
                    }
                    else {
                        if (or_equal)
                            tuple.emplace_back(SmartTable::greater_than_equal(x[j], y[j]));
                        else
                            tuple.emplace_back(SmartTable::greater_than(x[j], y[j]));
                    }
                }
            }
            else {
                if (j < i) {
                    tuple.emplace_back(SmartTable::equals(x[j], fixed_y_vals[j]));
                }
                else if (j == i) {
                    if (reverse) {
                        if (or_equal)
                            tuple.emplace_back(SmartTable::less_than_equal(x[j], fixed_y_vals[j]));
                        else
                            tuple.emplace_back(SmartTable::less_than(x[j], fixed_y_vals[j]));
                    }
                    else {
                        if (or_equal)
                            tuple.emplace_back(SmartTable::greater_than_equal(x[j], fixed_y_vals[j]));
                        else
                            tuple.emplace_back(SmartTable::greater_than(x[j], fixed_y_vals[j]));
                    }
                }
            }
        }
        tuples.emplace_back(tuple);
    }

    auto all_vars = x;
    if (! fixed_y) all_vars.insert(all_vars.end(), y.begin(), y.end());

    p.post(SmartTable{all_vars, tuples});

    bool lex_violated = false;
    optional<ProofOptions> proof_options = proofs ? make_optional(ProofOptions{proof_basename}) : nullopt;
    solve_with(p,
        SolveCallbacks{
            .solution = [&](const CurrentState & s) -> bool {
                vector<Integer> x_sols;
                vector<Integer> y_sols;
                for (int i = 0; i < length; ++i) {
                    x_sols.emplace_back(s(x[i]));
                    y_sols.emplace_back(fixed_y ? fixed_y_vals[i] : s(y[i]));
                }
                lex_violated = lex_violated || (reverse ? (! check_lex(y_sols, x_sols, or_equal)) : (! check_lex(x_sols, y_sols, or_equal)));
                return true;
            }},
        proof_options);

    if (lex_violated)
        return false;
    return ! proofs || run_veripb(proof_basename + ".opb", proof_basename + ".pbp");
}

auto run_at_most_1_test(bool proofs, const string & mode, int length, vector<pair<int, int>> & ranges, bool at_least, bool in_set) -> bool
{
    auto proof_basename = "smart_table_test_" + mode;
    vector<IntegerVariableID> x;
    Problem p;

    for (int i = 0; i < length; i++) {
        x.emplace_back(p.create_integer_variable(Integer(ranges[i].first), Integer(ranges[i].second)));
    }
    auto y = p.create_integer_variable(Integer{length}, Integer{length}, "y");

    SmartTuples tuples;

    for (int i = 0; i < length; ++i) {
        vector<SmartEntry> tuple;
        for (int j = 0; j < length; ++j) {
            if (j != i) {
                if (at_least) {
                    if (in_set) {
                        tuple.emplace_back(SmartTable::in_set(x[j], {1_i, Integer{length}}));
                    }
                    else {
                        tuple.emplace_back(SmartTable::equals(x[j], y));
                    }
                }
                else {
                    if (in_set) {
                        tuple.emplace_back(SmartTable::not_in_set(x[j], {1_i, Integer{length}}));
                    }
                    else {
                        tuple.emplace_back(SmartTable::not_equals(x[j], y));
                    }
                }
            }
        }
        tuples.emplace_back(tuple);
    }

    auto all_vars = x;
    all_vars.emplace_back(y);

    p.post(SmartTable{all_vars, tuples});
    bool at_most_1_violated = false;

    optional<ProofOptions> proof_options = proofs ? make_optional(ProofOptions{proof_basename}) : nullopt;
    solve_with(p,
        SolveCallbacks{
            .solution = [&](const CurrentState & s) -> bool {
                vector<Integer> x_sols;
                for (int i = 0; i < length; ++i)
                    x_sols.emplace_back(s(x[i]));
                at_most_1_violated = at_most_1_violated || ! check_at_most_1(x_sols, Integer{length}, at_least, in_set);
                return true;
            }},
        proof_options);

    if (at_most_1_violated)
        return false;
    return ! proofs || run_veripb(proof_basename + ".opb", proof_basename + ".pbp");
}

auto main(int argc, char * argv[]) -> int
{
    if (argc != 2)
        throw UnimplementedException{};

    vector<pair<int, vector<pair<int, int>>>> data = {
        // Length    //Ranges
        {3, {{1, 3}, {1, 2}, {2, 3}}},
        {3, {{1, 2}, {1, 2}, {1, 2}}},
        {4, {{-3, 0}, {1, 4}, {3, 3}, {3, 3}}},
        {4, {{5, 5}, {2, 4}, {0, 4}, {1, 5}}},
        {5, {{-1, 4}, {3, 6}, {2, 2}, {3, 3}, {3, 5}}},
        {5, {{1, 1}, {2, 2}, {3, 3}, {4, 4}, {1, 10}}}};

    string mode{argv[1]};

    for (bool proofs : {false, true}) {
        if (proofs && ! can_run_veripb())
            continue;
        for (auto & [length, ranges] : data) {
            if (mode == "lex_gt") {
                // x > y
                if (! run_lex_test(proofs, mode, length, ranges, false, false, false))
                    return EXIT_FAILURE;
            }
            else if (mode == "lex_ge") {
                // x >= y
                if (! run_lex_test(proofs, mode, length, ranges, false, true, false))
                    return EXIT_FAILURE;
            }
            else if (mode == "lex_lt") {
                // x < y
                if (! run_lex_test(proofs, mode, length, ranges, true, false, false))
                    return EXIT_FAILURE;
            }
            else if (mode == "lex_le") {
                // x <= y
                if (! run_lex_test(proofs, mode, length, ranges, true, true, false))
                    return EXIT_FAILURE;
            }
            else if (mode == "lex_gt_fixed") {
                // x > [1,..,n]
                if (! run_lex_test(proofs, mode, length, ranges, false, false, true))
                    return EXIT_FAILURE;
            }
            else if (mode == "lex_ge_fixed") {
                // x >= [1,..,n]
                if (! run_lex_test(proofs, mode, length, ranges, false, true, true))
                    return EXIT_FAILURE;
            }
            else if (mode == "lex_lt_fixed") {
                // x < [1,..,n]
                if (! run_lex_test(proofs, mode, length, ranges, true, false, true))
                    return EXIT_FAILURE;
            }
            else if (mode == "lex_le_fixed") {
                // x <= [1,..,n]
                if (! run_lex_test(proofs, mode, length, ranges, true, true, true))
                    return EXIT_FAILURE;
            }
            else if (mode == "am1_eq") {
                // at most one var in x == length
                if (! run_at_most_1_test(proofs, mode, length, ranges, false, false))
                    return EXIT_FAILURE;
            }
            else if (mode == "am1_in_set") {
                // at most one var in x one of {1, length}
                if (! run_at_most_1_test(proofs, mode, length, ranges, false, true))
                    return EXIT_FAILURE;
            }
            else if (mode == "al1_eq") {
                // at least one var in x == length
                if (! run_at_most_1_test(proofs, mode, length, ranges, true, false))
                    return EXIT_FAILURE;
            }
            else if (mode == "al1_in_set") {
                // at least one var in x one of {1, length}
                if (! run_at_most_1_test(proofs, mode, length, ranges, true, true))
                    return EXIT_FAILURE;
            }
            else
                throw UnimplementedException{};
        }
    }

    return EXIT_SUCCESS;
}
