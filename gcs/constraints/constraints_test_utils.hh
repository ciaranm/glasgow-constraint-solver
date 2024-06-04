#ifndef GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_CONSTRAINTS_CONSTRAINTS_TEST_UTILS_HH
#define GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_CONSTRAINTS_CONSTRAINTS_TEST_UTILS_HH

#include <gcs/current_state.hh>
#include <gcs/exception.hh>
#include <gcs/problem.hh>
#include <gcs/search_heuristics.hh>
#include <gcs/solve.hh>

#include <gcs/innards/variable_id_utils.hh>

#include <util/enumerate.hh>

#include <fmt/core.h>
#include <fmt/ostream.h>
#include <fmt/ranges.h>

#include <cstdlib>
#include <functional>
#include <iostream>
#include <optional>
#include <string>
#include <tuple>
#include <utility>
#include <vector>

namespace gcs::test_innards
{
    template <typename... Args_>
    [[nodiscard]] auto run_veripb(Args_... args) -> bool
    {
        auto cmd = fmt::format("veripb {}", fmt::join(std::vector<std::string>{args...}, " "));
        fmt::println(std::cerr, "$ {}", cmd);
        return EXIT_SUCCESS == system(cmd.c_str());
    }

    [[nodiscard]] inline auto can_run_veripb() -> bool
    {
        return run_veripb("--help", ">/dev/null");
    }

    template <typename ResultsSet_, typename IsSatisfying_, typename... Accumulated_>
    auto generate_expected(ResultsSet_ & expected, IsSatisfying_ is_satisfying, const std::tuple<Accumulated_...> & acc) -> void
    {
        if (std::apply(is_satisfying, acc))
            std::apply([&](auto &... args) { expected.emplace(args...); }, acc);
    }

    template <typename ResultsSet_, typename IsSatisfying_, typename... Accumulated_, typename... RestOfArgs_>
    auto generate_expected(ResultsSet_ & expected, IsSatisfying_ is_satisfying, const std::tuple<Accumulated_...> & acc,
        const std::vector<std::pair<int, int>> & range_arg_vec, RestOfArgs_... rest_of_args) -> void;

    template <typename ResultsSet_, typename IsSatisfying_, typename... Accumulated_, typename... RestOfArgs_>
    auto generate_expected(ResultsSet_ & expected, IsSatisfying_ is_satisfying, const std::tuple<Accumulated_...> & acc,
        std::pair<int, int> range_arg, RestOfArgs_... rest_of_args) -> void
    {
        for (int n = range_arg.first; n <= range_arg.second; ++n)
            generate_expected(expected, is_satisfying, std::tuple_cat(acc, std::tuple{n}), rest_of_args...);
    }

    template <typename ResultsSet_, typename IsSatisfying_, typename... Accumulated_, typename... RestOfArgs_>
    auto generate_expected(ResultsSet_ & expected, IsSatisfying_ is_satisfying, const std::tuple<Accumulated_...> & acc,
        const std::vector<std::pair<int, int>> & range_arg_vec, RestOfArgs_... rest_of_args) -> void
    {
        std::function<auto(std::size_t, std::vector<int>)->void> build = [&](std::size_t pos, std::vector<int> sol) -> void {
            if (pos == range_arg_vec.size()) {
                generate_expected(expected, is_satisfying, std::tuple_cat(acc, std::tuple{sol}), rest_of_args...);
            }
            else {
                for (int n = range_arg_vec.at(pos).first; n <= range_arg_vec.at(pos).second; ++n) {
                    sol.push_back(n);
                    build(pos + 1, sol);
                    sol.pop_back();
                }
            }
        };
        std::vector<int> sol;
        build(0, sol);
    }

    template <typename ResultsSet_, typename IsSatisfying_, typename... Args_>
    auto build_expected(ResultsSet_ & expected, IsSatisfying_ is_satisfying, Args_... args) -> void
    {
        generate_expected(expected, is_satisfying, {}, std::forward<Args_>(args)...);
    }

    template <typename ResultsSet_>
    auto check_results(const std::optional<std::string> & proof_name, const ResultsSet_ & expected, const ResultsSet_ & actual) -> void
    {
        using fmt::println;
        using std::cerr;

        if (expected != actual) {
            println(cerr, "test did not produce expected results");
            println(cerr, "expected: {}", expected);
            println(cerr, "actual:   {}", actual);
            for (auto & item : actual)
                if (! expected.contains(item))
                    println(cerr, "extra:    {}", item);
            for (auto & item : expected)
                if (! actual.contains(item))
                    println(cerr, "missing:  {}", item);

            throw UnexpectedException{"Test did not produce expected results"};
        }

        if (proof_name)
            if (! run_veripb(*proof_name + ".opb", *proof_name + ".pbp"))
                throw UnexpectedException{"veripb verification failed"};
    }

    template <typename SolutionCallback_, typename TraceCallback_>
    auto solve_for_tests_with_callbacks(Problem & p, const std::optional<std::string> & proof_name, const SolutionCallback_ & f, const TraceCallback_ & t) -> void
    {
        solve_with(p,
            SolveCallbacks{.solution = f, .trace = t, .branch = branch_randomly(p), .guess = guess_randomly()},
            proof_name ? make_optional<ProofOptions>(*proof_name + ".opb", *proof_name + ".pbp") : std::nullopt);
    }

    auto extract_from_state(const CurrentState & s, IntegerVariableID v) -> int
    {
        return s(v).raw_value;
    }

    template <typename T_>
    auto extract_from_state(const CurrentState & s, const std::vector<T_> & v)
    {
        using ItemType = decltype(extract_from_state(s, *v.begin()));
        std::vector<ItemType> result;
        for (auto & i : v)
            result.push_back(extract_from_state(s, i));
        return result;
    }

    template <typename ResultsSet_, typename... Args_>
    auto solve_for_tests(Problem & p, const std::optional<std::string> & proof_name, ResultsSet_ & actual, const std::tuple<Args_...> & vars) -> void
    {
        solve_for_tests_with_callbacks(
            p, proof_name,
            [&](const CurrentState & s) -> bool {
                std::apply([&](const auto &... args) {
                    actual.emplace(extract_from_state(s, args)...);
                },
                    vars);
                return true;
            },
            [&](const CurrentState &) -> bool {
                return true;
            });
    }

    enum class CheckConsistency
    {
        None,
        BC,
        GAC
    };

    template <typename ResultsSet_>
    auto consistency_not_achieved(const std::string & which, const ResultsSet_ & expected, const CurrentState & s,
        const std::vector<IntegerVariableID> & all_vars, const IntegerVariableID & var, Integer val) -> void
    {
        using fmt::println;
        using std::cerr;
        println(cerr, "{} not achieved in test", which);
        println(cerr, "expected: {}", expected);
        println(cerr, "var {} value {} does not occur anywhere in expected", innards::debug_string(var), val);
        for (const auto & v : all_vars) {
            std::vector<Integer> values;
            for (Integer i : s.each_value(v))
                values.push_back(i);
            println(cerr, "var {} has values {}", innards::debug_string(v), values);
        }
        throw UnexpectedException{"consistency not achieved"};
    }

    template <typename ResultsSet_, typename Get_>
    auto check_support(const ResultsSet_ & expected, const CurrentState & s,
        const std::vector<IntegerVariableID> & all_vars, const IntegerVariableID & var, CheckConsistency consistency, const Get_ & get_from_expected) -> void
    {
        switch (consistency) {
        case CheckConsistency::None:
            return;

        case CheckConsistency::GAC:
            for (auto val : s.each_value(var)) {
                bool found_support = false;
                for (auto & x : expected)
                    if (get_from_expected(x) == val.raw_value) {
                        found_support = true;
                        break;
                    }
                if (! found_support)
                    consistency_not_achieved("gac", expected, s, all_vars, var, val);
            }
            return;

        case CheckConsistency::BC:
            for (const auto & val : std::vector{s.lower_bound(var), s.upper_bound(var)}) {
                bool found_support = false;
                for (auto & x : expected)
                    if (get_from_expected(x) == val.raw_value) {
                        found_support = true;
                        break;
                    }
                if (! found_support)
                    consistency_not_achieved("bc", expected, s, all_vars, var, val);
            }
            return;
        }

        throw NonExhaustiveSwitch{};
    }

    template <typename ResultsSet_, typename Get_>
    auto check_support(const ResultsSet_ & expected, const CurrentState & s,
        const std::vector<IntegerVariableID> & all_vars, const std::vector<IntegerVariableID> & vars, CheckConsistency consistency, const Get_ & get_from_expected) -> void
    {
        switch (consistency) {
        case CheckConsistency::None:
            return;

        case CheckConsistency::BC:
            for (const auto & [the_idx, the_var] : enumerate(vars)) {
                const auto & idx = the_idx;
                const auto & var = the_var;
                for (const auto & val : std::vector{s.lower_bound(var), s.upper_bound(var)}) {
                    bool found_support = false;
                    for (auto & x : expected)
                        if (get_from_expected(x).at(idx) == val.raw_value) {
                            found_support = true;
                            break;
                        }
                    if (! found_support)
                        consistency_not_achieved("gac", expected, s, all_vars, var, val);
                }
            }
            return;

        case CheckConsistency::GAC:
            for (const auto & [the_idx, the_var] : enumerate(vars)) {
                const auto & idx = the_idx;
                const auto & var = the_var;
                for (auto val : s.each_value(var)) {
                    bool found_support = false;
                    for (auto & x : expected)
                        if (get_from_expected(x).at(idx) == val.raw_value) {
                            found_support = true;
                            break;
                        }
                    if (! found_support)
                        consistency_not_achieved("gac", expected, s, all_vars, var, val);
                }
            }
            return;
        }

        throw NonExhaustiveSwitch{};
    }

    inline auto add_to_all_vars(std::vector<IntegerVariableID> & all_vars, IntegerVariableID v) -> void
    {
        all_vars.push_back(v);
    }

    inline auto add_to_all_vars(std::vector<IntegerVariableID> & all_vars, const std::vector<IntegerVariableID> & v) -> void
    {
        all_vars.insert(all_vars.end(), v.begin(), v.end());
    }

    template <typename ResultsSet_, typename... AllArgs_>
    auto solve_for_tests_checking_consistency(Problem & p, const std::optional<std::string> & proof_name, const ResultsSet_ & expected,
        ResultsSet_ & actual, const std::tuple<std::pair<AllArgs_, CheckConsistency>...> & all_vars) -> void
    {
        std::vector<IntegerVariableID> all_vars_as_vector;
        [&]<std::size_t... i_>(std::index_sequence<i_...>) {
            (add_to_all_vars(all_vars_as_vector, get<i_>(all_vars).first), ...);
        }(std::index_sequence_for<AllArgs_...>());
        solve_for_tests_with_callbacks(
            p, proof_name,
            [&](const CurrentState & s) -> bool {
                std::apply([&](const auto &... args) {
                    actual.emplace(extract_from_state(s, args.first)...);
                },
                    all_vars);
                return true;
            },
            [&](const CurrentState & s) -> bool {
                [&]<std::size_t... i_>(std::index_sequence<i_...>) {
                    (check_support(expected, s, all_vars_as_vector, get<i_>(all_vars).first, get<i_>(all_vars).second, [&](const auto & x) { return get<i_>(x); }), ...);
                }(std::index_sequence_for<AllArgs_...>());
                return true;
            });
    }

    template <typename ResultsSet_, typename... AllArgs_>
    auto solve_for_tests_checking_gac(Problem & p, const std::optional<std::string> & proof_name, const ResultsSet_ & expected,
        ResultsSet_ & actual, const std::tuple<AllArgs_...> & all_vars) -> void
    {
        auto all_vars_are_gac = [&]<std::size_t... i_>(std::index_sequence<i_...>) {
            return std::make_tuple(std::make_pair(get<i_>(all_vars), CheckConsistency::GAC)...);
        }(std::index_sequence_for<AllArgs_...>());
        solve_for_tests_checking_consistency(p, proof_name, expected, actual, all_vars_are_gac);
    }

    struct RandomBounds
    {
        int lower_min, lower_max, add_min, add_max;
    };

    auto random_bounds(int lower_min, int lower_max, int add_min, int add_max) -> RandomBounds
    {
        return RandomBounds{lower_min, lower_max, add_min, add_max};
    }

    template <typename Random_, typename Item_>
    auto generate_random_data_item(Random_ & rand, std::vector<Item_> vec);

    template <typename Random_>
    auto generate_random_data_item(Random_ &, int value) -> int
    {
        return value;
    }

    template <typename Random_, typename Int_>
    auto generate_random_data_item(Random_ & rand, std::uniform_int_distribution<Int_> dist)
    {
        return dist(rand);
    }

    template <typename Random_>
    auto generate_random_data_item(Random_ & rand, const RandomBounds & bounds)
    {
        std::uniform_int_distribution<int> lower_dist{bounds.lower_min, bounds.lower_max}, add_dist{bounds.add_min, bounds.add_max};
        auto lower = lower_dist(rand);
        auto upper = lower + add_dist(rand);
        return std::pair{lower, upper};
    }

    template <typename Random_, typename Item1_, typename Item2_>
    auto generate_random_data_item(Random_ & rand, std::pair<Item1_, Item2_> values)
    {
        return std::pair{generate_random_data_item(rand, values.first), generate_random_data_item(rand, values.second)};
    }

    template <typename Random_, typename Item_>
    auto generate_random_data_item(Random_ & rand, std::vector<Item_> vec)
    {
        using ItemType = decltype(generate_random_data_item(rand, *vec.begin()));
        std::vector<ItemType> result;
        for (unsigned n = 0; n < vec.size(); ++n)
            result.emplace_back(generate_random_data_item(rand, vec.at(n)));
        return result;
    }

    template <typename Random_, typename ResultsSet_, typename... Args_>
    auto generate_random_data(Random_ & rand, ResultsSet_ & data, Args_... args) -> void
    {
        data.emplace_back(generate_random_data_item(rand, std::forward<Args_>(args))...);
    }
}

#endif
