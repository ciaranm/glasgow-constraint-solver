#ifndef GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_CONSTRAINTS_INNARDS_CONSTRAINTS_TEST_UTILS_HH
#define GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_CONSTRAINTS_INNARDS_CONSTRAINTS_TEST_UTILS_HH

#include <gcs/current_state.hh>
#include <gcs/exception.hh>
#include <gcs/problem.hh>
#include <gcs/search_heuristics.hh>
#include <gcs/solve.hh>

#include <gcs/innards/variable_id_utils.hh>

#include <util/enumerate.hh>
#include <util/overloaded.hh>

#include <algorithm>
#include <array>
#include <cstdio>
#include <cstdlib>
#include <functional>
#include <iostream>
#include <optional>
#include <random>
#include <string>
#include <tuple>
#include <unordered_set>
#include <utility>
#include <vector>
#include <version>

#if defined(__cpp_lib_print) && defined(__cpp_lib_format)
#include <print>
#include <variant>

template <typename... Ts_>
struct std::formatter<std::variant<Ts_...>> : std::formatter<std::string>
{
    template <typename FormatContext_>
    auto format(const std::variant<Ts_...> & v, FormatContext_ & ctx) const
    {
        return std::visit([&](const auto & val) { return std::formatter<std::string>::format(std::format("{}", val), ctx); }, v);
    }
};
#else
#include <fmt/core.h>
#include <fmt/ostream.h>
#include <fmt/ranges.h>
#include <fmt/std.h>
#endif

namespace gcs::test_innards
{
    template <typename... Args_>
    [[nodiscard]] auto run_veripb(Args_... args) -> bool
    {
        std::string cmd{"veripb"};
        for (auto & a : std::vector<std::string>{args...})
            (cmd += ' ') += a;
#if defined(__cpp_lib_print) && defined(__cpp_lib_format)
        using std::println;
#else
        using fmt::println;
#endif
        println(std::cerr, "$ {}", cmd);
        return EXIT_SUCCESS == system(cmd.c_str());
    }

    [[nodiscard]] inline auto can_run_veripb() -> bool
    {
        return run_veripb("--help", ">/dev/null");
    }

    /**
     * Verify a test's proof with VeriPB, then, on success, delete its .opb/.pbp
     * files.
     *
     * Every proving test instance writes its proof into the working directory,
     * and VeriPB .pbp files for enumeration tests routinely reach hundreds of
     * megabytes. Left in place they accumulate over a run: a full parallel
     * `ctest` otherwise holds gigabytes of proofs at once, which can exhaust the
     * disk mid-run and make an *unrelated* lane's proof write fail (an uncaught
     * std::ios_failure that terminates that test). Deleting each proof as soon as
     * it verifies bounds the footprint to the lanes running concurrently.
     *
     * The files are kept when verification fails, so a failing proof is still on
     * disk to inspect. std::remove of an already-absent file is a harmless no-op.
     */
    inline auto verify_proof_and_clean_up(const std::string & proof_name) -> void
    {
        if (! run_veripb(proof_name + ".opb", proof_name + ".pbp"))
            throw UnexpectedException{"veripb verification failed"};
        std::remove((proof_name + ".opb").c_str());
        std::remove((proof_name + ".pbp").c_str());
    }

    /**
     * \name Runtime caps for pathological random test cases
     *
     * Some data-driven constraint tests occasionally generate an instance with
     * a very large number of solutions or a very large search tree. Because the
     * proof is logged and verified by VeriPB, these cases produce huge proofs
     * and dominate the (parallel) test suite runtime.
     *
     * Two optional caps bound this, read from the environment so they can be
     * applied suite-wide without editing each test:
     *  - \c GCS_TEST_MAX_SOLUTIONS : stop a solve once this many solutions have
     *    been collected;
     *  - \c GCS_TEST_MAX_RECURSIONS : stop a solve once this many internal
     *    search nodes (trace callbacks) have been visited.
     *
     * When a cap fires the solve stops early. The solver then emits a partial
     * but still VeriPB-checkable proof (conclusion SAT or NONE — the same path
     * used by check_initialisation_only_for_tests), and check_results() weakens
     * its comparison to a soundness-only subset check (see last_run_truncated).
     *
     * An unset or empty variable means "no cap"; the default behaviour with
     * neither variable set is exactly the historical full-enumeration check.
     * @{
     */
    inline auto env_cap(const char * name) -> std::optional<unsigned long long>
    {
        if (auto v = std::getenv(name); v && *v)
            return std::strtoull(v, nullptr, 10);
        return std::nullopt;
    }

    /// Whether the most recent solve_for_tests*() call stopped early because a
    /// cap fired. Set by solve_for_tests_with_callbacks(), read by
    /// check_results(); single-threaded, one solve per check by construction.
    inline auto last_run_truncated() -> bool &
    {
        static bool truncated = false;
        return truncated;
    }
    /// @}

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
        const std::vector<std::vector<std::pair<int, int>>> & range_arg_vec, RestOfArgs_... rest_of_args) -> void;

    template <typename ResultsSet_, typename IsSatisfying_, typename... Accumulated_, typename... RestOfArgs_>
    auto generate_expected(ResultsSet_ & expected, IsSatisfying_ is_satisfying, const std::tuple<Accumulated_...> & acc,
        std::pair<int, int> range_arg, RestOfArgs_... rest_of_args) -> void;

    template <typename ResultsSet_, typename IsSatisfying_, typename... Accumulated_, typename... RestOfArgs_>
    auto generate_expected(ResultsSet_ & expected, IsSatisfying_ is_satisfying, const std::tuple<Accumulated_...> & acc, std::vector<int> vec_arg,
        RestOfArgs_... rest_of_args) -> void;

    template <typename ResultsSet_, typename IsSatisfying_, typename... Accumulated_, typename... RestOfArgs_>
    auto generate_expected(ResultsSet_ & expected, IsSatisfying_ is_satisfying, const std::tuple<Accumulated_...> & acc,
        std::variant<int, std::pair<int, int>> range_or_const_arg, RestOfArgs_... rest_of_args) -> void;

    template <typename ResultsSet_, typename IsSatisfying_, typename... Accumulated_, typename... RestOfArgs_>
    auto generate_expected(ResultsSet_ & expected, IsSatisfying_ is_satisfying, const std::tuple<Accumulated_...> & acc,
        const std::vector<std::variant<int, std::pair<int, int>>> & range_arg_vec, RestOfArgs_... rest_of_args) -> void;

    template <typename ResultsSet_, typename IsSatisfying_, typename... Accumulated_, typename... RestOfArgs_>
    auto generate_expected(ResultsSet_ & expected, IsSatisfying_ is_satisfying, const std::tuple<Accumulated_...> & acc,
        std::pair<int, int> range_arg, RestOfArgs_... rest_of_args) -> void
    {
        for (int n = range_arg.first; n <= range_arg.second; ++n)
            generate_expected(expected, is_satisfying, std::tuple_cat(acc, std::tuple{n}), rest_of_args...);
    }

    template <typename ResultsSet_, typename IsSatisfying_, typename... Accumulated_, typename... RestOfArgs_>
    auto generate_expected(ResultsSet_ & expected, IsSatisfying_ is_satisfying, const std::tuple<Accumulated_...> & acc, std::vector<int> vec_arg,
        RestOfArgs_... rest_of_args) -> void
    {
        for (int n : vec_arg)
            generate_expected(expected, is_satisfying, std::tuple_cat(acc, std::tuple{n}), rest_of_args...);
    }

    template <typename ResultsSet_, typename IsSatisfying_, typename... Accumulated_, typename... RestOfArgs_>
    auto generate_expected(ResultsSet_ & expected, IsSatisfying_ is_satisfying, const std::tuple<Accumulated_...> & acc, int const_arg,
        RestOfArgs_... rest_of_args) -> void
    {
        generate_expected(expected, is_satisfying, std::tuple_cat(acc, std::tuple{const_arg}), rest_of_args...);
    }

    template <typename ResultsSet_, typename IsSatisfying_, typename... Accumulated_, typename... RestOfArgs_>
    auto generate_expected(ResultsSet_ & expected, IsSatisfying_ is_satisfying, const std::tuple<Accumulated_...> & acc,
        std::variant<int, std::pair<int, int>> range_or_const_arg, RestOfArgs_... rest_of_args) -> void
    {
        std::visit([&](auto arg) { generate_expected(expected, is_satisfying, acc, arg, rest_of_args...); }, range_or_const_arg);
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

    template <typename ResultsSet_, typename IsSatisfying_, typename... Accumulated_, typename... RestOfArgs_>
    auto generate_expected(ResultsSet_ & expected, IsSatisfying_ is_satisfying, const std::tuple<Accumulated_...> & acc,
        const std::vector<std::vector<std::pair<int, int>>> & range_arg_vec, RestOfArgs_... rest_of_args) -> void
    {
        std::function<auto(std::size_t, std::size_t, std::vector<std::vector<int>>)->void> build = [&](std::size_t pos1, std::size_t pos2,
                                                                                                       std::vector<std::vector<int>> sol) -> void {
            if (pos1 == range_arg_vec.size()) {
                sol.pop_back();
                generate_expected(expected, is_satisfying, std::tuple_cat(acc, std::tuple{sol}), rest_of_args...);
                sol.emplace_back();
            }
            else if (pos2 == range_arg_vec.at(pos1).size()) {
                sol.emplace_back();
                build(pos1 + 1, 0, sol);
                sol.pop_back();
            }
            else {
                for (int n = range_arg_vec.at(pos1).at(pos2).first; n <= range_arg_vec.at(pos1).at(pos2).second; ++n) {
                    sol.at(pos1).push_back(n);
                    build(pos1, pos2 + 1, sol);
                    sol.at(pos1).pop_back();
                }
            }
        };
        std::vector<std::vector<int>> sol;
        sol.emplace_back();
        build(0, 0, sol);
    }

    template <typename ResultsSet_, typename IsSatisfying_, typename... Accumulated_, typename... RestOfArgs_>
    auto generate_expected(ResultsSet_ & expected, IsSatisfying_ is_satisfying, const std::tuple<Accumulated_...> & acc,
        const std::vector<std::variant<int, std::pair<int, int>>> & range_arg_vec, RestOfArgs_... rest_of_args) -> void
    {
        std::function<auto(std::size_t, std::vector<int>)->void> build = [&](std::size_t pos, std::vector<int> sol) -> void {
            if (pos == range_arg_vec.size()) {
                generate_expected(expected, is_satisfying, std::tuple_cat(acc, std::tuple{sol}), rest_of_args...);
            }
            else {
                overloaded{
                    [&](int n) {
                        sol.push_back(n);
                        build(pos + 1, sol);
                        sol.pop_back();
                    }, //
                    [&](std::pair<int, int> p) {
                        for (int n = p.first; n <= p.second; ++n) {
                            sol.push_back(n);
                            build(pos + 1, sol);
                            sol.pop_back();
                        }
                    } //
                }
                    .visit(range_arg_vec.at(pos));
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
#if defined(__cpp_lib_print) && defined(__cpp_lib_format)
        using std::println;
#else
        using fmt::println;
#endif
        using std::cerr;

        if (last_run_truncated()) {
            // The solve was stopped early by a runtime cap, so `actual` holds
            // only a subset of the solutions. Completeness is no longer
            // checkable; verify soundness instead — every solution the solver
            // produced must be genuinely satisfying (present in `expected`,
            // which is built independently by the test's own oracle). The
            // partial proof is still verified by VeriPB below.
            for (const auto & item : actual)
                if (! expected.contains(item)) {
                    println(cerr, "truncated test run produced a spurious solution");
                    println(cerr, "spurious: {}", item);
                    throw UnexpectedException{"Truncated test run produced a solution not in expected"};
                }
            println(cerr, "[truncated run: {} of <= {} solutions checked sound]", actual.size(), expected.size());
            if (proof_name)
                verify_proof_and_clean_up(*proof_name);
            return;
        }

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
            verify_proof_and_clean_up(*proof_name);
    }

    /**
     * Singleton holding the --seed argv value, if one was passed.
     *
     * Test main()s call set_seed_from_argv(argc, argv) once at startup; the
     * seed then drives both the test's data RNG (callers read it via
     * get_seed()) and the harness's branching heuristic
     * (random_branch_with_optional_seed below). When unset, behaviour is
     * the historical random_device-based randomness.
     */
    inline auto seed_storage() -> std::optional<std::uint_fast32_t> &
    {
        static std::optional<std::uint_fast32_t> seed;
        return seed;
    }

    inline auto get_seed() -> std::optional<std::uint_fast32_t>
    {
        return seed_storage();
    }

    /**
     * Scan argv for `--seed=N`, storing the value if present.
     *
     * Unknown args are ignored so this composes with existing per-test argv
     * (the mode selector of comparison_test / linear_test, the --view-wrap
     * flags, etc.).
     */
    inline auto set_seed_from_argv(int argc, char * argv[]) -> void
    {
        const std::string prefix = "--seed=";
        for (int i = 1; i < argc; ++i) {
            std::string arg = argv[i];
            if (arg.starts_with(prefix)) {
                seed_storage() = static_cast<std::uint_fast32_t>(std::stoul(arg.substr(prefix.size())));
                return;
            }
        }
        seed_storage() = std::nullopt;
    }

    /// Build the random branching pair, honouring --seed if set. Uses
    /// reject_random_interval so every constraint test exercises (and VeriPB-checks)
    /// interval/range branching, including backtrack clauses over interval-reject
    /// decisions. This relies on the laminar containment edges maintained by
    /// need_invar so an interval reject propagates to the (eq/range) atoms a
    /// constraint's conflict depends on.
    inline auto random_branch_with_optional_seed(const Problem & p)
    {
        if (auto seed = get_seed())
            return branch_with(variable_order::random(p, *seed), value_order::reject_random_interval(*seed + 1));
        return branch_with(variable_order::random(p), value_order::reject_random_interval());
    }

    template <typename SolutionCallback_, typename TraceCallback_>
    auto solve_for_tests_with_callbacks(
        Problem & p, const std::optional<std::string> & proof_name, const SolutionCallback_ & f, const TraceCallback_ & t) -> void
    {
        // Every constraint test runs with the idempotence claim checker on:
        // each honoured PropagatorState::EnableButIdempotent claim is verified
        // by an immediate re-run, which aborts the solve if it infers anything.
        // Deterministic, at most doubles the cost of claiming runs, and a
        // passing re-run emits nothing, so the proof lanes are unaffected.
        // MSVC has no POSIX setenv; _putenv_s always overwrites, so mirror the
        // don't-overwrite (overwrite == 0) semantics with a getenv check.
#ifdef _WIN32
        if (! std::getenv("GCS_CHECK_IDEMPOTENT_CLAIMS"))
            _putenv_s("GCS_CHECK_IDEMPOTENT_CLAIMS", "1");
#else
        setenv("GCS_CHECK_IDEMPOTENT_CLAIMS", "1", 0);
#endif

        // Apply the optional runtime caps (see env_cap). The wrappers count
        // solutions / internal search nodes and return false to stop the solve
        // once a cap is reached; `f` and `t` and these counters all outlive the
        // synchronous solve_with() call below, so capture by reference is safe.
        const auto max_solutions = env_cap("GCS_TEST_MAX_SOLUTIONS");
        const auto max_recursions = env_cap("GCS_TEST_MAX_RECURSIONS");
        last_run_truncated() = false;
        unsigned long long solution_count = 0, node_count = 0;

        auto capped_solution = [&](const CurrentState & s) -> bool {
            if (max_solutions && solution_count >= *max_solutions) {
                last_run_truncated() = true;
                return false;
            }
            ++solution_count;
            return f(s);
        };
        auto capped_trace = [&](const CurrentState & s) -> bool {
            if (max_recursions && node_count >= *max_recursions) {
                last_run_truncated() = true;
                return false;
            }
            ++node_count;
            return t(s);
        };

        solve_with(p,
            SolveCallbacks{
                .solution = capped_solution,                  //
                .trace = capped_trace,                        //
                .branch = random_branch_with_optional_seed(p) //
            },
            proof_name ? std::make_optional<ProofOptions>(ProofFileNames{*proof_name}) : std::nullopt);
    }

    /**
     * Solve only as far as the first complete propagation, then bail out via
     * a trace callback returning false. VeriPB checks any RUP / pol steps the
     * initialisers emitted and accepts the resulting "conclusion NONE" proof,
     * without making us pay for full enumeration. Useful for testing the
     * proofs emitted by initialisers in isolation.
     */
    auto check_initialisation_only_for_tests(Problem & p, const std::string & proof_name) -> void
    {
        solve_with(p, SolveCallbacks{.trace = [](const CurrentState &) -> bool { return false; }, .branch = random_branch_with_optional_seed(p)},
            std::make_optional<ProofOptions>(ProofFileNames{proof_name}));

        verify_proof_and_clean_up(proof_name);
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
                std::apply([&](const auto &... args) { actual.emplace(extract_from_state(s, args)...); }, vars);
                return true;
            },
            [&](const CurrentState &) -> bool { return true; });
    }

    enum class CheckConsistency
    {
        None,
        BC,
        GAC
    };

    inline auto consistency_not_achieved(const std::string & which, const std::unordered_set<long long> & locally_supported, const CurrentState & s,
        const std::vector<IntegerVariableID> & all_vars, const IntegerVariableID & var, Integer val) -> void
    {
#if defined(__cpp_lib_print) && defined(__cpp_lib_format)
        using std::println;
#else
        using fmt::println;
#endif
        using std::cerr;
        std::vector<long long> supported{locally_supported.begin(), locally_supported.end()};
        std::ranges::sort(supported);
        println(cerr, "{} not achieved in test", which);
        println(cerr, "var {} value {} has no support at the current node", innards::debug_string(var), val);
        println(cerr, "values of {} that do have a support here: {}", innards::debug_string(var), supported);
        for (const auto & v : all_vars) {
            std::vector<Integer> values;
            for (Integer i : s.each_value(v))
                values.push_back(i);
            println(cerr, "var {} has values {}", innards::debug_string(v), values);
        }
        throw UnexpectedException{"consistency not achieved"};
    }

    /**
     * Is `val` consistent with `var`'s current state for the purposes of being
     * part of a support at the given consistency level? GAC requires the value
     * to be present in the live domain; BC (which the solver implements as
     * bounds(Z)) only requires it to lie within the current [lower, upper]
     * interval, so a support may legitimately pass through a hole that branching
     * punched into a partner's domain. Using the right filter per level keeps a
     * correctly-bounds(Z) partner from triggering a spurious failure when a BC
     * variable's bound is being checked.
     */
    inline auto component_supports(const CurrentState & s, const IntegerVariableID & var, int val, CheckConsistency level) -> bool
    {
        switch (level) {
            using enum CheckConsistency;
        case None: return true;
        case GAC: return s.in_domain(var, Integer{val});
        case BC: return s.lower_bound(var) <= Integer{val} && Integer{val} <= s.upper_bound(var);
        }
        throw NonExhaustiveSwitch{};
    }

    inline auto component_supports(
        const CurrentState & s, const std::vector<IntegerVariableID> & vars, const std::vector<int> & vals, CheckConsistency level) -> bool
    {
        for (const auto & [idx, var] : enumerate(vars))
            if (! component_supports(s, var, vals.at(idx), level))
                return false;
        return true;
    }

    /// How many supported-value-set slots a position contributes: one for a
    /// scalar variable, one per element for a vector position.
    inline auto support_slot_count(const IntegerVariableID &) -> std::size_t
    {
        return 1;
    }

    inline auto support_slot_count(const std::vector<IntegerVariableID> & vars) -> std::size_t
    {
        return vars.size();
    }

    /// Record an alive tuple's component value(s) into a position's slots.
    inline auto record_support(std::vector<std::unordered_set<long long>> & slots, int val) -> void
    {
        slots.at(0).insert(val);
    }

    inline auto record_support(std::vector<std::unordered_set<long long>> & slots, const std::vector<int> & vals) -> void
    {
        for (const auto & [idx, val] : enumerate(vals))
            slots.at(idx).insert(val);
    }

    /**
     * Check one position against the per-node supported-value sets the caller
     * built (one pass over `expected`, filtered to tuples alive at this node).
     * GAC checks every live domain value; BC checks the two bounds.
     */
    inline auto check_support(const std::vector<std::unordered_set<long long>> & slots, const CurrentState & s,
        const std::vector<IntegerVariableID> & all_vars, const IntegerVariableID & var, CheckConsistency consistency) -> void
    {
        switch (consistency) {
            using enum CheckConsistency;
        case None: return;
        case GAC:
            for (auto val : s.each_value(var))
                if (! slots.at(0).contains(val.raw_value))
                    consistency_not_achieved("gac", slots.at(0), s, all_vars, var, val);
            return;
        case BC:
            for (auto val : {s.lower_bound(var), s.upper_bound(var)})
                if (! slots.at(0).contains(val.raw_value))
                    consistency_not_achieved("bc", slots.at(0), s, all_vars, var, val);
            return;
        }
        throw NonExhaustiveSwitch{};
    }

    inline auto check_support(const std::vector<std::unordered_set<long long>> & slots, const CurrentState & s,
        const std::vector<IntegerVariableID> & all_vars, const std::vector<IntegerVariableID> & vars, CheckConsistency consistency) -> void
    {
        switch (consistency) {
            using enum CheckConsistency;
        case None: return;
        case GAC:
            for (const auto & [idx, var] : enumerate(vars))
                for (auto val : s.each_value(var))
                    if (! slots.at(idx).contains(val.raw_value))
                        consistency_not_achieved("gac", slots.at(idx), s, all_vars, var, val);
            return;
        case BC:
            for (const auto & [idx, var] : enumerate(vars))
                for (auto val : {s.lower_bound(var), s.upper_bound(var)})
                    if (! slots.at(idx).contains(val.raw_value))
                        consistency_not_achieved("bc", slots.at(idx), s, all_vars, var, val);
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
        [&]<std::size_t... i_>(std::index_sequence<i_...>) { (add_to_all_vars(all_vars_as_vector, std::get<i_>(all_vars).first), ...); }(
            std::index_sequence_for<AllArgs_...>());

        // Which consistency levels are present? Each level needs its own pass
        // over `expected` with its own "alive at this node" filter (GAC: every
        // other component in domain; BC: every other component within bounds),
        // so we skip the pass for an absent level entirely.
        const bool any_gac = [&]<std::size_t... i_>(std::index_sequence<i_...>) {
            return ((std::get<i_>(all_vars).second == CheckConsistency::GAC) || ...);
        }(std::index_sequence_for<AllArgs_...>());
        const bool any_bc = [&]<std::size_t... i_>(std::index_sequence<i_...>) {
            return ((std::get<i_>(all_vars).second == CheckConsistency::BC) || ...);
        }(std::index_sequence_for<AllArgs_...>());

        // Per top-level position, a set of locally supported values per slot
        // (one slot for a scalar, one per element of a vector position). The
        // shape is fixed across the search, so size it once and only clear
        // (keeping capacity) at each node.
        std::vector<std::vector<std::unordered_set<long long>>> support(sizeof...(AllArgs_));
        [&]<std::size_t... i_>(std::index_sequence<i_...>) { ((support[i_].resize(support_slot_count(std::get<i_>(all_vars).first))), ...); }(
            std::index_sequence_for<AllArgs_...>());

        solve_for_tests_with_callbacks(
            p, proof_name,
            [&](const CurrentState & s) -> bool {
                std::apply([&](const auto &... args) { actual.emplace(extract_from_state(s, args.first)...); }, all_vars);
                return true;
            },
            [&](const CurrentState & s) -> bool {
                for (auto & slots : support)
                    for (auto & slot : slots)
                        slot.clear();

                // A tuple is a valid support at `level` only if *every* position
                // (including None-tagged ones, e.g. a counted array) is alive at
                // this node under that level's filter.
                auto tuple_alive = [&](const auto & x, CheckConsistency level) {
                    return [&]<std::size_t... i_>(std::index_sequence<i_...>) {
                        return (component_supports(s, std::get<i_>(all_vars).first, std::get<i_>(x), level) && ...);
                    }(std::index_sequence_for<AllArgs_...>());
                };

                // One pass over `expected` per level: for each alive tuple,
                // record the value(s) of every position tagged with that level.
                auto record_level = [&](CheckConsistency level) {
                    for (const auto & x : expected) {
                        if (! tuple_alive(x, level))
                            continue;
                        [&]<std::size_t... i_>(std::index_sequence<i_...>) {
                            ((std::get<i_>(all_vars).second == level ? record_support(support[i_], std::get<i_>(x)) : (void)0), ...);
                        }(std::index_sequence_for<AllArgs_...>());
                    }
                };

                if (any_gac)
                    record_level(CheckConsistency::GAC);
                if (any_bc)
                    record_level(CheckConsistency::BC);

                [&]<std::size_t... i_>(std::index_sequence<i_...>) {
                    (check_support(support[i_], s, all_vars_as_vector, std::get<i_>(all_vars).first, std::get<i_>(all_vars).second), ...);
                }(std::index_sequence_for<AllArgs_...>());
                return true;
            });
    }

    template <typename ResultsSet_, typename... AllArgs_>
    auto solve_for_tests_checking_gac(Problem & p, const std::optional<std::string> & proof_name, const ResultsSet_ & expected, ResultsSet_ & actual,
        const std::tuple<AllArgs_...> & all_vars) -> void
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

    struct RandomBoundsOrConstant
    {
        int lower_min, lower_max, add_min, add_max;
    };

    struct RandomConstant
    {
        int lower_min, lower_max;
    };

    auto random_bounds(int lower_min, int lower_max, int add_min, int add_max) -> RandomBounds
    {
        return RandomBounds{lower_min, lower_max, add_min, add_max};
    }

    auto random_bounds_or_constant(int lower_min, int lower_max, int add_min, int add_max) -> RandomBoundsOrConstant
    {
        return RandomBoundsOrConstant{lower_min, lower_max, add_min, add_max};
    }

    auto random_constant(int lower_min, int lower_max) -> RandomConstant
    {
        return RandomConstant{lower_min, lower_max};
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

    template <typename Random_>
    auto generate_random_data_item(Random_ & rand, const RandomBoundsOrConstant & bounds)
    {
        // One in three calls produces a constant in the support of the
        // bounds-pair shape; the rest produce the pair, matching the spirit
        // of equals_test's 2:1 var-to-constant ratio.
        std::uniform_int_distribution<int> choice{0, 2};
        if (choice(rand) == 0) {
            std::uniform_int_distribution<int> const_dist{bounds.lower_min, bounds.lower_max + bounds.add_max};
            return std::variant<int, std::pair<int, int>>{const_dist(rand)};
        }
        std::uniform_int_distribution<int> lower_dist{bounds.lower_min, bounds.lower_max}, add_dist{bounds.add_min, bounds.add_max};
        auto lower = lower_dist(rand);
        auto upper = lower + add_dist(rand);
        return std::variant<int, std::pair<int, int>>{std::pair{lower, upper}};
    }

    template <typename Random_, typename Item1_, typename Item2_>
    auto generate_random_data_item(Random_ & rand, std::pair<Item1_, Item2_> values)
    {
        return std::pair{generate_random_data_item(rand, values.first), generate_random_data_item(rand, values.second)};
    }

    template <typename Random_>
    auto generate_random_data_item(Random_ & rand, const RandomConstant & constant)
    {
        std::uniform_int_distribution<int> dist{constant.lower_min, constant.lower_max};
        return dist(rand);
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

    auto create_integer_variable_or_constant(Problem & problem, std::pair<int, int> bounds) -> IntegerVariableID
    {
        return problem.create_integer_variable(Integer(bounds.first), Integer(bounds.second));
    }

    auto create_integer_variable_or_constant(Problem & problem, std::vector<int> values) -> IntegerVariableID
    {
        std::vector<Integer> vs;
        for (auto v : values)
            vs.push_back(Integer(v));
        return problem.create_integer_variable(vs);
    }

    auto create_integer_variable_or_constant(Problem &, int value) -> IntegerVariableID
    {
        return ConstantIntegerVariableID{Integer(value)};
    }

    /**
     * \brief Describes how to wrap a test variable as a view.
     *
     * A test variable can be presented to the constraint under test in one of
     * three shapes:
     *  - as a bare SimpleIntegerVariableID (no view machinery exercised),
     *  - as a ViewOfIntegerVariableID with negate_first = false,
     *  - as a ViewOfIntegerVariableID with negate_first = true.
     *
     * The wrap is applied to the IntegerVariableID returned to the test, while
     * the underlying SimpleIntegerVariableID is created with an adjusted
     * domain so that the view's values match the domain spec the test asked
     * for. This keeps the test's is_satisfying predicate and expected-results
     * set unchanged — only the constraint-side encoding differs.
     *
     * Use the factory helpers (view_none, view_offset, view_neg,
     * view_neg_offset) rather than constructing this struct directly.
     */
    struct ViewWrap
    {
        bool bare;   ///< if true, use a bare variable and ignore negate/offset
        bool negate; ///< negate_first for the resulting ViewOfIntegerVariableID
        int offset;  ///< then_add for the resulting ViewOfIntegerVariableID

        [[nodiscard]] constexpr auto operator<=>(const ViewWrap &) const = default;
    };

    /// No wrap: hand the test a bare SimpleIntegerVariableID.
    [[nodiscard]] constexpr inline auto view_none() -> ViewWrap
    {
        return {true, false, 0};
    }

    /// Wrap as `var + k`. With k = 0 this still constructs a
    /// ViewOfIntegerVariableID, exercising the view layer transparently.
    [[nodiscard]] constexpr inline auto view_offset(int k) -> ViewWrap
    {
        return {false, false, k};
    }

    /// Wrap as `-var`.
    [[nodiscard]] constexpr inline auto view_neg() -> ViewWrap
    {
        return {false, true, 0};
    }

    /// Wrap as `-var + k`.
    [[nodiscard]] constexpr inline auto view_neg_offset(int k) -> ViewWrap
    {
        return {false, true, k};
    }

    /**
     * \brief The canonical sweep over view forms for the proof-view audit.
     *
     * Covers:
     *  - bare variable (no view at all);
     *  - identity view (negate = false, offset = 0) — exercises the view
     *    layer while remaining semantically equivalent to bare;
     *  - offset-only views with magnitudes {1, 5, 6, 17}, both signs;
     *  - negation alone, and negation combined with the same offset spread.
     *
     * Magnitudes 5/6 bracket the suspected boundary where small-constant
     * special-cases stop coinciding with correct behaviour; 17 is a generic
     * "definitely large" value; 1 catches off-by-one mistakes.
     *
     * Total: 19 wraps. Per-test sweep policy is chosen by the caller; the
     * intended Phase 2 policy is:
     *  - "single-position": run the test N times for an N-arg constraint,
     *    wrapping one argument at a time and leaving the rest bare (19*N
     *    configurations);
     *  - "uniform": run the test once with every argument wrapped the same
     *    way (19 configurations).
     * The full cross-product is intentionally avoided.
     */
    inline auto all_view_wraps() -> std::vector<ViewWrap>
    {
        return {
            view_none(),
            view_offset(0),
            view_offset(1),
            view_offset(-1),
            view_offset(5),
            view_offset(-5),
            view_offset(6),
            view_offset(-6),
            view_offset(17),
            view_offset(-17),
            view_neg(),
            view_neg_offset(1),
            view_neg_offset(-1),
            view_neg_offset(5),
            view_neg_offset(-5),
            view_neg_offset(6),
            view_neg_offset(-6),
            view_neg_offset(17),
            view_neg_offset(-17),
        };
    }

    /**
     * \brief Inverse of a view's transformation.
     *
     * Given a value the test expects to observe (a view value) and the wrap
     * that produced the view, returns the value the underlying
     * SimpleIntegerVariableID must take. View value v = (negate ? -x : x) +
     * offset, so x = negate ? offset - v : v - offset.
     */
    [[nodiscard]] inline auto invert_view(ViewWrap wrap, int value) -> int
    {
        return wrap.negate ? wrap.offset - value : value - wrap.offset;
    }

    /**
     * \brief Bounds-domain variant: wrap-aware variable creation.
     *
     * For a ViewWrap that isn't `view_none()`, creates the underlying
     * SimpleIntegerVariableID with domain [invert(lo), invert(hi)] (swapped if
     * needed for negation), then applies the view operators to land back on
     * the requested visible domain.
     */
    auto create_integer_variable_or_constant_with_view(Problem & problem, std::pair<int, int> bounds, ViewWrap wrap) -> IntegerVariableID
    {
        if (wrap.bare)
            return create_integer_variable_or_constant(problem, bounds);

        auto u_lo = invert_view(wrap, bounds.first);
        auto u_hi = invert_view(wrap, bounds.second);
        if (u_lo > u_hi)
            std::swap(u_lo, u_hi);

        IntegerVariableID v = problem.create_integer_variable(Integer(u_lo), Integer(u_hi));
        if (wrap.negate)
            v = -v;
        if (wrap.offset != 0)
            v = v + Integer(wrap.offset);
        else if (! wrap.negate)
            v = v + Integer(0); // force a ViewOfIntegerVariableID for the identity-view case
        return v;
    }

    /**
     * \brief Enumerated-value-list variant: wrap-aware variable creation.
     *
     * Each value is inverted through the wrap so that, once the view applies
     * its transformation, the visible value set matches the input.
     */
    auto create_integer_variable_or_constant_with_view(Problem & problem, std::vector<int> values, ViewWrap wrap) -> IntegerVariableID
    {
        if (wrap.bare)
            return create_integer_variable_or_constant(problem, values);

        std::vector<Integer> vs;
        for (auto value : values)
            vs.push_back(Integer(invert_view(wrap, value)));

        IntegerVariableID v = problem.create_integer_variable(vs);
        if (wrap.negate)
            v = -v;
        if (wrap.offset != 0)
            v = v + Integer(wrap.offset);
        else if (! wrap.negate)
            v = v + Integer(0);
        return v;
    }

    /**
     * \brief Constant variant: wraps are a no-op.
     *
     * Wrapping a constant collapses to an equivalent constant by the
     * semantics in variable_id.cc, exercising no view machinery. Provided so
     * that callers iterating over mixed var/const argument lists can apply a
     * wrap uniformly.
     */
    auto create_integer_variable_or_constant_with_view(Problem & problem, int value, ViewWrap) -> IntegerVariableID
    {
        return create_integer_variable_or_constant(problem, value);
    }

    /**
     * \brief Vector variant: per-element wrap-aware variable creation.
     *
     * `specs` and `wraps` must have equal size. Each element is dispatched to
     * the appropriate scalar overload of create_integer_variable_or_constant_with_view.
     */
    template <typename Spec_>
    auto create_integer_variable_or_constant_vector_with_views(
        Problem & problem, const std::vector<Spec_> & specs, const std::vector<ViewWrap> & wraps) -> std::vector<IntegerVariableID>
    {
        if (specs.size() != wraps.size())
            throw UnexpectedException{"create_integer_variable_or_constant_vector_with_views: spec / wrap size mismatch"};
        std::vector<IntegerVariableID> result;
        result.reserve(specs.size());
        for (std::size_t i = 0; i < specs.size(); ++i)
            result.push_back(create_integer_variable_or_constant_with_view(problem, specs.at(i), wraps.at(i)));
        return result;
    }

    /**
     * \brief A specific (wrap, position) configuration to apply during one
     * test run.
     *
     * `wrap_index` indexes into all_view_wraps(). When `single_position` is
     * set, only that variable position takes the chosen wrap and the rest
     * stay bare; when unset, every position takes the wrap (uniform sweep).
     * Default-constructed: wrap_index = 0 (view_none), uniform — matches the
     * pre-sweep test behaviour.
     *
     * When `mixed` is set, `wrap_index` and `single_position` are ignored and
     * each position takes a *different* wrap from a fixed cycle (see
     * `mixed_view_cycle`): distinct large offsets and a mix of negated and
     * non-negated. This is the one configuration that exercises two different
     * views in the same constraint at once — the cross-view interactions the
     * uniform and single-position policies can't reach — and is cheap enough
     * to run on every constraint test, not just under the full sweep.
     */
    struct ViewWrapConfig
    {
        int wrap_index = 0;
        std::optional<int> single_position{};
        bool mixed = false;
    };

    /**
     * \brief The per-position wrap cycle used by the `mixed` policy.
     *
     * Chosen so that any constraint with at least two positions gets at least
     * one positive large-offset view and at least one negated large-offset
     * view, with *different* offsets, so cross-view cancellation and
     * differing bit-vector widths are genuinely exercised.
     */
    inline auto mixed_view_cycle() -> std::array<ViewWrap, 4>
    {
        return {view_offset(17), view_neg_offset(13), view_offset(-11), view_neg_offset(-7)};
    }

    /**
     * \brief Parse view-sweep flags out of argv, leaving other args alone.
     *
     * Recognised flags:
     *  - `--view-wrap=N`         : integer index into all_view_wraps()
     *  - `--view-position=all`   : uniform sweep across all positions
     *  - `--view-position=K`     : single-position sweep, position K
     *
     * Returns the default ViewWrapConfig (no wrapping) if neither flag is
     * present. Unknown args are ignored so existing mode-style argv (e.g. the
     * comparison_test "ge" / "ge_if" / ... selectors) keeps working.
     */
    inline auto parse_view_wrap_config_from_argv(int argc, char * argv[]) -> ViewWrapConfig
    {
        ViewWrapConfig cfg;
        for (int i = 1; i < argc; ++i) {
            std::string arg = argv[i];
            if (arg.starts_with("--view-wrap="))
                cfg.wrap_index = std::stoi(arg.substr(std::string{"--view-wrap="}.size()));
            else if (arg.starts_with("--view-position=")) {
                auto val = arg.substr(std::string{"--view-position="}.size());
                if (val == "all" || val == "uniform")
                    cfg.single_position = std::nullopt;
                else if (val == "mixed")
                    cfg.mixed = true;
                else
                    cfg.single_position = std::stoi(val);
            }
        }
        return cfg;
    }

    /**
     * \brief Realise a ViewWrapConfig into a per-position wrap list.
     *
     * - Uniform sweep (single_position unset): every entry is wraps[wrap_index].
     * - Single-position sweep: position `*single_position` gets
     *   wraps[wrap_index], the rest get view_none(). Out-of-range positions
     *   are silently clamped (so a config that names a position higher than
     *   the constraint has degrades to "all bare", which the test can detect
     *   and skip rather than producing duplicated bare-sweep coverage).
     */
    inline auto wraps_for_positions(ViewWrapConfig cfg, int n_positions) -> std::vector<ViewWrap>
    {
        std::vector<ViewWrap> result(static_cast<std::size_t>(n_positions), view_none());
        if (cfg.mixed) {
            auto cycle = mixed_view_cycle();
            for (std::size_t i = 0; i < result.size(); ++i)
                result[i] = cycle[i % cycle.size()];
            return result;
        }
        auto wraps = all_view_wraps();
        auto chosen = wraps.at(static_cast<std::size_t>(cfg.wrap_index));
        if (cfg.single_position) {
            if (*cfg.single_position >= 0 && *cfg.single_position < n_positions)
                result.at(static_cast<std::size_t>(*cfg.single_position)) = chosen;
        }
        else {
            std::fill(result.begin(), result.end(), chosen);
        }
        return result;
    }

    /**
     * \brief Stable, filename-safe label for a ViewWrapConfig.
     *
     * Used to disambiguate proof output filenames when the same test binary
     * runs many times in the same working directory. Examples: "w0_pall",
     * "w5_p2", "w12_pall".
     */
    inline auto view_wrap_config_label(const ViewWrapConfig & cfg) -> std::string
    {
        if (cfg.mixed)
            return "mixed";
        std::string s = "w" + std::to_string(cfg.wrap_index) + "_p";
        s += cfg.single_position ? std::to_string(*cfg.single_position) : "all";
        return s;
    }

    /**
     * \brief Whether this config would produce no actual wrapping.
     *
     * True when wrap_index = 0 (view_none) or when single_position is set but
     * out of range. The redundant-coverage cases that CMake's sweep would
     * generate are detected here so the test can skip them and ctest sees
     * "skipped" rather than a duplicate bare run.
     */
    inline auto view_wrap_config_is_effectively_bare(const ViewWrapConfig & cfg, int n_positions) -> bool
    {
        if (cfg.mixed)
            return n_positions == 0;
        if (cfg.wrap_index == 0)
            return true;
        if (cfg.single_position && (*cfg.single_position < 0 || *cfg.single_position >= n_positions))
            return true;
        return false;
    }
}

#endif
