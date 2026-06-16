#include <gcs/constraints/innards/constraints_test_utils.hh>
#include <gcs/constraints/nogoods.hh>
#include <gcs/current_state.hh>
#include <gcs/exception.hh>
#include <gcs/problem.hh>
#include <gcs/solve.hh>
#include <gcs/variable_condition.hh>

#include <cstddef>
#include <cstdlib>
#include <iostream>
#include <optional>
#include <set>
#include <tuple>
#include <utility>
#include <vector>
#include <version>

#if defined(__cpp_lib_print) && defined(__cpp_lib_format)
#include <print>
#else
#include <fmt/core.h>
#include <fmt/ostream.h>
#endif

using namespace gcs;
using namespace gcs::test_innards;

using std::cerr;
using std::flush;
using std::make_optional;
using std::nullopt;
using std::pair;
using std::set;
using std::size_t;
using std::tuple;
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
    // A literal of a test nogood, by variable index so the same nogood drives
    // both the posted constraint and the independent oracle.
    struct TestLit
    {
        size_t var;
        VariableConditionOperator op;
        int value;
    };
    using TestNogood = vector<TestLit>;

    auto literal_true_on(const TestLit & l, const vector<int> & assignment) -> bool
    {
        using enum VariableConditionOperator;
        switch (l.op) {
        case Equal: return assignment[l.var] == l.value;
        case NotEqual: return assignment[l.var] != l.value;
        case GreaterEqual: return assignment[l.var] >= l.value;
        case Less: return assignment[l.var] < l.value;
        }
        return false;
    }

    auto make_condition(const vector<IntegerVariableID> & vars, const TestLit & l) -> IntegerVariableCondition
    {
        return VariableConditionFrom<IntegerVariableID>{vars[l.var], l.op, Integer{l.value}};
    }

    enum class Holds
    {
        True,
        False,
        Undecided
    };

    // The oracle's own bound-based entailment, independent of the propagator's.
    // For >= / < it is genuinely bound-based (x >= 10 holds once lower >= 10), so
    // it catches a propagator that only matched literals exactly.
    auto literal_holds(const CurrentState & s, const vector<IntegerVariableID> & vars, const TestLit & l) -> Holds
    {
        using enum VariableConditionOperator;
        auto v = vars[l.var];
        Integer val{l.value};
        switch (l.op) {
        case Equal:
            if (! s.in_domain(v, val))
                return Holds::False;
            return s.has_single_value(v) ? Holds::True : Holds::Undecided;
        case NotEqual:
            if (! s.in_domain(v, val))
                return Holds::True;
            return s.has_single_value(v) ? Holds::False : Holds::Undecided;
        case GreaterEqual:
            if (s.lower_bound(v) >= val)
                return Holds::True;
            if (s.upper_bound(v) < val)
                return Holds::False;
            return Holds::Undecided;
        case Less:
            if (s.upper_bound(v) < val)
                return Holds::True;
            if (s.lower_bound(v) >= val)
                return Holds::False;
            return Holds::Undecided;
        }
        return Holds::Undecided;
    }

    auto run_nogoods_test(bool proofs, const vector<pair<int, int>> & domains, const vector<TestNogood> & nogoods) -> void
    {
        print(cerr, "nogoods {} vars, {} nogoods{}", domains.size(), nogoods.size(), proofs ? " with proofs:" : ":");
        cerr << flush;

        // Oracle: an assignment is a solution iff no nogood is fully satisfied.
        set<tuple<vector<int>>> expected, actual;
        build_expected(
            expected, [&](const vector<int> & a) -> bool {
                for (const auto & nogood : nogoods) {
                    bool all_true = true;
                    for (const auto & l : nogood)
                        if (! literal_true_on(l, a)) {
                            all_true = false;
                            break;
                        }
                    if (all_true)
                        return false;
                }
                return true;
            },
            domains);
        println(cerr, " expecting {} solutions", expected.size());

        Problem p;
        vector<IntegerVariableID> vars;
        for (const auto & d : domains)
            vars.push_back(p.create_integer_variable(Integer{d.first}, Integer{d.second}));

        vector<Nogood> posted;
        for (const auto & nogood : nogoods) {
            Nogood n;
            for (const auto & l : nogood)
                n.push_back(make_condition(vars, l));
            posted.push_back(std::move(n));
        }
        p.post(Nogoods{std::move(posted)});

        auto proof_name = proofs ? make_optional<std::string>("nogoods_test") : nullopt;

        solve_for_tests_with_callbacks(
            p, proof_name,
            [&](const CurrentState & s) -> bool {
                actual.emplace(extract_from_state(s, vars));
                return true;
            },
            [&](const CurrentState & s) -> bool {
                // Per-clause unit-propagation reference. At every node, for each
                // nogood: if no literal is falsified then the clause is not yet
                // satisfied, so at least two literals must still be non-entailed
                // (the two watches). One or zero ⇒ the propagator missed a unit
                // inference or a contradiction.
                for (const auto & nogood : nogoods) {
                    int entailed = 0, falsified = 0;
                    for (const auto & l : nogood)
                        switch (literal_holds(s, vars, l)) {
                        case Holds::True: ++entailed; break;
                        case Holds::False: ++falsified; break;
                        case Holds::Undecided: break;
                        }
                    if (falsified == 0 && entailed > static_cast<int>(nogood.size()) - 2)
                        throw UnexpectedException{"nogood under-propagated: a clause was unit or violated but not enforced"};
                }
                return true;
            });

        check_results(proof_name, expected, actual);
    }

    auto run_all_tests(bool proofs) -> void
    {
        using enum VariableConditionOperator;

        // Pure equality nogoods (a NegativeTable in disguise).
        run_nogoods_test(proofs, {{1, 3}, {1, 3}},
            {{{0, Equal, 1}, {1, Equal, 1}}});
        // Exclude the diagonal.
        run_nogoods_test(proofs, {{1, 3}, {1, 3}},
            {{{0, Equal, 1}, {1, Equal, 1}}, {{0, Equal, 2}, {1, Equal, 2}}, {{0, Equal, 3}, {1, Equal, 3}}});
        // Cascade: (x=1, y=*) all forbidden forces x != 1.
        run_nogoods_test(proofs, {{1, 3}, {1, 3}},
            {{{0, Equal, 1}, {1, Equal, 1}}, {{0, Equal, 1}, {1, Equal, 2}}, {{0, Equal, 1}, {1, Equal, 3}}});

        // A unit nogood over an order literal: forbids x >= 4, i.e. forces x < 4.
        run_nogoods_test(proofs, {{0, 6}},
            {{{0, GreaterEqual, 4}}});

        // Order literals: forbid (x >= 3 and y < 3).
        run_nogoods_test(proofs, {{0, 5}, {0, 5}},
            {{{0, GreaterEqual, 3}, {1, Less, 3}}});

        // Entailment watching: x is in [11, 13] so x >= 10 always holds; the
        // nogood (x >= 10 and y = 5) must therefore force y != 5. The oracle's
        // bound-based entailment fires on the >= 11 bound, so a propagator that
        // matched x >= 10 only exactly would be caught.
        run_nogoods_test(proofs, {{11, 13}, {4, 6}},
            {{{0, GreaterEqual, 10}, {1, Equal, 5}}});

        // Mixed literal kinds in one nogood.
        run_nogoods_test(proofs, {{0, 3}, {0, 3}, {0, 3}},
            {{{0, Equal, 1}, {1, GreaterEqual, 2}, {2, NotEqual, 2}}});

        // A not-equal literal: forbid (x != 2 and y != 2) over small domains.
        run_nogoods_test(proofs, {{1, 3}, {1, 3}},
            {{{0, NotEqual, 2}, {1, NotEqual, 2}}});

        // Unsatisfiable at the root: forbid both x <= 2 and x >= 3 over [0, 5].
        run_nogoods_test(proofs, {{0, 5}},
            {{{0, Less, 3}}, {{0, GreaterEqual, 3}}});

        // Several order nogoods that interact over three variables.
        run_nogoods_test(proofs, {{0, 4}, {0, 4}, {0, 4}},
            {{{0, GreaterEqual, 3}, {1, GreaterEqual, 3}},
                {{1, Less, 2}, {2, Less, 2}},
                {{0, Equal, 0}, {2, GreaterEqual, 4}}});
    }
}

auto main(int argc, char * argv[]) -> int
{
    set_seed_from_argv(argc, argv);

    for (bool proofs : {false, true}) {
        if (proofs && ! can_run_veripb())
            continue;
        run_all_tests(proofs);
    }

    return EXIT_SUCCESS;
}
