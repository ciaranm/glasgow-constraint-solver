#include <gcs/constraints/innards/constraints_test_utils.hh>
#include <gcs/constraints/nogoods.hh>
#include <gcs/current_state.hh>
#include <gcs/exception.hh>
#include <gcs/problem.hh>
#include <gcs/search_heuristics.hh>
#include <gcs/solve.hh>
#include <gcs/stats.hh>
#include <gcs/variable_condition.hh>

#include <cstddef>
#include <cstdlib>
#include <iostream>
#include <optional>
#include <random>
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
using std::mt19937;
using std::nullopt;
using std::pair;
using std::random_device;
using std::set;
using std::size_t;
using std::tuple;
using std::uniform_int_distribution;
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

    auto run_nogoods_test(bool refined, bool proofs, const vector<pair<int, int>> & domains, const vector<TestNogood> & nogoods) -> void
    {
        print(cerr, "nogoods [{}] {} vars, {} nogoods{}", refined ? "refined" : "scan", domains.size(), nogoods.size(), proofs ? " with proofs:" : ":");
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
        p.post(Nogoods{std::move(posted), refined});

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

    using Instance = pair<vector<pair<int, int>>, vector<TestNogood>>;

    // The hand-picked instances, shared by the per-mode oracle/UP/proof tests and
    // the scan-vs-refined differential.
    auto hand_picked_instances() -> vector<Instance>
    {
        using enum VariableConditionOperator;
        return {
            // Pure equality nogoods (a NegativeTable in disguise).
            {{{1, 3}, {1, 3}}, {{{0, Equal, 1}, {1, Equal, 1}}}},
            // Exclude the diagonal.
            {{{1, 3}, {1, 3}}, {{{0, Equal, 1}, {1, Equal, 1}}, {{0, Equal, 2}, {1, Equal, 2}}, {{0, Equal, 3}, {1, Equal, 3}}}},
            // Cascade: (x=1, y=*) all forbidden forces x != 1.
            {{{1, 3}, {1, 3}}, {{{0, Equal, 1}, {1, Equal, 1}}, {{0, Equal, 1}, {1, Equal, 2}}, {{0, Equal, 1}, {1, Equal, 3}}}},
            // A unit nogood over an order literal: forbids x >= 4, i.e. forces x < 4.
            {{{0, 6}}, {{{0, GreaterEqual, 4}}}},
            // Order literals: forbid (x >= 3 and y < 3).
            {{{0, 5}, {0, 5}}, {{{0, GreaterEqual, 3}, {1, Less, 3}}}},
            // Entailment watching: x is in [11, 13] so x >= 10 always holds; the
            // nogood (x >= 10 and y = 5) must therefore force y != 5. The oracle's
            // bound-based entailment fires on the >= 11 bound, so a propagator that
            // matched x >= 10 only exactly would be caught.
            {{{11, 13}, {4, 6}}, {{{0, GreaterEqual, 10}, {1, Equal, 5}}}},
            // Mixed literal kinds in one nogood.
            {{{0, 3}, {0, 3}, {0, 3}}, {{{0, Equal, 1}, {1, GreaterEqual, 2}, {2, NotEqual, 2}}}},
            // A not-equal literal: forbid (x != 2 and y != 2) over small domains.
            {{{1, 3}, {1, 3}}, {{{0, NotEqual, 2}, {1, NotEqual, 2}}}},
            // Unsatisfiable at the root: forbid both x <= 2 and x >= 3 over [0, 5].
            {{{0, 5}}, {{{0, Less, 3}}, {{0, GreaterEqual, 3}}}},
            // Several order nogoods that interact over three variables.
            {{{0, 4}, {0, 4}, {0, 4}}, {{{0, GreaterEqual, 3}, {1, GreaterEqual, 3}}, {{1, Less, 2}, {2, Less, 2}}, {{0, Equal, 0}, {2, GreaterEqual, 4}}}},
        };
    }

    auto run_all_tests(bool refined, bool proofs) -> void
    {
        for (const auto & [domains, nogoods] : hand_picked_instances())
            run_nogoods_test(refined, proofs, domains, nogoods);
    }

    // Solve one instance in the chosen trigger mode with a deterministic,
    // degree-independent brancher (in_order), returning the search statistics.
    // Because in_order ignores degree, the scan path (which adds an on_change
    // trigger per variable) and the refined path (which adds none) branch
    // identically, so any difference in recursions or solutions is a difference
    // in *propagation* -- a missed inference under-propagates and explores more
    // nodes; an unsound inference prunes a real solution.
    template <typename ValueGen_>
    auto solve_for_differential(bool refined, const vector<pair<int, int>> & domains,
        const vector<TestNogood> & nogoods, ValueGen_ value_gen) -> Stats
    {
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
        p.post(Nogoods{std::move(posted), refined});

        return solve_with(p,
            SolveCallbacks{
                .solution = [](const CurrentState &) { return true; },
                .branch = branch_with(variable_order::in_order(vars), value_gen)});
    }

    auto run_differential(const vector<pair<int, int>> & domains, const vector<TestNogood> & nogoods) -> void
    {
        auto check = [&](auto make_value_gen, const char * label) {
            auto scan = solve_for_differential(false, domains, nogoods, make_value_gen());
            auto refined = solve_for_differential(true, domains, nogoods, make_value_gen());
            println(cerr, "nogoods differential [{}] {} vars {} nogoods: scan rec={} sol={} | refined rec={} sol={}",
                label, domains.size(), nogoods.size(), scan.recursions, scan.solutions, refined.recursions, refined.solutions);
            if (scan.recursions != refined.recursions || scan.solutions != refined.solutions) {
                println(cerr, "DIVERGED. instance:");
                for (size_t vi = 0; vi < domains.size(); ++vi)
                    println(cerr, "  var {}: [{}, {}]", vi, domains[vi].first, domains[vi].second);
                for (const auto & ng : nogoods) {
                    print(cerr, "  nogood:");
                    for (const auto & l : ng)
                        print(cerr, " (v{} op{} {})", l.var, static_cast<int>(l.op), l.value);
                    println(cerr, "");
                }
                throw UnexpectedException{"refined nogoods diverged from scan: different search tree or solution count"};
            }
        };
        // Instantiation branching (each upper-/single-value decision) and bounds-
        // splitting (gradual order-literal entailment, more backtracking): both
        // must give scan and refined the identical tree.
        check([] { return value_order::smallest_in(); }, "smallest");
        check([] { return value_order::split_smallest_first(); }, "split");
    }

    // Random, often backtrack-heavy instances for the differential: small domains,
    // a handful of nogoods of mixed literal kinds, so clauses go unit and conflict
    // and watches move and are restored across many backtracks.
    auto run_random_differentials() -> void
    {
        using enum VariableConditionOperator;
        mt19937 rng;
        if (auto seed = get_seed())
            rng.seed(*seed);
        else
            rng.seed(random_device{}());

        auto pick_op = [&]() {
            switch (uniform_int_distribution{0, 3}(rng)) {
            case 0: return Equal;
            case 1: return NotEqual;
            case 2: return GreaterEqual;
            default: return Less;
            }
        };

        for (int iter = 0; iter < 300; ++iter) {
            int nvars = uniform_int_distribution{2, 4}(rng);
            vector<pair<int, int>> domains;
            for (int v = 0; v < nvars; ++v) {
                int lo = uniform_int_distribution{0, 3}(rng);
                domains.emplace_back(lo, lo + uniform_int_distribution{0, 4}(rng));
            }

            int nng = uniform_int_distribution{1, 6}(rng);
            vector<TestNogood> nogoods;
            for (int n = 0; n < nng; ++n) {
                TestNogood ng;
                int len = uniform_int_distribution{1, 4}(rng);
                for (int l = 0; l < len; ++l) {
                    auto var = static_cast<size_t>(uniform_int_distribution{0, nvars - 1}(rng));
                    // A value spanning just outside the domain, so literals are a
                    // mix of always-/never-/sometimes-true.
                    int value = uniform_int_distribution{domains[var].first - 1, domains[var].second + 1}(rng);
                    ng.push_back(TestLit{var, pick_op(), value});
                }
                nogoods.push_back(std::move(ng));
            }
            run_differential(domains, nogoods);
        }
    }

    auto run_all_differentials() -> void
    {
        for (const auto & [domains, nogoods] : hand_picked_instances())
            run_differential(domains, nogoods);
        run_random_differentials();
    }
}

auto main(int argc, char * argv[]) -> int
{
    set_seed_from_argv(argc, argv);

    // Scan vs refined must explore the identical tree and find the identical
    // solutions on every instance: a pure same-tree differential (no proof needed).
    run_all_differentials();

    // Each mode independently checked against the brute-force oracle and the
    // per-node unit-propagation reference, with its proof verified when veripb is
    // available.
    for (bool refined : {false, true})
        for (bool proofs : {false, true}) {
            if (proofs && ! can_run_veripb())
                continue;
            run_all_tests(refined, proofs);
        }

    return EXIT_SUCCESS;
}
