/* Test vehicle for the refined per-literal trigger mechanism (issue #335, stage
 * B1). MiniLinearGreaterEqual is a deliberately small `sum c_i x_i >= K`
 * bounds-consistency propagator (all c_i > 0, all x_i >= 0) that drives itself
 * ENTIRELY from refined watches: it has no coarse Triggers, arms one upper-bound
 * watch per variable at install, and re-arms a variable's watch when it fires.
 *
 * It exists only to exercise the refined-watch engine (the index, the fired-watch
 * inbox, consume-on-fire, re-arm, and restore-on-backtrack); it is not a public
 * constraint and is expected to be retired once refined triggers fold into the
 * real Linear (stage E). Correctness is checked the same way the real Linear is:
 * a brute-force solution oracle (catches over-pruning and any missed leaf check)
 * plus per-node bounds-consistency checking (catches under-pruning, including a
 * watch that was not restored after backtrack, since the check runs at
 * post-backtrack nodes too).
 */

#include <gcs/constraint.hh>
#include <gcs/constraints/innards/constraints_test_utils.hh>
#include <gcs/current_state.hh>
#include <gcs/exception.hh>
#include <gcs/expression.hh>
#include <gcs/innards/inference_tracker.hh>
#include <gcs/innards/justification.hh>
#include <gcs/innards/propagators.hh>
#include <gcs/innards/reason.hh>
#include <gcs/innards/state.hh>
#include <gcs/problem.hh>
#include <gcs/solve.hh>
#include <gcs/stats.hh>

#include <util/enumerate.hh>

#include <cstdint>
#include <cstdlib>
#include <functional>
#include <iostream>
#include <memory>
#include <random>
#include <set>
#include <tuple>
#include <utility>
#include <vector>

using std::make_optional;
using std::make_unique;
using std::move;
using std::mt19937;
using std::nullopt;
using std::pair;
using std::random_device;
using std::set;
using std::string;
using std::tuple;
using std::uniform_int_distribution;
using std::unique_ptr;
using std::vector;

#if defined(__cpp_lib_print) && defined(__cpp_lib_format)
using std::print;
using std::println;
#else
using fmt::print;
using fmt::println;
#endif

using std::cerr;
using std::flush;

using namespace gcs;
using namespace gcs::innards;
using namespace gcs::test_innards;

namespace
{
    // A minimal certified-free `sum c_i x_i >= K` propagator (positive
    // coefficients, non-negative variables) that triggers only through refined
    // watches. No proof is emitted, so its tests run without --prove; the trigger
    // mechanism it exercises is semantics-preserving and carries no proof
    // obligation of its own, and the real Linear already certifies the logic.
    class MiniLinearGreaterEqual : public Constraint
    {
    private:
        WeightedSum _coeff_vars;
        Integer _value;
        bool _refined;

    public:
        // refined = true drives the propagator from refined upper-bound watches;
        // false falls back to coarse on_bounds triggers with the identical
        // propagation body, so the two can be compared directly.
        explicit MiniLinearGreaterEqual(WeightedSum coeff_vars, Integer value, bool refined = true) :
            _coeff_vars(move(coeff_vars)),
            _value(value),
            _refined(refined)
        {
        }

        auto install(Propagators & propagators, State & initial_state, ProofModel * const) && -> void override
        {
            vector<pair<Integer, IntegerVariableID>> terms;
            for (const auto & [coeff, var] : _coeff_vars.terms)
                terms.emplace_back(coeff, var);

            // Arm one upper-bound watch per variable: x_i < ub(x_i) becomes entailed
            // exactly when x_i's upper bound next drops. Payload = the variable's
            // index into terms, so the propagator knows which watch to re-arm.
            Triggers triggers;
            if (_refined)
                for (const auto & [idx, term] : enumerate(terms))
                    triggers.refined.emplace_back(term.second < initial_state.upper_bound(term.second),
                        static_cast<std::uint32_t>(idx));
            else
                for (const auto & term : terms)
                    triggers.on_bounds.push_back(term.second);

            propagators.install(
                constraint_id(),
                [terms = move(terms), value = _value](
                    const State & state, auto & inference, ProofLogger * const logger,
                    const RefinedWatchContext & watches) -> PropagatorState {
                    Integer max_sum{0_i};
                    for (const auto & [coeff, var] : terms)
                        max_sum += coeff * state.upper_bound(var);

                    if (max_sum < value)
                        inference.contradiction(logger, JustifyUsingRUP{}, ReasonFunction{});
                    else {
                        auto slack = max_sum - value;
                        for (const auto & [coeff, var] : terms) {
                            auto new_lower = state.upper_bound(var) - (slack / coeff);
                            if (new_lower > state.lower_bound(var))
                                inference.infer_greater_than_or_equal(logger, var, new_lower, JustifyUsingRUP{}, ReasonFunction{});
                        }
                        // A watch is consumed when it fires; re-arm each fired
                        // variable's upper-bound watch at its now-lower bound.
                        for (auto payload : watches.fired_payloads()) {
                            auto var = terms[payload].second;
                            watches.watch(var < state.upper_bound(var), payload);
                        }
                    }
                    return PropagatorState::Enable;
                },
                triggers);
        }

        auto clone() const -> unique_ptr<Constraint> override
        {
            return make_unique<MiniLinearGreaterEqual>(_coeff_vars, _value, _refined);
        }

        auto s_exprify(const ProofModel * const) const -> string override
        {
            return "mini_linear_greater_equal";
        }
    };

    // One `sum c_i x_i >= K` over three non-negative variables: enumerate every
    // solution and check it against the brute-force oracle, with per-node
    // bounds-consistency checking on every variable.
    auto run_mini_linear_ge_test(pair<int, int> v1_range, pair<int, int> v2_range, pair<int, int> v3_range,
        vector<int> coeffs, int value) -> void
    {
        print(cerr, "mini_linear ge {} {} {} coeffs={} >= {}:", v1_range, v2_range, v3_range, coeffs, value);
        cerr << flush;

        auto is_satisfying = [&](int a, int b, int c) {
            return coeffs[0] * a + coeffs[1] * b + coeffs[2] * c >= value;
        };

        set<tuple<int, int, int>> expected, actual;
        build_expected(expected, is_satisfying, v1_range, v2_range, v3_range);
        println(cerr, " expecting {} solutions", expected.size());

        Problem p;
        auto v1 = p.create_integer_variable(Integer(v1_range.first), Integer(v1_range.second));
        auto v2 = p.create_integer_variable(Integer(v2_range.first), Integer(v2_range.second));
        auto v3 = p.create_integer_variable(Integer(v3_range.first), Integer(v3_range.second));
        auto vs = vector<IntegerVariableID>{v1, v2, v3};

        WeightedSum c;
        for (const auto & [idx, coeff] : enumerate(coeffs))
            c += Integer{coeff} * vs[idx];
        p.post(MiniLinearGreaterEqual{c, Integer{value}});

        solve_for_tests_checking_consistency(p, nullopt, expected, actual,
            tuple{pair{v1, CheckConsistency::BC}, pair{v2, CheckConsistency::BC}, pair{v3, CheckConsistency::BC}});

        check_results(nullopt, expected, actual);

        // check_results compares solution SETS, which hides a solution reported more
        // than once (a backtrack/watch bug can re-explore a subtree). Assert the raw
        // count from a plain enumeration matches the oracle too.
        Problem pc;
        auto c1 = pc.create_integer_variable(Integer(v1_range.first), Integer(v1_range.second));
        auto c2 = pc.create_integer_variable(Integer(v2_range.first), Integer(v2_range.second));
        auto c3 = pc.create_integer_variable(Integer(v3_range.first), Integer(v3_range.second));
        auto cvs = vector<IntegerVariableID>{c1, c2, c3};
        WeightedSum cc;
        for (const auto & [idx, coeff] : enumerate(coeffs))
            cc += Integer{coeff} * cvs[idx];
        pc.post(MiniLinearGreaterEqual{cc, Integer{value}});
        auto stats = solve(pc, [](const CurrentState &) { return true; });
        if (stats.solutions != expected.size())
            throw UnexpectedException{"mini_linear produced the wrong number of solutions (duplicates or missing)"};
    }

    // Positive-laziness / same-tree check: solve the same instance with refined
    // watches and with coarse on_bounds (identical propagation body). Both must
    // explore the same search tree (equal recursions: same bounds-consistent
    // fixpoint, same brancher), and the refined version must never wake more often
    // -- it skips the lower-bound-change and self-retrigger wakes coarse on_bounds
    // incurs. The printed counts show the reduction; the mutation tests separately
    // confirm the refined path is load-bearing rather than a silent fallback.
    auto measure_laziness(pair<int, int> v1_range, pair<int, int> v2_range, pair<int, int> v3_range,
        vector<int> coeffs, int value) -> void
    {
        auto run = [&](bool refined) -> Stats {
            Problem p;
            auto v1 = p.create_integer_variable(Integer(v1_range.first), Integer(v1_range.second));
            auto v2 = p.create_integer_variable(Integer(v2_range.first), Integer(v2_range.second));
            auto v3 = p.create_integer_variable(Integer(v3_range.first), Integer(v3_range.second));
            auto vs = vector<IntegerVariableID>{v1, v2, v3};
            WeightedSum c;
            for (const auto & [idx, coeff] : enumerate(coeffs))
                c += Integer{coeff} * vs[idx];
            p.post(MiniLinearGreaterEqual{c, Integer{value}, refined});
            return solve(p, [](const CurrentState &) { return true; });
        };

        auto refined = run(true), coarse = run(false);
        println(cerr, "mini_linear laziness {} {} {} coeffs={} >= {}: recursions={} solutions={} propagations refined={} coarse={}",
            v1_range, v2_range, v3_range, coeffs, value, coarse.recursions, coarse.solutions, refined.propagations, coarse.propagations);
        if (refined.recursions != coarse.recursions || refined.solutions != coarse.solutions)
            throw UnexpectedException{"refined and coarse triggers diverged: different search tree or solution count"};
        if (refined.propagations > coarse.propagations)
            throw UnexpectedException{"refined triggers woke more often than coarse on_bounds"};
    }
}

auto main(int, char *[]) -> int
{
    // Hand-picked cases: a slack constraint, tight ones that force lower-bound
    // raises (and so watch firing + re-arming as the search drives bounds down),
    // and a trivially-true / trivially-false pair.
    run_mini_linear_ge_test({0, 4}, {0, 4}, {0, 4}, {1, 1, 1}, 6);
    run_mini_linear_ge_test({0, 5}, {0, 5}, {0, 5}, {1, 2, 3}, 12);
    run_mini_linear_ge_test({0, 6}, {0, 3}, {0, 3}, {100, 5, 2}, 350);
    run_mini_linear_ge_test({0, 3}, {0, 3}, {0, 3}, {2, 3, 5}, 0);
    run_mini_linear_ge_test({0, 2}, {0, 2}, {0, 2}, {1, 1, 1}, 7);
    run_mini_linear_ge_test({1, 4}, {2, 5}, {0, 6}, {3, 1, 4}, 20);

    measure_laziness({0, 6}, {0, 3}, {0, 3}, {100, 5, 2}, 350);
    measure_laziness({0, 5}, {0, 5}, {0, 5}, {1, 2, 3}, 12);
    measure_laziness({1, 4}, {2, 5}, {0, 6}, {3, 1, 4}, 20);

    random_device rand_dev;
    mt19937 rand(rand_dev());
    uniform_int_distribution coeff_dist(1, 8);
    uniform_int_distribution hi_dist(2, 7);
    uniform_int_distribution val_dist(0, 60);
    for (int x = 0; x < 200; ++x) {
        auto hi = [&]() { return pair{0, hi_dist(rand)}; };
        run_mini_linear_ge_test(hi(), hi(), hi(),
            {coeff_dist(rand), coeff_dist(rand), coeff_dist(rand)}, val_dist(rand));
    }

    return EXIT_SUCCESS;
}
