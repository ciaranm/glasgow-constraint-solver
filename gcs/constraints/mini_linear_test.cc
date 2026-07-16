/* Test vehicle for the refined per-literal trigger mechanism (issue #335, stages
 * B1 and B2). MiniLinearGreaterEqual is a deliberately small `sum c_i x_i >= K`
 * bounds-consistency propagator (all c_i > 0, all x_i >= 0). It runs in three
 * trigger modes with an identical propagation body, so they can be compared
 * directly: coarse on_bounds; a refined upper-bound watch on every variable,
 * re-armed on fire (B1); and the PB watched-set that keeps armed only enough
 * upper-bound watches to cover K + W, so variables outside the set are never
 * watched (B2).
 *
 * It exists only to exercise the refined-watch engine (the index, the fired-watch
 * inbox, consume-on-fire, re-arm, restore-on-backtrack, and is_watching); it is
 * not a public constraint and is expected to be retired once refined triggers fold
 * into the real Linear (stage E). Correctness is checked the way the real Linear
 * is: a brute-force solution oracle (catches over-pruning and any missed leaf
 * check), a raw solution-count check (catches duplicate solutions that a solution
 * SET would hide), and per-node bounds-consistency checking (catches under-pruning,
 * including a watch not restored after backtrack, since it runs at post-backtrack
 * nodes too). A laziness comparison asserts watched-set <= refined-all <= coarse
 * wakes, and strictly fewer on dominant instances.
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
#include <gcs/innards/s_expr.hh>
#include <gcs/innards/state.hh>
#include <gcs/problem.hh>
#include <gcs/search_heuristics.hh>
#include <gcs/solve.hh>
#include <gcs/stats.hh>

#include <util/enumerate.hh>

#include <algorithm>
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
using std::set;
using std::string;
using std::tuple;
using std::uniform_int_distribution;
using std::unique_ptr;
using std::vector;
using std::ranges::sort;

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
    public:
        // How the propagator is triggered; the propagation body is identical in all
        // three. Coarse = ordinary on_bounds triggers. RefinedAll = a refined upper-
        // bound watch on every variable, re-armed on fire (the B1 scheme; lazier than
        // coarse only by skipping lower-bound-change and self-retrigger wakes).
        // WatchedSet = the PB watched-set: keep armed only enough upper-bound watches
        // to cover K + W, so variables outside the set are never watched (B2).
        enum class Mode
        {
            Coarse,
            RefinedAll,
            WatchedSet
        };

    private:
        WeightedSum _coeff_vars;
        Integer _value;
        Mode _mode;

    public:
        explicit MiniLinearGreaterEqual(WeightedSum coeff_vars, Integer value, Mode mode = Mode::RefinedAll) :
            _coeff_vars(move(coeff_vars)), _value(value), _mode(mode)
        {
        }

        auto install(Propagators & propagators, State & initial_state, ProofModel * const) && -> void override
        {
            vector<pair<Integer, IntegerVariableID>> terms;
            for (const auto & [coeff, var] : _coeff_vars.terms)
                terms.emplace_back(coeff, var);

            // Coarse triggers on every variable's bounds. Both refined modes arm an
            // upper-bound watch (x_i < ub(x_i), entailed exactly when x_i's upper
            // bound drops) on every variable at install -- so scope and degree match
            // coarse (identical search tree), and WatchedSet then sheds the watches it
            // does not need. Payload = the variable's index into terms.
            Triggers triggers;
            if (_mode == Mode::Coarse)
                for (const auto & term : terms)
                    triggers.on_bounds.push_back(term.second);
            else
                for (const auto & [idx, term] : enumerate(terms))
                    triggers.refined.emplace_back(term.second < initial_state.upper_bound(term.second), static_cast<std::uint32_t>(idx));

            propagators.install(
                constraint_id(),
                [terms = move(terms), value = _value, mode = _mode](
                    const State & state, auto & inference, ProofLogger * const logger, const RefinedWatchContext & watches) -> PropagatorState {
                    Integer max_sum{0_i};
                    for (const auto & [coeff, var] : terms)
                        max_sum += coeff * state.upper_bound(var);

                    if (max_sum < value)
                        inference.contradiction(logger, JustifyUsingRUP{}, NoReason{});
                    else {
                        auto slack = max_sum - value;
                        for (const auto & [coeff, var] : terms) {
                            auto new_lower = state.upper_bound(var) - (slack / coeff);
                            if (new_lower > state.lower_bound(var))
                                inference.infer(logger, var >= new_lower, JustifyUsingRUP{}, NoReason{});
                        }

                        if (mode == Mode::RefinedAll) {
                            // A watch is consumed when it fires; re-arm each fired
                            // variable's upper-bound watch at its now-lower bound.
                            for (auto payload : watches.fired_payloads())
                                watches.watch(terms[payload].second < state.upper_bound(terms[payload].second), payload);
                        }
                        else if (mode == Mode::WatchedSet) {
                            // Keep enough upper-bound watches armed that the watched
                            // set alone covers K + W (W = max c_i*(ub_i - lb_i) on the
                            // post-prune bounds). Because max_sum >= the sum over the
                            // watched set, that certifies global dormancy and the
                            // unwatched variables need no watch. A fired variable not
                            // needed for coverage is simply not re-armed (it sheds).
                            Integer w{0_i};
                            for (const auto & [coeff, var] : terms) {
                                auto span = coeff * (state.upper_bound(var) - state.lower_bound(var));
                                if (span > w)
                                    w = span;
                            }
                            auto needed = value + w;
                            Integer covered{0_i};
                            for (const auto & [coeff, var] : terms)
                                if (watches.is_watching(var))
                                    covered += coeff * state.upper_bound(var);
                            if (covered < needed) {
                                vector<pair<Integer, std::uint32_t>> candidates;
                                for (const auto & [idx, term] : enumerate(terms))
                                    if (! watches.is_watching(term.second))
                                        candidates.emplace_back(term.first * state.upper_bound(term.second), static_cast<std::uint32_t>(idx));
                                sort(candidates, [](const auto & a, const auto & b) { return a.first > b.first; });
                                for (const auto & [contrib, idx] : candidates) {
                                    if (covered >= needed)
                                        break;
                                    watches.watch(terms[idx].second < state.upper_bound(terms[idx].second), idx);
                                    covered += contrib;
                                }
                            }
                        }
                    }
                    return PropagatorState::Enable;
                },
                triggers);
        }

        auto clone() const -> unique_ptr<Constraint> override
        {
            return make_unique<MiniLinearGreaterEqual>(_coeff_vars, _value, _mode);
        }

        auto s_expr(const ProofModel * const) const -> SExpr override
        {
            return SExpr::atom(constraint_type());
        }

        auto constraint_type() const -> string override
        {
            return "mini_linear_greater_equal";
        }
    };

    auto mode_name(MiniLinearGreaterEqual::Mode mode) -> const char *
    {
        switch (mode) {
            using enum MiniLinearGreaterEqual::Mode;
        case Coarse: return "coarse";
        case RefinedAll: return "refined-all";
        case WatchedSet: return "watched-set";
        }
        return "?";
    }

    // One `sum c_i x_i >= K` over three non-negative variables, propagated in the
    // given trigger mode: enumerate every solution and check it against the brute-
    // force oracle, with per-node bounds-consistency checking on every variable.
    auto run_mini_linear_ge_test(MiniLinearGreaterEqual::Mode mode, pair<int, int> v1_range, pair<int, int> v2_range, pair<int, int> v3_range,
        vector<int> coeffs, int value) -> void
    {
        print(cerr, "mini_linear ge [{}] {} {} {} coeffs={} >= {}:", mode_name(mode), v1_range, v2_range, v3_range, coeffs, value);
        cerr << flush;

        auto is_satisfying = [&](int a, int b, int c) { return coeffs[0] * a + coeffs[1] * b + coeffs[2] * c >= value; };

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
        p.post(MiniLinearGreaterEqual{c, Integer{value}, mode});

        solve_for_tests_checking_consistency(
            p, nullopt, expected, actual, tuple{pair{v1, CheckConsistency::BC}, pair{v2, CheckConsistency::BC}, pair{v3, CheckConsistency::BC}});

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
        pc.post(MiniLinearGreaterEqual{cc, Integer{value}, mode});
        auto stats = solve(pc, [](const CurrentState &) { return true; });
        if (stats.solutions != expected.size())
            throw UnexpectedException{"mini_linear produced the wrong number of solutions (duplicates or missing)"};
    }

    // Positive-laziness / same-tree check: solve the same instance in all three
    // trigger modes (identical propagation body). All must explore the same search
    // tree (equal recursions: same bounds-consistent fixpoint, same brancher) and
    // find the same solutions; and the watched-set must wake no more than
    // refined-all, which wakes no more than coarse. The printed counts show the
    // reduction; the mutation tests separately confirm each mechanism is load-bearing
    // rather than a silent fallback.
    auto measure_laziness(
        bool strict_watched_set_win, pair<int, int> v1_range, pair<int, int> v2_range, pair<int, int> v3_range, vector<int> coeffs, int value) -> void
    {
        using enum MiniLinearGreaterEqual::Mode;
        auto run = [&](MiniLinearGreaterEqual::Mode mode) -> Stats {
            Problem p;
            auto v1 = p.create_integer_variable(Integer(v1_range.first), Integer(v1_range.second));
            auto v2 = p.create_integer_variable(Integer(v2_range.first), Integer(v2_range.second));
            auto v3 = p.create_integer_variable(Integer(v3_range.first), Integer(v3_range.second));
            auto vs = vector<IntegerVariableID>{v1, v2, v3};
            WeightedSum c;
            for (const auto & [idx, coeff] : enumerate(coeffs))
                c += Integer{coeff} * vs[idx];
            p.post(MiniLinearGreaterEqual{c, Integer{value}, mode});
            // Bounds-splitting branching (x <= mid, then x > mid) drops upper bounds
            // gradually, so a shed variable's later drops no longer wake the watched-
            // set propagator -- which is where its advantage over refined-all shows
            // (instantiation branching drops each ub once, at the moment it sheds).
            return solve_with(p,
                SolveCallbacks{.solution = [](const CurrentState &) { return true; },
                    .branch = branch_with(variable_order::dom_then_deg(p), value_order::split_smallest_first())});
        };

        auto coarse = run(Coarse), refined_all = run(RefinedAll), watched = run(WatchedSet);
        println(cerr,
            "mini_linear laziness {} {} {} coeffs={} >= {}: recursions={} solutions={} propagations coarse={} refined-all={} watched-set={}",
            v1_range, v2_range, v3_range, coeffs, value, coarse.recursions, coarse.solutions, coarse.propagations, refined_all.propagations,
            watched.propagations);
        if (refined_all.recursions != coarse.recursions || watched.recursions != coarse.recursions || refined_all.solutions != coarse.solutions ||
            watched.solutions != coarse.solutions)
            throw UnexpectedException{"mini_linear trigger modes diverged: different search tree or solution count"};
        if (refined_all.propagations > coarse.propagations || watched.propagations > refined_all.propagations)
            throw UnexpectedException{"expected watched-set <= refined-all <= coarse propagations"};
        // On a strongly dominant instance the watched set is just the big variable,
        // so it must wake STRICTLY less than refined-all (which re-arms every
        // variable). This guards is_watching: if it stopped reporting armed watches,
        // the grow step would re-watch everything and the win would vanish.
        if (strict_watched_set_win && watched.propagations >= refined_all.propagations)
            throw UnexpectedException{"watched-set did not wake strictly less than refined-all on a dominant instance"};
    }
}

auto main(int argc, char * argv[]) -> int
{
    establish_and_announce_seed(argc, argv);

    using enum MiniLinearGreaterEqual::Mode;

    // Run the refined-all (B1) and watched-set (B2) modes through identical
    // correctness checks: hand-picked cases (a slack constraint, tight ones that
    // force lower-bound raises, a trivially-true and a trivially-false) plus random
    // instances. Coarse is exercised by the laziness comparison below.
    for (auto mode : {RefinedAll, WatchedSet}) {
        run_mini_linear_ge_test(mode, {0, 4}, {0, 4}, {0, 4}, {1, 1, 1}, 6);
        run_mini_linear_ge_test(mode, {0, 5}, {0, 5}, {0, 5}, {1, 2, 3}, 12);
        run_mini_linear_ge_test(mode, {0, 6}, {0, 3}, {0, 3}, {100, 5, 2}, 350);
        run_mini_linear_ge_test(mode, {0, 3}, {0, 3}, {0, 3}, {2, 3, 5}, 0);
        run_mini_linear_ge_test(mode, {0, 2}, {0, 2}, {0, 2}, {1, 1, 1}, 7);
        run_mini_linear_ge_test(mode, {1, 4}, {2, 5}, {0, 6}, {3, 1, 4}, 20);

        mt19937 rand(*get_seed());
        uniform_int_distribution coeff_dist(1, 8);
        uniform_int_distribution hi_dist(2, 7);
        uniform_int_distribution val_dist(0, 60);
        for (int x = 0; x < 200; ++x) {
            auto hi = [&]() { return pair{0, hi_dist(rand)}; };
            run_mini_linear_ge_test(mode, hi(), hi(), hi(), {coeff_dist(rand), coeff_dist(rand), coeff_dist(rand)}, val_dist(rand));
        }
    }

    measure_laziness(true, {0, 15}, {0, 15}, {0, 15}, {100, 1, 1}, 100);
    measure_laziness(true, {0, 6}, {0, 3}, {0, 3}, {100, 5, 2}, 350);
    measure_laziness(false, {0, 5}, {0, 5}, {0, 5}, {1, 2, 3}, 12);
    measure_laziness(false, {1, 4}, {2, 5}, {0, 6}, {3, 1, 4}, 20);

    return EXIT_SUCCESS;
}
