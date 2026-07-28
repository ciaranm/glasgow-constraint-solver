#include <gcs/constraints/difference.hh>
#include <gcs/constraints/innards/constraints_test_utils.hh>
#include <gcs/constraints/linear.hh>
#include <gcs/exception.hh>
#include <gcs/problem.hh>
#include <gcs/solve.hh>

#include <cstdlib>
#include <functional>
#include <iostream>
#include <memory>
#include <optional>
#include <random>
#include <set>
#include <string>
#include <tuple>
#include <utility>
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
using std::function;
using std::make_optional;
using std::make_shared;
using std::mt19937;
using std::nullopt;
using std::optional;
using std::pair;
using std::set;
using std::string;
using std::to_string;
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

using namespace gcs;
using namespace gcs::test_innards;

namespace
{
    // One end of an edge: either variable `var` offset by `offset` (a bare
    // variable when the offset is zero, a `+X + c` view otherwise), or, when
    // `var` is unset, the constant `offset`.
    struct Operand
    {
        optional<size_t> var;
        int offset;
    };

    auto v(size_t i) -> Operand
    {
        return Operand{i, 0};
    }

    auto v(size_t i, int offset) -> Operand
    {
        return Operand{i, offset};
    }

    auto c(int value) -> Operand
    {
        return Operand{nullopt, value};
    }

    // A half-reification condition, written as `vars[var] == value` so that the
    // condition variable is an ordinary member of the domain list and the
    // oracle's enumeration covers both of its settings.
    struct Cond
    {
        size_t var;
        int value;
    };

    auto b(size_t i, int value = 1) -> optional<Cond>
    {
        return Cond{i, value};
    }

    struct EdgeSpec
    {
        Operand x;
        Operand y;
        int d;
        optional<Cond> cond = nullopt;
    };

    auto operand_value(const Operand & o, const vector<int> & vals) -> int
    {
        return (o.var ? vals.at(*o.var) : 0) + o.offset;
    }

    auto operand_id(const Operand & o, const vector<IntegerVariableID> & vars) -> IntegerVariableID
    {
        if (! o.var)
            return constant_variable(Integer(o.offset));
        if (o.offset == 0)
            return vars.at(*o.var);
        return vars.at(*o.var) + Integer(o.offset);
    }

    auto make_vars(Problem & p, const vector<pair<int, int>> & domains) -> vector<IntegerVariableID>
    {
        vector<IntegerVariableID> vars;
        for (const auto & [lo, hi] : domains)
            vars.push_back(p.create_integer_variable(Integer(lo), Integer(hi)));
        return vars;
    }

    auto satisfied(const vector<int> & vals, const vector<EdgeSpec> & edges) -> bool
    {
        for (const auto & e : edges) {
            // A half-reified edge constrains nothing when its condition is
            // false. This is the whole semantics under test, and it is stated
            // here independently of the solver, so an over-pruning propagator
            // (one that let a false edge participate) loses solutions against
            // this oracle.
            if (e.cond && vals.at(e.cond->var) != e.cond->value)
                continue;
            if (operand_value(e.x, vals) - operand_value(e.y, vals) > e.d)
                return false;
        }
        return true;
    }

    auto condition_id(const optional<Cond> & c, const vector<IntegerVariableID> & vars) -> optional<IntegerVariableCondition>
    {
        if (! c)
            return nullopt;
        return vars.at(c->var) == Integer(c->value);
    }

    // Post the same system as one DifferenceConstraints, and separately as one
    // two-term LinearLessThanEqual per edge. Both are checked against an
    // independent C++ oracle, and against each other: a soundness failure in
    // the propagator shows up as a missing solution, over-pruning as an extra
    // one, and proof logging can catch neither of those (it only ever catches a
    // wrong inference). See the survey's section 5.2, item 11.
    //
    // The global model is then solved a second time with incrementality turned
    // off, and *both* the solution set and the recursion count have to come out
    // identical. That is not a smoke test: given the gate invariants the
    // incremental route reaches the same per-call fixpoint as the from-scratch
    // one, and a bounds fixpoint is the least fixpoint of monotone inflationary
    // operators, so it is unique --- which makes the search tree bit-identical.
    // `propagations` and the proof bytes may legitimately differ, because
    // Dijkstra settles in a different order from the predecessor forest, but a
    // `recursions` difference is a lost or gained inference and nothing else.
    // This is the sharpest check there is on the incremental machinery, because
    // every way it can go wrong loses propagation, and lost propagation is
    // invisible to VeriPB.
    auto run_test(bool proofs, const string & mode, const string & name, const vector<pair<int, int>> & domains, const vector<EdgeSpec> & edges)
        -> void
    {
        print(cerr, "difference {} {} domains={} edges={}{}", mode, name, domains, edges.size(), proofs ? " with proofs:" : ":");
        cerr << flush;

        set<tuple<vector<int>>> expected, actual, decomposed, from_scratch;
        build_expected(expected, [&](const vector<int> & vals) { return satisfied(vals, edges); }, domains);
        println(cerr, " expecting {} solutions", expected.size());

        // Whether either solve stopped early because a runtime cap fired (see
        // GCS_TEST_CAP_DEFAULTS). check_results copes with that on its own --- it
        // drops to checking soundness of what was produced --- but the
        // cross-check below cannot: two truncated runs stop after the same
        // *number* of solutions, not the same *set*, because the two models
        // search in different orders. Comparing them then reports a disagreement
        // where there is none, which is a defect of this harness rather than of
        // the propagator, and it is what CI found on the reified random mode
        // (whose extra condition variables multiply the solution count).
        bool truncated = false;
        unsigned long long incremental_recursions = 0, from_scratch_recursions = 0;

        {
            Problem p;
            auto vars = make_vars(p, domains);
            vector<DifferenceEdge> posted;
            for (const auto & e : edges)
                posted.push_back(DifferenceEdge{operand_id(e.x, vars), operand_id(e.y, vars), Integer(e.d), condition_id(e.cond, vars)});
            // The differential fixpoint audit is on for every fixture in this
            // file: after each incremental call the from-scratch pass is re-run
            // on the same starting bounds and the same active edge set, and the
            // two have to agree node for node. That catches a completeness
            // failure at the wake where it happens rather than as a missing
            // solution a long way downstream, or not at all.
            p.post(DifferenceConstraints{posted}.auditing_incremental_propagation());

            auto proof_name = proofs ? make_optional("difference_test_" + mode + "_" + name) : nullopt;
            // Bounds consistent, not GAC: the propagator only reads and writes
            // bounds, and gcs domains can have holes where the paper's Theorem
            // 2 assumes ranges.
            solve_for_tests(p, proof_name, actual, tuple{vars});
            truncated = truncated || last_run_truncated();
            incremental_recursions = last_run_recursions();
            check_results(proof_name, expected, actual);
        }

        {
            Problem p;
            auto vars = make_vars(p, domains);
            vector<DifferenceEdge> posted;
            for (const auto & e : edges)
                posted.push_back(DifferenceEdge{operand_id(e.x, vars), operand_id(e.y, vars), Integer(e.d), condition_id(e.cond, vars)});
            p.post(DifferenceConstraints{posted}.incrementally(false));

            solve_for_tests(p, nullopt, from_scratch, tuple{vars});
            truncated = truncated || last_run_truncated();
            from_scratch_recursions = last_run_recursions();
        }

        {
            Problem p;
            auto vars = make_vars(p, domains);
            for (const auto & e : edges) {
                auto sum = WeightedSum{} + 1_i * operand_id(e.x, vars) + -1_i * operand_id(e.y, vars);
                if (auto cond = condition_id(e.cond, vars))
                    p.post(LinearLessThanEqualIf{sum, Integer(e.d), *cond});
                else
                    p.post(LinearLessThanEqual{sum, Integer(e.d)});
            }
            solve_for_tests(p, nullopt, decomposed, tuple{vars});
            truncated = truncated || last_run_truncated();
        }

        if (truncated) {
            println(cerr, "difference {} {}: a cap fired, so the global/decomposed cross-check is skipped", mode, name);
            return;
        }

        if (actual != decomposed) {
            println(cerr, "difference {} {}: global and decomposed models disagree", mode, name);
            println(cerr, "global has {} solutions, decomposed has {}", actual.size(), decomposed.size());
            throw UnexpectedException{"difference global and decomposed models disagree"};
        }

        if (actual != from_scratch) {
            println(cerr, "difference {} {}: incremental and from-scratch propagation disagree", mode, name);
            println(cerr, "incremental has {} solutions, from-scratch has {}", actual.size(), from_scratch.size());
            throw UnexpectedException{"difference incremental and from-scratch propagation disagree"};
        }

        if (incremental_recursions != from_scratch_recursions)
            throw UnexpectedException{"difference " + mode + " " + name + ": incremental propagation took " + to_string(incremental_recursions) +
                " recursions against the from-scratch pass's " + to_string(from_scratch_recursions) +
                ". The two reach the identical per-call fixpoint --- a bounds closure is the least fixpoint of monotone inflationary operators and "
                "is "
                "therefore unique --- so the search tree cannot legitimately differ. This is a lost or gained inference in the incremental route, "
                "and "
                "it is invisible to proof logging. Fix gcs/constraints/difference/difference_incremental.cc or the gate handling in "
                "difference_graph.cc; do NOT relax this check."};
    }

    // The transitive push: two edges whose combined bound is strictly stronger
    // than either edge on its own. x - y <= -3 gives y >= x + 3, y - z <= -4
    // gives z >= y + 4, so the system entails z >= x + 7 -- a bound no single
    // edge implies. Solve as far as the first complete propagation and read the
    // bounds off, so this asserts the propagator actually fires rather than
    // merely that the solution set is right.
    auto run_transitive_test(bool incremental) -> void
    {
        print(cerr, "difference transitive push (incremental={}):", incremental);
        cerr << flush;

        Problem p;
        auto x = p.create_integer_variable(0_i, 10_i, "x");
        auto y = p.create_integer_variable(0_i, 10_i, "y");
        auto z = p.create_integer_variable(0_i, 10_i, "z");
        p.post(DifferenceConstraints{{DifferenceEdge{x, y, -3_i}, DifferenceEdge{y, z, -4_i}}}
                .incrementally(incremental)
                .auditing_incremental_propagation());

        optional<Integer> z_lower, x_upper;
        solve_with(p, SolveCallbacks{.trace = [&](const CurrentState & s) -> bool {
            z_lower = s.lower_bound(z);
            x_upper = s.upper_bound(x);
            return false;
        }});

        println(cerr, " z >= {}, x <= {}", z_lower ? z_lower->raw_value : -1, x_upper ? x_upper->raw_value : -1);
        if (z_lower != make_optional(7_i))
            throw UnexpectedException{"difference did not push z's lower bound transitively to 7"};
        if (x_upper != make_optional(3_i))
            throw UnexpectedException{"difference did not push x's upper bound transitively to 3"};
    }

    // The hole snap, which is why this propagator returns PropagatorState::Enable
    // rather than EnableButIdempotent. One Bellman-Ford pass each way reaches the
    // fixpoint of the *bounds abstraction*, but an inferred bound can land
    // strictly above the value the pass computed, because the state snaps it past
    // a hole in the domain -- and that higher bound seeds the next call, which
    // then pushes further. So a second call genuinely infers more, and the
    // propagator must be re-woken by its own inferences.
    //
    // y has the hole {3, 4, 5}. First call: lb(y) >= lb(x) + 3 = 3, which snaps
    // to 6; lb(z) >= lb(y) + 2, but the *pass* computed lb(y) = 3, so it only
    // pushes z to 5. Second call, seeded from the snapped lb(y) = 6: z >= 8.
    // Nothing else is in the model, so if the propagator claimed idempotence the
    // engine would not re-wake it from its own inferences and z would be left at
    // 5. Confirmed by mutation: switching the return to EnableButIdempotent makes
    // this fail (and also trips the harness's GCS_CHECK_IDEMPOTENT_CLAIMS re-run).
    auto run_hole_snap_test(bool incremental) -> void
    {
        print(cerr, "difference hole snap (incremental={}):", incremental);
        cerr << flush;

        Problem p;
        auto x = p.create_integer_variable(0_i, 10_i, "x");
        auto y = p.create_integer_variable(vector<Integer>{0_i, 1_i, 2_i, 6_i, 7_i, 8_i, 9_i, 10_i}, "y");
        auto z = p.create_integer_variable(0_i, 10_i, "z");
        p.post(DifferenceConstraints{{DifferenceEdge{x, y, -3_i}, DifferenceEdge{y, z, -2_i}}}
                .incrementally(incremental)
                .auditing_incremental_propagation());

        optional<Integer> y_lower, z_lower;
        solve_with(p, SolveCallbacks{.trace = [&](const CurrentState & s) -> bool {
            y_lower = s.lower_bound(y);
            z_lower = s.lower_bound(z);
            return false;
        }});

        println(cerr, " y >= {}, z >= {}", y_lower ? y_lower->raw_value : -1, z_lower ? z_lower->raw_value : -1);
        if (y_lower != make_optional(6_i))
            throw UnexpectedException{"difference did not snap y's lower bound past the hole to 6"};
        if (z_lower != make_optional(8_i))
            throw UnexpectedException{"difference stopped at the first pass's lower bound for z instead of re-running from the snapped bound: "
                                      "the propagator must not claim idempotence"};
    }

    // The transitive push again, but across half-reified edges, plus the
    // negative control that is the bug this feature most plausibly introduces:
    // a propagator that ignored an edge's condition, or that tested it wrongly,
    // would prune from an edge that is not in force. Solution counting alone
    // would catch that only in the fixtures where the false edge actually
    // excludes something, so assert the bounds directly.
    //
    //   b1 is fixed TRUE, and its edges must fire: x - y <= -3, y - z <= -4
    //   give z >= 7 and x <= 3, exactly as in the unconditional case.
    //   b2 is fixed FALSE, and its edge (w - z <= -20, impossible over these
    //   domains) must not fire at all: w keeps its full 0..10 range.
    //
    // Confirmed by mutation: dropping the DefinitelyTrue test in the
    // active-edge snapshot empties w's domain and this fails immediately.
    auto run_reified_bounds_test(bool incremental) -> void
    {
        print(cerr, "difference reified push and negative control (incremental={}):", incremental);
        cerr << flush;

        Problem p;
        auto x = p.create_integer_variable(0_i, 10_i, "x");
        auto y = p.create_integer_variable(0_i, 10_i, "y");
        auto z = p.create_integer_variable(0_i, 10_i, "z");
        auto w = p.create_integer_variable(0_i, 10_i, "w");
        auto b1 = p.create_integer_variable(1_i, 1_i, "b1");
        auto b2 = p.create_integer_variable(0_i, 0_i, "b2");
        p.post(DifferenceConstraints{
            {DifferenceEdge{x, y, -3_i, b1 == 1_i}, DifferenceEdge{y, z, -4_i, b1 == 1_i}, DifferenceEdge{w, z, -20_i, b2 == 1_i}}}
                .incrementally(incremental)
                .auditing_incremental_propagation());

        optional<Integer> z_lower, x_upper, w_lower, w_upper;
        solve_with(p, SolveCallbacks{.trace = [&](const CurrentState & s) -> bool {
            z_lower = s.lower_bound(z);
            x_upper = s.upper_bound(x);
            w_lower = s.lower_bound(w);
            w_upper = s.upper_bound(w);
            return false;
        }});

        println(cerr, " z >= {}, x <= {}, w in {}..{}", z_lower ? z_lower->raw_value : -1, x_upper ? x_upper->raw_value : -1,
            w_lower ? w_lower->raw_value : -1, w_upper ? w_upper->raw_value : -1);
        if (z_lower != make_optional(7_i) || x_upper != make_optional(3_i))
            throw UnexpectedException{"difference did not push transitively across half-reified edges whose condition is true"};
        if (w_lower != make_optional(0_i) || w_upper != make_optional(10_i))
            throw UnexpectedException{"difference propagated a half-reified edge whose condition is false: the edge must not participate in the "
                                      "graph at all while its literal is not currently true"};
    }

    // A half-reified edge that canonicalises to `cond -> 0 <= d` with d < 0 is
    // a fact about the condition, and one that has to be stated: quietly
    // dropping it would let cond hold with the constraint violated, which is
    // unsound rather than merely incomplete. Unconditionally the same edge is a
    // root contradiction instead, which is why the two live in different places.
    auto run_reified_degenerate_test(bool incremental) -> void
    {
        print(cerr, "difference reified degenerate edge (incremental={}):", incremental);
        cerr << flush;

        Problem p;
        auto x = p.create_integer_variable(0_i, 5_i, "x");
        auto bad = p.create_integer_variable(0_i, 1_i, "bad");
        auto fine = p.create_integer_variable(0_i, 1_i, "fine");
        // bad -> x - x <= -1, i.e. !bad. fine -> x - x <= 0, i.e. nothing.
        p.post(DifferenceConstraints{{DifferenceEdge{x, x, -1_i, bad == 1_i}, DifferenceEdge{x, x, 0_i, fine == 1_i}}}
                .incrementally(incremental)
                .auditing_incremental_propagation());

        optional<Integer> bad_upper, fine_upper;
        solve_with(p, SolveCallbacks{.trace = [&](const CurrentState & s) -> bool {
            bad_upper = s.upper_bound(bad);
            fine_upper = s.upper_bound(fine);
            return false;
        }});

        println(cerr, " bad <= {}, fine <= {}", bad_upper ? bad_upper->raw_value : -1, fine_upper ? fine_upper->raw_value : -1);
        if (bad_upper != make_optional(0_i))
            throw UnexpectedException{"difference did not refute the condition of a half-reified edge saying cond -> 0 <= -1"};
        if (fine_upper != make_optional(1_i))
            throw UnexpectedException{"difference refuted the condition of a vacuous half-reified edge saying cond -> 0 <= 0"};
    }

    // A negated view operand is not a difference constraint at all, and
    // accepting one would be unsound rather than merely incomplete, so it is
    // rejected at construction.
    auto run_negated_view_test() -> void
    {
        print(cerr, "difference negated view rejection:");
        cerr << flush;

        Problem p;
        auto x = p.create_integer_variable(0_i, 5_i, "x");
        auto y = p.create_integer_variable(0_i, 5_i, "y");

        for (auto [lhs, rhs] : vector<pair<IntegerVariableID, IntegerVariableID>>{{-x, y}, {x, -y}, {-x + 2_i, y}}) {
            bool threw = false;
            try {
                DifferenceConstraints rejected{{DifferenceEdge{lhs, rhs, 0_i}}};
                static_cast<void>(rejected);
            }
            catch (const InvalidProblemDefinitionException &) {
                threw = true;
            }
            if (! threw)
                throw UnexpectedException{"difference accepted a negated view operand"};
        }

        println(cerr, " ok");
    }

    // What a fixture expects the root simplification stage to have done. Only
    // the fields that are set are checked, because a fixture usually pins one
    // sub-step and would otherwise have to restate every other count.
    //
    // These assertions are the whole reason the counters exist. Redundant-edge
    // removal, node removal and zero-cycle detection are all invisible from
    // outside: they change no solution, no proof and no search tree. A stage
    // that quietly did nothing at all would pass the solution-equivalence check,
    // the recursion check, the OPB byte-diff and VeriPB. So "the counters say it
    // fired" is the only thing standing between a working stage and a shipped
    // no-op, and a failure here means the *stage* is broken, not that the
    // expectation has gone stale.
    struct SimplifyExpectation
    {
        optional<bool> ran = nullopt;
        optional<size_t> rounds_at_least = nullopt;
        optional<size_t> redundant_edges_removed = nullopt;
        optional<size_t> conditions_fixed = nullopt;
        optional<size_t> isolated_nodes_removed = nullopt;
        optional<size_t> zero_weight_cycles = nullopt;
        optional<size_t> nodes_on_zero_weight_cycles = nullopt;
        optional<bool> base_negative_cycle = nullopt;
        // Simplification is never allowed to make the search bigger. Set this
        // when a fixture is one where fixing a condition should make it strictly
        // smaller.
        bool expect_fewer_recursions = false;
    };

    auto check_count(const string & name, const string & what, const optional<size_t> & expected, size_t actual) -> void
    {
        if (expected && *expected != actual)
            throw UnexpectedException{"difference simplify " + name + ": the root simplification stage reported " + to_string(actual) + " " + what +
                ", expected " + to_string(*expected) +
                ". This is an assertion about the stage, not about the fixture: it fires when the stage stops doing its job, and a stage that "
                "silently does nothing passes every other check in this file. Fix gcs/constraints/difference/difference_simplify.cc."};
    }

    // Solve the same system twice, once with the root simplification stage on
    // and once with it off, and insist that the only thing that changed is how
    // much searching it took.
    //
    // Redundant-edge removal, node removal and zero-cycle detection are
    // propagation-neutral by construction, so on a fixture where no condition is
    // fixed the recursion counts must be *equal*: a difference means an edge was
    // dropped that was carrying propagation. Fixing a condition is strictly
    // stronger, so on those fixtures the count may fall, and the fixture says so
    // rather than the check quietly allowing it either way.
    auto run_simplify_test(bool proofs, const string & name, const vector<pair<int, int>> & domains, const vector<EdgeSpec> & edges,
        const SimplifyExpectation & expected) -> void
    {
        print(cerr, "difference simplify {} domains={} edges={}{}", name, domains, edges.size(), proofs ? " with proofs:" : ":");
        cerr << flush;

        set<tuple<vector<int>>> oracle, with, without;
        build_expected(oracle, [&](const vector<int> & vals) { return satisfied(vals, edges); }, domains);

        // Deliberately not solve_for_tests_with_callbacks: that wrapper applies
        // the GCS_TEST_MAX_SOLUTIONS / GCS_TEST_MAX_RECURSIONS caps, and a run
        // those truncate says nothing about completeness *and* reports a
        // recursion count that is the cap rather than the search. Every fixture
        // here is a handful of variables over a handful of values, so full
        // enumeration is cheap and unconditional. \sa INCREMENTALITY-INVARIANTS
        auto stats = make_shared<DifferenceSimplificationStats>();
        auto solve_one = [&](bool simplify, set<tuple<vector<int>>> & into, const optional<string> & proof_name) -> unsigned long long {
            Problem p;
            auto vars = make_vars(p, domains);
            vector<DifferenceEdge> posted;
            for (const auto & e : edges)
                posted.push_back(DifferenceEdge{operand_id(e.x, vars), operand_id(e.y, vars), Integer(e.d), condition_id(e.cond, vars)});
            p.post(DifferenceConstraints{posted}.simplifying_at_root(simplify).reporting_simplification_to(simplify ? stats : nullptr));

            // The same branching heuristic, from the same seed, in both runs, so
            // that a difference in the recursion count is a difference in
            // propagation and cannot be a difference in search order.
            auto result = solve_with(p,
                SolveCallbacks{.solution = [&](const CurrentState & s) -> bool {
                                   into.emplace(extract_from_state(s, vars));
                                   return true;
                               },
                    .branch = random_branch_with_optional_seed(p)},
                proof_name ? make_optional<ProofOptions>(ProofFileNames{*proof_name}) : nullopt);
            return result.recursions;
        };

        auto with_recursions = solve_one(true, with, proofs ? make_optional("difference_simplify_" + name) : nullopt);
        auto without_recursions = solve_one(false, without, nullopt);

        println(cerr, " {} solutions, recursions {} -> {}, ran={} rounds={} redundant={} fixed={} isolated={} zerocycles={}/{} negcycle={} {:.6f}s",
            oracle.size(), without_recursions, with_recursions, stats->ran, stats->rounds, stats->redundant_edges_removed, stats->conditions_fixed,
            stats->isolated_nodes_removed, stats->zero_weight_cycles, stats->nodes_on_zero_weight_cycles, stats->base_negative_cycle, stats->seconds);

        if (proofs)
            verify_proof_and_clean_up("difference_simplify_" + name);

        if (with != oracle)
            throw UnexpectedException{"difference simplify " + name + ": simplification on disagrees with the oracle, " + to_string(with.size()) +
                " solutions against " + to_string(oracle.size())};
        if (without != oracle)
            throw UnexpectedException{"difference simplify " + name + ": simplification off disagrees with the oracle, " + to_string(without.size()) +
                " solutions against " + to_string(oracle.size())};

        if (expected.ran && *expected.ran != stats->ran)
            throw UnexpectedException{"difference simplify " + name + ": the root simplification stage " + (stats->ran ? "ran" : "did not run") +
                ", and it was supposed to " + (*expected.ran ? "" : "not ") + "run"};
        if (expected.rounds_at_least && stats->rounds < *expected.rounds_at_least)
            throw UnexpectedException{"difference simplify " + name + ": the root simplification stage took " + to_string(stats->rounds) +
                " rounds, expected at least " + to_string(*expected.rounds_at_least) +
                ". Fewer rounds than that means it stopped before its fixpoint, so fixing a condition is no longer re-activating the edges that "
                "fixing it makes definitely true."};
        check_count(name, "redundant edges removed", expected.redundant_edges_removed, stats->redundant_edges_removed);
        check_count(name, "conditions fixed", expected.conditions_fixed, stats->conditions_fixed);
        check_count(name, "isolated nodes removed", expected.isolated_nodes_removed, stats->isolated_nodes_removed);
        check_count(name, "zero weight cycles", expected.zero_weight_cycles, stats->zero_weight_cycles);
        check_count(name, "nodes on zero weight cycles", expected.nodes_on_zero_weight_cycles, stats->nodes_on_zero_weight_cycles);
        if (expected.base_negative_cycle && *expected.base_negative_cycle != stats->base_negative_cycle)
            throw UnexpectedException{"difference simplify " + name + ": base_negative_cycle was " + to_string(stats->base_negative_cycle) +
                ", expected " + to_string(*expected.base_negative_cycle)};

        if (expected.expect_fewer_recursions) {
            if (with_recursions >= without_recursions)
                throw UnexpectedException{"difference simplify " + name + ": simplification took " + to_string(with_recursions) +
                    " recursions against " + to_string(without_recursions) +
                    " without it, but this fixture is one where fixing a condition at the root is supposed to remove search"};
        }
        else if (with_recursions != without_recursions)
            throw UnexpectedException{"difference simplify " + name + ": simplification changed the search from " + to_string(without_recursions) +
                " recursions to " + to_string(with_recursions) +
                ". Redundant-edge removal, node removal and zero-cycle detection are propagation-neutral by construction, so a fixture that fixes "
                "no condition must search identically. An edge that was carrying propagation has been dropped."};
    }

    auto run_simplify_tests(bool proofs) -> void
    {
        // Redundant edges. The direct edge is implied by the two-step path, so
        // it stops being propagated; the model keeps it, and nothing else moves.
        run_simplify_test(proofs, "redundant_direct", {{0, 5}, {0, 5}, {0, 5}}, {{v(0), v(1), -1}, {v(1), v(2), -1}, {v(0), v(2), 0}},
            SimplifyExpectation{.ran = true, .redundant_edges_removed = 1});

        // Parallel edges: the weaker one is strictly implied, and of the two
        // that attain the distance exactly one is kept --- dropping both would
        // change the distance, which is why the tie is handled separately.
        run_simplify_test(proofs, "redundant_parallel", {{0, 6}, {0, 6}}, {{v(0), v(1), 1}, {v(0), v(1), -2}, {v(0), v(1), -2}, {v(0), v(1), 3}},
            SimplifyExpectation{.ran = true, .redundant_edges_removed = 3});

        // A node that is only ever a static bound has no arcs at all, so it
        // drops out of the relaxation loop and out of the round bound.
        run_simplify_test(proofs, "isolated_node", {{0, 8}, {0, 8}, {0, 8}}, {{v(0), c(4), 3}, {v(1), v(2), -1}},
            SimplifyExpectation{.ran = true, .isolated_nodes_removed = 1});

        // A zero-weight cycle, which is what the unimplemented fourth sub-step
        // would unify. Counted, so that "would it ever fire?" is a measurement.
        run_simplify_test(proofs, "zero_cycle", {{0, 5}, {0, 5}}, {{v(0), v(1), -2}, {v(1), v(0), 2}},
            SimplifyExpectation{.ran = true, .zero_weight_cycles = 1, .nodes_on_zero_weight_cycles = 2});
        run_simplify_test(proofs, "zero_cycle_three", {{0, 5}, {0, 5}, {0, 5}}, {{v(0), v(1), 0}, {v(1), v(2), 0}, {v(2), v(0), 0}},
            SimplifyExpectation{.ran = true, .zero_weight_cycles = 1, .nodes_on_zero_weight_cycles = 3});
        run_simplify_test(proofs, "no_zero_cycle", {{0, 5}, {0, 5}, {0, 5}}, {{v(0), v(1), -1}, {v(1), v(2), -1}},
            SimplifyExpectation{.ran = true, .zero_weight_cycles = 0, .nodes_on_zero_weight_cycles = 0});

        // The deliverable. `b -> x - y <= -5` together with the unconditional
        // `y - x <= 2` closes a cycle of weight -3, so b cannot hold, and saying
        // so at the root removes the branch that would have discovered it.
        run_simplify_test(proofs, "fix_one", {{0, 10}, {0, 10}, {0, 1}}, {{v(1), v(0), 2}, {v(0), v(1), -5, b(2)}},
            SimplifyExpectation{.ran = true, .conditions_fixed = 1, .expect_fewer_recursions = true});

        // The same, through a two-edge witness path, so the pol has three
        // addends and the path is recovered from the shortest-path tree rather
        // than being a single edge.
        run_simplify_test(proofs, "fix_via_path", {{0, 10}, {0, 10}, {0, 10}, {0, 1}}, {{v(1), v(2), 1}, {v(2), v(0), 1}, {v(0), v(1), -5, b(3)}},
            SimplifyExpectation{.ran = true, .conditions_fixed = 1, .expect_fewer_recursions = true});

        // A conditional edge that does *not* close a cycle must be left alone.
        // The negative control: a stage that fixed conditions too eagerly would
        // lose solutions, and the oracle comparison above is what catches it.
        run_simplify_test(proofs, "fix_none", {{0, 10}, {0, 10}, {0, 1}}, {{v(1), v(0), 5}, {v(0), v(1), -2, b(2)}},
            SimplifyExpectation{.ran = true, .conditions_fixed = 0});

        // The boundary: the cycle weighs exactly zero, so the condition is
        // perfectly satisfiable and must not be touched. Changing the test from
        // `< 0` to `<= 0` fixes b here and loses every solution with b true,
        // which the oracle comparison catches immediately (confirmed by
        // mutation).
        run_simplify_test(proofs, "fix_boundary_zero", {{0, 10}, {0, 10}, {0, 1}}, {{v(1), v(0), 5}, {v(0), v(1), -5, b(2)}},
            SimplifyExpectation{.ran = true, .conditions_fixed = 0});

        // Both polarities of one Boolean, which is what a disjunctive resource
        // contributes. Only the one that closes a cycle is fixed.
        run_simplify_test(proofs, "fix_one_polarity", {{0, 10}, {0, 10}, {0, 1}},
            {{v(1), v(0), 2}, {v(0), v(1), -5, b(2)}, {v(1), v(0), -1, b(2, 0)}},
            SimplifyExpectation{.ran = true, .conditions_fixed = 1, .expect_fewer_recursions = true});

        // Two independent Booleans, both fixable, in one round.
        run_simplify_test(proofs, "fix_two", {{0, 10}, {0, 10}, {0, 10}, {0, 1}, {0, 1}},
            {{v(1), v(0), 2}, {v(0), v(1), -5, b(3)}, {v(2), v(0), 1}, {v(0), v(2), -4, b(4)}},
            SimplifyExpectation{.ran = true, .conditions_fixed = 2, .expect_fewer_recursions = true});

        // The cascade, which is why the stage iterates rather than running once.
        // b1's true edge closes a cycle against `y - x <= 1`, so b1 is false ---
        // which makes b1's *false* edge `y - z <= -3` definitely active, and only
        // then is there any path from x to z at all, which is what makes b2's
        // edge close a cycle in its turn. Round one cannot see the second fix,
        // because in round one z has no incoming edge.
        //
        // Confirmed by mutation: replacing the fixpoint loop with a single round
        // leaves b2 unfixed and this fails on the count.
        run_simplify_test(proofs, "fix_cascade", {{0, 10}, {0, 10}, {0, 10}, {0, 1}, {0, 1}},
            {{v(1), v(0), 1}, {v(0), v(1), 2}, {v(0), v(1), -5, b(3)}, {v(1), v(2), -3, b(3, 0)}, {v(2), v(0), -1, b(4)}},
            SimplifyExpectation{.ran = true, .rounds_at_least = 3, .conditions_fixed = 2, .expect_fewer_recursions = true});
    }

    // The paper's RCPSP/max headline, in miniature: two unit-capacity tasks
    // whose maximum time lags are tight enough that neither can precede the
    // other. Every setting of the ordering Boolean closes a negative cycle, so
    // the model is infeasible --- but at the root no Boolean is fixed and so no
    // conditional edge is in the graph, which is exactly why #590 measured that
    // the propagator alone cannot see it and #587 before it.
    //
    // The simplification stage can, and the way it does is worth stating because
    // it is simpler than expected. Both polarities of the ordering Boolean are
    // separately impossible, so both are found fixable in the *same* round: the
    // first is inferred, the second contradicts it, and the model is refuted
    // before search starts. So the counters read one condition fixed in one
    // round --- the second fix is the contradiction, and never gets counted,
    // which is also why the counters are published by a destructor rather than
    // at the end of the stage.
    auto run_root_refutation_test() -> void
    {
        print(cerr, "difference root refutation:");
        cerr << flush;

        auto solve_one = [&](bool simplify, DifferenceSimplificationStats & into) -> pair<unsigned long long, unsigned long long> {
            Problem p;
            auto s_i = p.create_integer_variable(0_i, 20_i, "s_i");
            auto s_j = p.create_integer_variable(0_i, 20_i, "s_j");
            auto before = p.create_integer_variable(0_i, 1_i, "before");
            auto stats = make_shared<DifferenceSimplificationStats>();
            p.post(DifferenceConstraints{{// maximum time lags, in both directions: the two starts are within 2 of each other
                                             DifferenceEdge{s_j, s_i, 2_i}, DifferenceEdge{s_i, s_j, 2_i},
                                             // the unary resource, as a disjunction over durations of 4
                                             DifferenceEdge{s_i, s_j, -4_i, before == 1_i}, DifferenceEdge{s_j, s_i, -4_i, before == 0_i}}}
                    .simplifying_at_root(simplify)
                    .reporting_simplification_to(stats));

            auto result = solve_with(p, SolveCallbacks{.branch = random_branch_with_optional_seed(p)});
            into = *stats;
            return {result.recursions, result.solutions};
        };

        DifferenceSimplificationStats on, off;
        auto [on_recursions, on_solutions] = solve_one(true, on);
        auto [off_recursions, off_solutions] = solve_one(false, off);

        println(cerr, " recursions {} -> {}, solutions {}/{}, fixed={} rounds={} negcycle={}", off_recursions, on_recursions, off_solutions,
            on_solutions, on.conditions_fixed, on.rounds, on.base_negative_cycle);

        if (0 != on_solutions || 0 != off_solutions)
            throw UnexpectedException{"difference root refutation: the fixture is supposed to be unsatisfiable"};
        if (! on.ran)
            throw UnexpectedException{"difference root refutation: the simplification stage did not run at all"};
        if (1 != on.conditions_fixed)
            throw UnexpectedException{"difference root refutation: the simplification stage recorded " + to_string(on.conditions_fixed) +
                " conditions fixed, expected exactly 1: both polarities of the ordering Boolean close a cycle against the maximum time lag, the "
                "first is inferred and the second is the contradiction, which unwinds before it can be counted"};
        if (1 != on_recursions)
            throw UnexpectedException{"difference root refutation: with simplification the model must be refuted at the root, in " +
                to_string(on_recursions) + " recursions rather than 1"};
        if (off_recursions <= on_recursions)
            throw UnexpectedException{"difference root refutation: without simplification the solver is supposed to have to search, and it took " +
                to_string(off_recursions) + " recursions"};
    }

    // The incremental machinery's failure mode is always the same: an inference
    // that should have been made is not, because a gate said there was nothing
    // to do. Every one of those failures is invisible to proof logging, and most
    // are invisible to a solution count too, because a lost bound push usually
    // only makes the solver search harder. So these fixtures assert an
    // *invariant at every search node*: the propagator's own consequence has to
    // hold at every fully-propagated state the search visits, not merely at the
    // leaves. That is a direct test of the gate, and it fails at the node where
    // the gate first went wrong.
    //
    // The branching is fixed and deterministic in each, so the scenario really
    // is the one described rather than whatever a random order happened to
    // produce, and every one of them runs both incrementally and from scratch.
    struct NodeInvariant
    {
        string what;
        function<auto(const CurrentState &)->bool> holds;
    };

    auto run_node_invariant_test(const string & name, bool incremental, Problem & p, const vector<IntegerVariableID> & branch_vars,
        const vector<NodeInvariant> & invariants, unsigned long long expected_solutions) -> void
    {
        print(cerr, "difference {} (incremental={}):", name, incremental);
        cerr << flush;

        optional<string> failure;
        unsigned long long nodes = 0;
        auto result = solve_with(p,
            SolveCallbacks{.trace = [&](const CurrentState & s) -> bool {
                               ++nodes;
                               for (const auto & i : invariants)
                                   if (! i.holds(s)) {
                                       failure = i.what;
                                       return false;
                                   }
                               return true;
                           },
                .branch = branch_with(variable_order::in_order(branch_vars), value_order::largest_first())});

        println(cerr, " {} nodes, {} solutions", nodes, result.solutions);

        if (failure)
            throw UnexpectedException{"difference " + name + " (incremental=" + (incremental ? "yes" : "no") +
                "): a consequence of the difference system does not hold at a search node the solver visited: " + *failure +
                ". A bound the system entails was never pushed, which is a lost inference and is invisible to proof logging. Fix "
                "gcs/constraints/difference/difference_incremental.cc or the gate handling in difference_graph.cc."};
        if (result.solutions != expected_solutions)
            throw UnexpectedException{"difference " + name + " (incremental=" + (incremental ? "yes" : "no") + "): found " +
                to_string(result.solutions) + " solutions, expected " + to_string(expected_solutions)};
    }

    // (a) The stale-Do scenario, verbatim. `sel` is branched first and
    // largest-value-first, so the search sets `y >= 10`, propagates (recording
    // Do(y) = 10), fails against `z <= 12`, backtracks to `y >= 5`, and only
    // then does the sibling set `y >= 7`.
    //
    // A `Do` array clamped lazily against the current bounds at the next call,
    // rather than restored exactly, would compute Do(y) = min(10, 7) = 7, which
    // is min D(y), leave `y` out of `Vl`, and never push `z >= 10`: the
    // consequences of `y >= 7` were computed in a branch that no longer exists.
    // Successive guesses tightening the same variable is the commonest
    // branching pattern there is, so this is not an exotic case.
    auto run_stale_do_test(bool incremental) -> void
    {
        Problem p;
        auto sel = p.create_integer_variable(0_i, 1_i, "sel");
        auto y = p.create_integer_variable(5_i, 20_i, "y");
        auto z = p.create_integer_variable(0_i, 12_i, "z");
        p.post(DifferenceConstraints{{DifferenceEdge{y, z, -3_i}}}.incrementally(incremental).auditing_incremental_propagation());
        p.post(LinearGreaterThanEqualIf{WeightedSum{} + 1_i * y, 10_i, sel == 1_i});
        p.post(LinearGreaterThanEqualIf{WeightedSum{} + 1_i * y, 7_i, sel == 0_i});

        // y in 7..9 forced by z <= 12 and z >= y + 3, with sel = 0; sel = 1
        // needs y >= 10 and so z >= 13, which is impossible.
        run_node_invariant_test("incremental stale do", incremental, p, {sel, y, z},
            {{"z >= y + 3", [=](const CurrentState & s) { return s.lower_bound(z) >= s.lower_bound(y) + 3_i; }},
                {"y <= z - 3", [=](const CurrentState & s) { return s.upper_bound(y) <= s.upper_bound(z) - 3_i; }}},
            6);
    }

    // (b) A Boolean fixed with no node bound change at all. At the root `b` is
    // undecided, so its edge is not in the graph and nothing constrains y; the
    // moment `b` is fixed true the edge joins the graph and `y >= x + 4` has to
    // be pushed --- from x's *root* lower bound, which has not moved since the
    // last run.
    //
    // So `Vl` is empty, and an implementation that transcribed only the paper's
    // section 5.4 (repair the potential function on activation, and stop there)
    // would do nothing at all here. Section 4.4 is the one that says to seed
    // bound propagation across the new arc as well.
    auto run_activation_seed_test(bool incremental) -> void
    {
        Problem p;
        auto b = p.create_integer_variable(0_i, 1_i, "b");
        auto x = p.create_integer_variable(0_i, 10_i, "x");
        auto y = p.create_integer_variable(0_i, 10_i, "y");
        p.post(DifferenceConstraints{{DifferenceEdge{x, y, -4_i, b == 1_i}}}
                .simplifying_at_root(false)
                .incrementally(incremental)
                .auditing_incremental_propagation());

        auto b_holds = [=](const CurrentState & s) { return s.lower_bound(b) == 1_i; };
        run_node_invariant_test("incremental activation seed", incremental, p, {b, x, y},
            {{"y >= x + 4 once b is true", [=](const CurrentState & s) { return ! b_holds(s) || s.lower_bound(y) >= s.lower_bound(x) + 4_i; }},
                {"x <= y - 4 once b is true", [=](const CurrentState & s) { return ! b_holds(s) || s.upper_bound(x) <= s.upper_bound(y) - 4_i; }}},
            // b = 1: x in 0..6, y in x+4..10, so sum over x of (7 - x) = 28.
            // b = 0: 121.
            149);
    }

    // (c) Activate, backtrack, tighten elsewhere, re-activate, and close a
    // negative cycle. `g` is branched first purely so that the (b, c) subtree is
    // entered four times, each entry after a backtrack that deactivated both
    // conditional edges; every activation after the first is a *re*-activation.
    //
    // The potential function is never trailed and drifts downwards over the
    // whole search, so an edge that satisfied the potential invariant when it
    // was last active can violate it when it comes back. Caching "this edge has
    // been checked" would leave the reduced cost negative, which corrupts
    // Dijkstra's settle order and can lose the refutation entirely.
    auto run_reactivation_test(bool incremental) -> void
    {
        Problem p;
        auto g = p.create_integer_variable(0_i, 3_i, "g");
        auto b = p.create_integer_variable(0_i, 1_i, "b");
        auto cc = p.create_integer_variable(0_i, 1_i, "c");
        auto x = p.create_integer_variable(0_i, 10_i, "x");
        auto y = p.create_integer_variable(0_i, 10_i, "y");
        // b and c together close a cycle of weight -3; either alone is fine.
        p.post(DifferenceConstraints{{DifferenceEdge{x, y, -5_i, b == 1_i}, DifferenceEdge{y, x, 2_i, cc == 1_i}}}
                .simplifying_at_root(false)
                .incrementally(incremental)
                .auditing_incremental_propagation());

        run_node_invariant_test("incremental reactivation", incremental, p, {g, b, cc, x, y},
            {{"b and c are never both true", [=](const CurrentState & s) { return ! (s.lower_bound(b) == 1_i && s.lower_bound(cc) == 1_i); }},
                {"y >= x + 5 once b is true",
                    [=](const CurrentState & s) { return s.lower_bound(b) != 1_i || s.lower_bound(y) >= s.lower_bound(x) + 5_i; }}},
            // Per g value: b=0,c=0 gives 121; b=0,c=1 gives |{x,y : x >= y - 2}|
            // = 121 - |{y - x > 2}| = 121 - 36 = 85; b=1,c=0 gives
            // |{y >= x + 5}| = 21; b=1,c=1 is refuted. 227 per g, four g values.
            908);
    }

    // (e) A conditional static bound applied in a branch that then fails must
    // leave nothing behind. Static bounds are re-derived from the state on every
    // call and never enter Do or the arc records, so there is nothing to leak;
    // this pins that, since a static bound is the one shape that is neither an
    // arc nor a node bound change.
    auto run_conditional_static_bound_test(bool incremental) -> void
    {
        Problem p;
        auto b = p.create_integer_variable(0_i, 1_i, "b");
        auto x = p.create_integer_variable(0_i, 10_i, "x");
        auto y = p.create_integer_variable(0_i, 10_i, "y");
        // b -> x <= 3 and b -> x >= 5, which cannot both hold, so every solution
        // has b = 0 and x unconstrained. y hangs off x by an ordinary edge, so a
        // bound left behind after the failed branch would show up as a missing
        // solution rather than only as a tighter domain.
        p.post(DifferenceConstraints{{DifferenceEdge{x, constant_variable(0_i), 3_i, b == 1_i},
                                         DifferenceEdge{constant_variable(5_i), x, 0_i, b == 1_i}, DifferenceEdge{x, y, 0_i}}}
                .simplifying_at_root(false)
                .incrementally(incremental)
                .auditing_incremental_propagation());

        run_node_invariant_test("incremental conditional static bound", incremental, p, {b, x, y},
            {{"y >= x", [=](const CurrentState & s) { return s.lower_bound(y) >= s.lower_bound(x); }},
                {"b is never true", [=](const CurrentState & s) { return s.lower_bound(b) != 1_i; }}},
            // b = 0, y >= x over 0..10: 66.
            66);
    }

    auto run_incremental_tests() -> void
    {
        for (bool incremental : {true, false}) {
            run_stale_do_test(incremental);
            run_activation_seed_test(incremental);
            run_reactivation_test(incremental);
            run_conditional_static_bound_test(incremental);
            // (d) The hole-snap topology, which is where recording the *state's*
            // bounds in Do rather than the bounds the run propagated from goes
            // wrong: the snap lands the state bound above the computed value, so
            // the mandatory self-re-wake finds Vl empty and stops with z at 5.
            run_hole_snap_test(incremental);
        }
    }

    auto run_all_tests(bool proofs, const string & mode) -> void
    {
        if (mode == "basic") {
            // A single edge, both signs of d.
            run_test(proofs, mode, "single_neg", {{0, 6}, {0, 6}}, {{v(0), v(1), -2}});
            run_test(proofs, mode, "single_pos", {{0, 6}, {0, 6}}, {{v(0), v(1), 2}});
            run_test(proofs, mode, "single_zero", {{0, 6}, {0, 6}}, {{v(0), v(1), 0}});

            // A chain: bounds have to travel the whole way in one pass.
            run_test(proofs, mode, "chain", {{0, 5}, {0, 5}, {0, 5}, {0, 5}}, {{v(0), v(1), -1}, {v(1), v(2), -1}, {v(2), v(3), -1}});

            // A tree: one source, two branches, so the predecessor forest has
            // more than one leaf.
            run_test(proofs, mode, "tree", {{0, 5}, {0, 5}, {0, 5}, {0, 5}, {0, 5}},
                {{v(0), v(1), -1}, {v(1), v(2), -1}, {v(1), v(3), -2}, {v(0), v(4), 1}});

            // Negative domains, and a mixture of edge weights.
            run_test(proofs, mode, "negative_domain", {{-4, 2}, {-3, 3}, {-2, 4}}, {{v(0), v(1), -1}, {v(1), v(2), 2}, {v(2), v(0), 3}});

            // Duplicate edges between the same pair, one strictly stronger.
            run_test(proofs, mode, "duplicate_edges", {{0, 6}, {0, 6}}, {{v(0), v(1), 1}, {v(0), v(1), -2}, {v(0), v(1), 3}});
        }
        else if (mode == "cycles") {
            // A negative cycle: unsatisfiable, and refuted by summing the cycle.
            run_test(proofs, mode, "negcycle3", {{0, 6}, {0, 6}, {0, 6}}, {{v(0), v(1), 0}, {v(1), v(2), 0}, {v(2), v(0), -1}});
            run_test(proofs, mode, "negcycle2", {{0, 8}, {0, 8}}, {{v(0), v(1), 0}, {v(1), v(0), -2}});
            run_test(proofs, mode, "negcycle_weighted", {{0, 5}, {0, 5}, {0, 5}, {0, 5}},
                {{v(0), v(1), 2}, {v(1), v(2), -3}, {v(2), v(3), 1}, {v(3), v(0), -1}});

            // A zero-weight cycle: satisfiable, and it forces equalities all
            // the way round.
            run_test(proofs, mode, "zerocycle", {{0, 5}, {0, 5}, {0, 5}}, {{v(0), v(1), 0}, {v(1), v(2), 0}, {v(2), v(0), 0}});
            run_test(proofs, mode, "zerocycle_offset", {{0, 6}, {0, 6}}, {{v(0), v(1), -2}, {v(1), v(0), 2}});

            // A negative cycle sitting inside a bigger graph, so the
            // predecessor walk has to skip the nodes hanging off it.
            run_test(proofs, mode, "negcycle_with_tail", {{0, 4}, {0, 4}, {0, 4}, {0, 4}},
                {{v(0), v(1), 0}, {v(1), v(2), 0}, {v(2), v(1), -1}, {v(2), v(3), 1}});
        }
        else if (mode == "views") {
            // Offset views on either or both ends. The offsets fold into the
            // weight, so the OPB row is over the bare variables and every
            // edge's row speaks the same representation.
            run_test(proofs, mode, "view_left", {{0, 6}, {0, 6}}, {{v(0, 3), v(1), 0}});
            run_test(proofs, mode, "view_right", {{0, 6}, {0, 6}}, {{v(0), v(1, -2), 1}});
            run_test(proofs, mode, "view_both", {{0, 5}, {0, 5}, {0, 5}}, {{v(0, 4), v(1, -1), -1}, {v(1, 2), v(2, 2), 0}});
            run_test(proofs, mode, "view_chain", {{0, 5}, {0, 5}, {0, 5}}, {{v(0, 1), v(1, 1), -1}, {v(1, -3), v(2, 3), 0}});

            // The same variable reached through two different offset views in
            // two edges: the graph joins them at one node, which only cancels
            // because both rows are emitted over the bare variable.
            run_test(proofs, mode, "view_shared_node", {{0, 5}, {0, 5}, {0, 5}}, {{v(0), v(1, 2), -1}, {v(1, -3), v(2), -1}});

            // A negative cycle whose edges are all expressed through views.
            run_test(proofs, mode, "view_negcycle", {{0, 5}, {0, 5}}, {{v(0, 2), v(1), 0}, {v(1, 1), v(0, 4), 0}});

            // Constant operands, which are static bounds on the other end.
            run_test(proofs, mode, "constant_upper", {{0, 8}}, {{v(0), c(2), 3}});
            run_test(proofs, mode, "constant_lower", {{0, 8}}, {{c(7), v(0), 2}});
            run_test(proofs, mode, "constant_both_true", {{0, 3}}, {{c(1), c(4), 0}, {v(0), c(0), 2}});
            run_test(proofs, mode, "constant_both_false", {{0, 3}}, {{c(4), c(1), 0}});
            run_test(proofs, mode, "constant_and_edge", {{0, 8}, {0, 8}}, {{c(4), v(0), 0}, {v(0), v(1), -2}});
        }
        else if (mode == "alias") {
            // The same variable in both slots, once vacuous and once a root
            // contradiction. Handled, not thrown: x - x <= d is 0 <= d.
            run_test(proofs, mode, "alias_ok", {{0, 5}, {0, 5}}, {{v(0), v(0), 0}, {v(0), v(1), -1}});
            run_test(proofs, mode, "alias_ok_pos", {{0, 5}}, {{v(0), v(0), 3}});
            run_test(proofs, mode, "alias_bad", {{0, 5}, {0, 5}}, {{v(0), v(0), -1}, {v(0), v(1), 0}});
            // Aliasing through views, where the offsets decide the sign.
            run_test(proofs, mode, "alias_view_ok", {{0, 5}}, {{v(0, 2), v(0), 3}});
            run_test(proofs, mode, "alias_view_bad", {{0, 5}}, {{v(0, 2), v(0), 1}});
            // An empty system, and one with nothing but a vacuous edge.
            run_test(proofs, mode, "empty", {{0, 3}}, {});
        }
        else if (mode == "reified") {
            // Throughout: the last one or two variables have domain 0..1 and
            // are the reification conditions, so the oracle enumerates both
            // settings of each and every fixture below checks the false branch
            // as well as the true one.

            // A negative cycle two of whose three edges are conditional. It
            // closes only when both conditions hold, so exactly the (1, 1)
            // quadrant is excluded -- and that is the case reified_hand.pbp
            // verifies by hand: sum the three rows, saturate, and the residual
            // is the clause ~b1 v ~b2.
            run_test(proofs, mode, "negcycle_two_conds", {{0, 5}, {0, 5}, {0, 5}, {0, 1}, {0, 1}},
                {{v(0), v(1), 0, b(3)}, {v(1), v(2), 0, b(4)}, {v(2), v(0), -1}});

            // The same cycle with every edge conditional on the same Boolean.
            // This is the paper's section 4.1 caveat made concrete (a Boolean
            // appearing in more than one difference constraint, which its
            // "domain propagator" claim excludes and which every disjunctive
            // encoding does anyway): soundness must hold regardless, and the
            // reason must not list the Boolean three times.
            run_test(proofs, mode, "negcycle_shared_cond", {{0, 5}, {0, 5}, {0, 5}, {0, 1}},
                {{v(0), v(1), 0, b(3)}, {v(1), v(2), 0, b(3)}, {v(2), v(0), -1, b(3)}});

            // Mixed: an unconditional cycle would already be infeasible, so the
            // conditional edge is the only thing standing between satisfiable
            // and not.
            run_test(proofs, mode, "negcycle_mixed", {{0, 4}, {0, 4}, {0, 4}, {0, 1}}, {{v(0), v(1), -1}, {v(1), v(2), -1}, {v(2), v(0), 1, b(3)}});

            // Bound pushes across conditional edges, chained, so the reason of
            // the second cites the first's inferred bound and its own condition.
            // Domains kept narrow enough that the whole solution set fits inside
            // the default runtime cap, so this keeps its cross-check against the
            // decomposed model even in a capped run.
            run_test(proofs, mode, "chain_conds", {{0, 4}, {0, 4}, {0, 4}, {0, 1}, {0, 1}}, {{v(0), v(1), -2, b(3)}, {v(1), v(2), -2, b(4)}});

            // A conditional edge that can never hold over these domains: the
            // negative control, as a solution count. Every assignment with the
            // condition false is a solution, and none with it true.
            run_test(proofs, mode, "cond_impossible", {{0, 4}, {0, 4}, {0, 1}}, {{v(0), v(1), -10, b(2)}});

            // Conditioning on the *false* value of a 0..1 variable, which is
            // the other half of a disjunctive decomposition.
            run_test(proofs, mode, "cond_on_zero", {{0, 4}, {0, 4}, {0, 1}}, {{v(0), v(1), -2, b(2, 0)}, {v(1), v(0), -2, b(2)}});

            // A conditional edge whose condition is over a variable with a
            // wider domain, so the condition is `x == 2' rather than a Boolean.
            run_test(proofs, mode, "cond_not_boolean", {{0, 4}, {0, 4}, {0, 3}}, {{v(0), v(1), -3, b(2, 2)}});

            // Conditional edges through offset views on both ends, which is
            // where a proof only telescopes because the rows are emitted over
            // the canonical bare variables.
            run_test(proofs, mode, "cond_views", {{0, 5}, {0, 5}, {0, 5}, {0, 1}}, {{v(0, 2), v(1, -1), -1, b(3)}, {v(1, 3), v(2), 0, b(3)}});
            run_test(proofs, mode, "cond_view_negcycle", {{0, 5}, {0, 5}, {0, 1}}, {{v(0, 2), v(1), 0, b(2)}, {v(1, 1), v(0, 4), 0}});

            // Conditional static bounds (a constant operand) and conditional
            // degenerate edges (aliasing), which are the two shapes that are not
            // graph edges at all.
            run_test(proofs, mode, "cond_constant", {{0, 8}, {0, 1}}, {{v(0), c(0), 3, b(1)}, {c(6), v(0), 0, b(1, 0)}});
            run_test(proofs, mode, "cond_alias_bad", {{0, 3}, {0, 1}}, {{v(0), v(0), -1, b(1)}});
            run_test(proofs, mode, "cond_alias_ok", {{0, 3}, {0, 1}}, {{v(0), v(0), 0, b(1)}});

            // Two Booleans, four quadrants, each excluding a different part of
            // the space: nothing may be pruned in the wrong quadrant.
            run_test(
                proofs, mode, "cond_quadrants", {{0, 4}, {0, 4}, {0, 1}, {0, 1}}, {{v(0), v(1), -2, b(2)}, {v(1), v(0), -2, b(3)}, {v(0), v(1), 1}});
        }
        else if (mode == "random" || mode == "random_reified") {
            // In random_reified, two extra 0..1 variables sit at the end of the
            // domain list and each edge is conditional on one of them (or on
            // neither) with equal probability, so mixed conditional and
            // unconditional systems, shared conditions and both polarities all
            // turn up without being enumerated by hand.
            auto reified = (mode == "random_reified");
            mt19937 rand(*get_seed());
            for (int iteration = 0; iteration < 12; ++iteration) {
                uniform_int_distribution n_vars_dist{2, 4};
                auto n_vars = n_vars_dist(rand);
                vector<pair<int, int>> domains;
                for (int i = 0; i < n_vars; ++i) {
                    uniform_int_distribution lo_dist{-3, 2};
                    auto lo = lo_dist(rand);
                    uniform_int_distribution width_dist{0, 4};
                    domains.emplace_back(lo, lo + width_dist(rand));
                }

                auto n_conds = reified ? 2 : 0;
                for (int i = 0; i < n_conds; ++i)
                    domains.emplace_back(0, 1);

                uniform_int_distribution n_edges_dist{1, 6};
                auto n_edges = n_edges_dist(rand);
                vector<EdgeSpec> edges;
                for (int e = 0; e < n_edges; ++e) {
                    uniform_int_distribution var_dist{0, n_vars - 1};
                    uniform_int_distribution offset_dist{-2, 2};
                    uniform_int_distribution d_dist{-3, 3};
                    optional<Cond> cond;
                    if (reified) {
                        uniform_int_distribution which_dist{0, 2 * n_conds};
                        auto which = which_dist(rand);
                        if (which > 0)
                            cond = Cond{static_cast<size_t>(n_vars + (which - 1) / 2), (which - 1) % 2};
                    }
                    edges.push_back(EdgeSpec{v(static_cast<size_t>(var_dist(rand)), offset_dist(rand)),
                        v(static_cast<size_t>(var_dist(rand)), offset_dist(rand)), d_dist(rand), cond});
                }

                run_test(proofs, mode, "random" + to_string(iteration), domains, edges);
            }
        }
        else
            throw UnimplementedException{};
    }
}

auto main(int argc, char * argv[]) -> int
{
    establish_and_announce_seed(argc, argv);

    if (argc < 2)
        throw UnimplementedException{};

    string mode{argv[1]};

    run_negated_view_test();
    if (mode == "basic")
        for (bool incremental : {true, false}) {
            run_transitive_test(incremental);
            run_hole_snap_test(incremental);
        }
    if (mode == "reified")
        for (bool incremental : {true, false}) {
            run_reified_bounds_test(incremental);
            run_reified_degenerate_test(incremental);
        }
    if (mode == "incremental") {
        run_incremental_tests();
        return EXIT_SUCCESS;
    }
    if (mode == "simplify") {
        run_root_refutation_test();
        for (bool proofs : {false, true}) {
            if (proofs && ! can_run_veripb())
                continue;
            run_simplify_tests(proofs);
        }
        return EXIT_SUCCESS;
    }

    for (bool proofs : {false, true}) {
        if (proofs && ! can_run_veripb())
            continue;
        run_all_tests(proofs, mode);
    }

    return EXIT_SUCCESS;
}
