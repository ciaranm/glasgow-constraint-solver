#include <gcs/constraints/difference.hh>
#include <gcs/constraints/innards/constraints_test_utils.hh>
#include <gcs/constraints/linear.hh>
#include <gcs/exception.hh>
#include <gcs/problem.hh>
#include <gcs/solve.hh>

#include <cstdlib>
#include <iostream>
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
using std::make_optional;
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
    auto run_test(bool proofs, const string & mode, const string & name, const vector<pair<int, int>> & domains, const vector<EdgeSpec> & edges)
        -> void
    {
        print(cerr, "difference {} {} domains={} edges={}{}", mode, name, domains, edges.size(), proofs ? " with proofs:" : ":");
        cerr << flush;

        set<tuple<vector<int>>> expected, actual, decomposed;
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

        {
            Problem p;
            auto vars = make_vars(p, domains);
            vector<DifferenceEdge> posted;
            for (const auto & e : edges)
                posted.push_back(DifferenceEdge{operand_id(e.x, vars), operand_id(e.y, vars), Integer(e.d), condition_id(e.cond, vars)});
            p.post(DifferenceConstraints{posted});

            auto proof_name = proofs ? make_optional("difference_test_" + mode + "_" + name) : nullopt;
            // Bounds consistent, not GAC: the propagator only reads and writes
            // bounds, and gcs domains can have holes where the paper's Theorem
            // 2 assumes ranges.
            solve_for_tests(p, proof_name, actual, tuple{vars});
            truncated = truncated || last_run_truncated();
            check_results(proof_name, expected, actual);
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

        if (truncated)
            println(cerr, "difference {} {}: a cap fired, so the global/decomposed cross-check is skipped", mode, name);
        else if (actual != decomposed) {
            println(cerr, "difference {} {}: global and decomposed models disagree", mode, name);
            println(cerr, "global has {} solutions, decomposed has {}", actual.size(), decomposed.size());
            throw UnexpectedException{"difference global and decomposed models disagree"};
        }
    }

    // The transitive push: two edges whose combined bound is strictly stronger
    // than either edge on its own. x - y <= -3 gives y >= x + 3, y - z <= -4
    // gives z >= y + 4, so the system entails z >= x + 7 -- a bound no single
    // edge implies. Solve as far as the first complete propagation and read the
    // bounds off, so this asserts the propagator actually fires rather than
    // merely that the solution set is right.
    auto run_transitive_test() -> void
    {
        print(cerr, "difference transitive push:");
        cerr << flush;

        Problem p;
        auto x = p.create_integer_variable(0_i, 10_i, "x");
        auto y = p.create_integer_variable(0_i, 10_i, "y");
        auto z = p.create_integer_variable(0_i, 10_i, "z");
        p.post(DifferenceConstraints{{DifferenceEdge{x, y, -3_i}, DifferenceEdge{y, z, -4_i}}});

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
    auto run_hole_snap_test() -> void
    {
        print(cerr, "difference hole snap:");
        cerr << flush;

        Problem p;
        auto x = p.create_integer_variable(0_i, 10_i, "x");
        auto y = p.create_integer_variable(vector<Integer>{0_i, 1_i, 2_i, 6_i, 7_i, 8_i, 9_i, 10_i}, "y");
        auto z = p.create_integer_variable(0_i, 10_i, "z");
        p.post(DifferenceConstraints{{DifferenceEdge{x, y, -3_i}, DifferenceEdge{y, z, -2_i}}});

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
    auto run_reified_bounds_test() -> void
    {
        print(cerr, "difference reified push and negative control:");
        cerr << flush;

        Problem p;
        auto x = p.create_integer_variable(0_i, 10_i, "x");
        auto y = p.create_integer_variable(0_i, 10_i, "y");
        auto z = p.create_integer_variable(0_i, 10_i, "z");
        auto w = p.create_integer_variable(0_i, 10_i, "w");
        auto b1 = p.create_integer_variable(1_i, 1_i, "b1");
        auto b2 = p.create_integer_variable(0_i, 0_i, "b2");
        p.post(DifferenceConstraints{
            {DifferenceEdge{x, y, -3_i, b1 == 1_i}, DifferenceEdge{y, z, -4_i, b1 == 1_i}, DifferenceEdge{w, z, -20_i, b2 == 1_i}}});

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
    auto run_reified_degenerate_test() -> void
    {
        print(cerr, "difference reified degenerate edge:");
        cerr << flush;

        Problem p;
        auto x = p.create_integer_variable(0_i, 5_i, "x");
        auto bad = p.create_integer_variable(0_i, 1_i, "bad");
        auto fine = p.create_integer_variable(0_i, 1_i, "fine");
        // bad -> x - x <= -1, i.e. !bad. fine -> x - x <= 0, i.e. nothing.
        p.post(DifferenceConstraints{{DifferenceEdge{x, x, -1_i, bad == 1_i}, DifferenceEdge{x, x, 0_i, fine == 1_i}}});

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
    if (mode == "basic") {
        run_transitive_test();
        run_hole_snap_test();
    }
    if (mode == "reified") {
        run_reified_bounds_test();
        run_reified_degenerate_test();
    }

    for (bool proofs : {false, true}) {
        if (proofs && ! can_run_veripb())
            continue;
        run_all_tests(proofs, mode);
    }

    return EXIT_SUCCESS;
}
