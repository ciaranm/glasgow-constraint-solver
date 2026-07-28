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

    struct EdgeSpec
    {
        Operand x;
        Operand y;
        int d;
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
        for (const auto & e : edges)
            if (operand_value(e.x, vals) - operand_value(e.y, vals) > e.d)
                return false;
        return true;
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

        {
            Problem p;
            auto vars = make_vars(p, domains);
            vector<DifferenceEdge> posted;
            for (const auto & e : edges)
                posted.push_back(DifferenceEdge{operand_id(e.x, vars), operand_id(e.y, vars), Integer(e.d)});
            p.post(DifferenceConstraints{posted});

            auto proof_name = proofs ? make_optional("difference_test_" + mode + "_" + name) : nullopt;
            // Bounds consistent, not GAC: the propagator only reads and writes
            // bounds, and gcs domains can have holes where the paper's Theorem
            // 2 assumes ranges.
            solve_for_tests(p, proof_name, actual, tuple{vars});
            check_results(proof_name, expected, actual);
        }

        {
            Problem p;
            auto vars = make_vars(p, domains);
            for (const auto & e : edges)
                p.post(LinearLessThanEqual{WeightedSum{} + 1_i * operand_id(e.x, vars) + -1_i * operand_id(e.y, vars), Integer(e.d)});
            solve_for_tests(p, nullopt, decomposed, tuple{vars});
        }

        if (actual != decomposed) {
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
        else if (mode == "random") {
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

                uniform_int_distribution n_edges_dist{1, 6};
                auto n_edges = n_edges_dist(rand);
                vector<EdgeSpec> edges;
                for (int e = 0; e < n_edges; ++e) {
                    uniform_int_distribution var_dist{0, n_vars - 1};
                    uniform_int_distribution offset_dist{-2, 2};
                    uniform_int_distribution d_dist{-3, 3};
                    edges.push_back(EdgeSpec{v(static_cast<size_t>(var_dist(rand)), offset_dist(rand)),
                        v(static_cast<size_t>(var_dist(rand)), offset_dist(rand)), d_dist(rand)});
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

    for (bool proofs : {false, true}) {
        if (proofs && ! can_run_veripb())
            continue;
        run_all_tests(proofs, mode);
    }

    return EXIT_SUCCESS;
}
