// Tests for the difference-logic presolver.
//
// READ THIS BEFORE "FIXING" A FAILURE HERE.
//
// This presolver is invisible from the outside by design. It adds no OPB
// content, changes no solution, and leaves every proof verifying. That means a
// presolver which silently lifted *nothing* -- because, say, Constraint::clone()
// stopped flattening a posted LinearLessThanEqual down to
// ReifiedLinearInequality, so that
// Problem::each_constraint_of_type<ReifiedLinearInequality>() no longer matched
// it -- would pass:
//
//   * every solution-set equivalence check (a no-op presolver preserves them);
//   * the OPB byte-identical check (byte-identical is the *expected* result);
//   * every VeriPB run (there would be nothing new to verify).
//
// So the assertions on DifferenceLogicStats below, and the propagation-count
// differential in the `differential` mode, are the only things standing between
// a silent regression and shipping. If one of them fails, DETECTION IS BROKEN.
// Do not update the expected numbers to match what the code now does. Fix
// gcs/presolvers/difference_logic.cc.

#include <gcs/constraints/all_different.hh>
#include <gcs/constraints/comparison.hh>
#include <gcs/constraints/innards/constraints_test_utils.hh>
#include <gcs/constraints/linear.hh>
#include <gcs/exception.hh>
#include <gcs/presolvers/difference_logic.hh>
#include <gcs/problem.hh>
#include <gcs/solve.hh>

#include <cstdio>
#include <cstdlib>
#include <fstream>
#include <iostream>
#include <iterator>
#include <memory>
#include <optional>
#include <set>
#include <sstream>
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
using std::ifstream;
using std::istreambuf_iterator;
using std::make_optional;
using std::make_shared;
using std::nullopt;
using std::optional;
using std::pair;
using std::set;
using std::shared_ptr;
using std::string;
using std::to_string;
using std::tuple;
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
    // Boilerplate every failure message here shares. Naming the invariant is not
    // enough on its own: the whole hazard is that "just update the number" looks
    // like a reasonable response to one of these.
    const string detection_is_broken = "\n\nThis means the presolver's DETECTION is broken, not that this expectation is stale.\n"
                                       "The most likely cause is a change to Constraint::clone() or to the Linear class\n"
                                       "hierarchy, such that Problem::each_constraint_of_type<ReifiedLinearInequality>()\n"
                                       "no longer yields posted LinearLessThanEqual constraints (clone() currently returns\n"
                                       "the family base -- see PR #585).\n\n"
                                       "Fix gcs/presolvers/difference_logic.cc. Do NOT update the expected count here: a\n"
                                       "presolver that lifts nothing still passes every solution-equivalence, OPB byte-diff\n"
                                       "and VeriPB check, so this assertion is the only thing standing between a silent\n"
                                       "regression and shipping.";

    auto check_count(const string & what, size_t expected, size_t actual, const string & fixture) -> void
    {
        if (expected != actual)
            throw UnexpectedException{"the difference-logic presolver reported " + to_string(actual) + " for " + what + " on fixture '" + fixture +
                "', expected " + to_string(expected) + "." + detection_is_broken};
    }

    // One end of an edge: variable `var` offset by `offset` (a bare variable
    // when the offset is zero, a `+X + c` view otherwise), or, when `var` is
    // unset, the constant `offset`.
    struct Operand
    {
        optional<size_t> var;
        int offset;
        bool negated = false;
    };

    auto v(size_t i) -> Operand
    {
        return Operand{i, 0};
    }

    auto v(size_t i, int offset) -> Operand
    {
        return Operand{i, offset};
    }

    auto neg(size_t i) -> Operand
    {
        return Operand{i, 0, true};
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
        auto base = o.var ? vals.at(*o.var) : 0;
        return (o.negated ? -base : base) + o.offset;
    }

    auto operand_id(const Operand & o, const vector<IntegerVariableID> & vars) -> IntegerVariableID
    {
        if (! o.var)
            return constant_variable(Integer(o.offset));
        auto base = o.negated ? -vars.at(*o.var) : vars.at(*o.var);
        return o.offset == 0 ? base : base + Integer(o.offset);
    }

    auto satisfied(const vector<int> & vals, const vector<EdgeSpec> & edges) -> bool
    {
        for (const auto & e : edges)
            if (operand_value(e.x, vals) - operand_value(e.y, vals) > e.d)
                return false;
        return true;
    }

    // How the presolver is (or is not) attached. The hybrid is what ships; the
    // third exists so the redundant donors can be measured, and because a search
    // tree that moves when they are switched off would mean the global
    // propagator does not in fact subsume them.
    enum class Config
    {
        NoPresolver,
        Hybrid,
        DonorsDisabled
    };

    auto config_name(Config config) -> string
    {
        switch (config) {
            using enum Config;
        case NoPresolver: return "no-presolver";
        case Hybrid: return "hybrid";
        case DonorsDisabled: return "donors-disabled";
        }
        throw UnimplementedException{};
    }

    // Post the system as one two-term LinearLessThanEqual per edge -- the shape
    // the presolver detects -- and attach the presolver as asked.
    auto build(Problem & p, const vector<pair<int, int>> & domains, const vector<EdgeSpec> & edges, Config config,
        const shared_ptr<DifferenceLogicStats> & stats) -> vector<IntegerVariableID>
    {
        vector<IntegerVariableID> vars;
        for (const auto & [lo, hi] : domains)
            vars.push_back(p.create_integer_variable(Integer(lo), Integer(hi)));

        for (const auto & e : edges)
            p.post(LinearLessThanEqual{WeightedSum{} + 1_i * operand_id(e.x, vars) + -1_i * operand_id(e.y, vars), Integer(e.d)});

        switch (config) {
            using enum Config;
        case NoPresolver: break;
        case Hybrid: p.add_presolver(DifferenceLogic{stats}); break;
        case DonorsDisabled: p.add_presolver(DifferenceLogic{stats}.disabling_lifted_donors()); break;
        }

        return vars;
    }

    // Solution-set equivalence across all three configurations, against an
    // independent C++ oracle. Sound and complete, in both directions: an
    // over-pruning presolver loses a solution and an unsound one gains one, and
    // no proof would catch either, since a proof only certifies what was
    // derived.
    auto run_equivalence_test(bool proofs, const string & name, const vector<pair<int, int>> & domains, const vector<EdgeSpec> & edges,
        size_t expected_edges_lifted) -> void
    {
        print(cerr, "difference presolver equivalence {} domains={} edges={}{}", name, domains, edges.size(), proofs ? " with proofs:" : ":");
        cerr << flush;

        set<tuple<vector<int>>> expected;
        build_expected(expected, [&](const vector<int> & vals) { return satisfied(vals, edges); }, domains);
        println(cerr, " expecting {} solutions", expected.size());

        for (auto config : {Config::NoPresolver, Config::Hybrid, Config::DonorsDisabled}) {
            auto stats = make_shared<DifferenceLogicStats>();
            Problem p;
            auto vars = build(p, domains, edges, config, stats);

            set<tuple<vector<int>>> actual;
            // The presolver only reads and writes bounds, so bounds consistent,
            // not GAC.
            auto proof_name = proofs ? make_optional("difference_presolver_" + name + "_" + config_name(config)) : nullopt;
            solve_for_tests(p, proof_name, actual, tuple{vars});
            check_results(proof_name, expected, actual);

            if (config != Config::NoPresolver)
                check_count("edges lifted", expected_edges_lifted, stats->edges_lifted, name);
        }
    }

    // The tripwire. Disabling the donors' own propagators must not change the
    // search tree at all: the global propagator subsumes every single-edge bound
    // push, and disabling changes neither degrees nor adjacency, so the
    // branching heuristic sees an unchanged problem. Solutions *and* recursions
    // must match exactly. (Propagation counts of course do not, and are the
    // point of the option.)
    auto run_tripwire_test(const string & name, const vector<pair<int, int>> & domains, const vector<EdgeSpec> & edges) -> void
    {
        print(cerr, "difference presolver tripwire {}:", name);
        cerr << flush;

        Stats results[2];
        for (auto [index, config] : {pair{0, Config::Hybrid}, pair{1, Config::DonorsDisabled}}) {
            auto stats = make_shared<DifferenceLogicStats>();
            Problem p;
            static_cast<void>(build(p, domains, edges, config, stats));
            results[index] = solve_with(p, SolveCallbacks{.solution = [&](const CurrentState &) -> bool { return true; }});
            if (config == Config::DonorsDisabled && 0 == stats->donor_propagators_disabled)
                throw UnexpectedException{"the difference-logic presolver disabled no donor propagators on fixture '" + name +
                    "', so the tripwire compared two identical configurations." + detection_is_broken};
        }

        println(cerr, " hybrid {} solutions / {} recursions / {} propagations, donors off {} / {} / {}", results[0].solutions, results[0].recursions,
            results[0].propagations, results[1].solutions, results[1].recursions, results[1].propagations);

        if (results[0].solutions != results[1].solutions)
            throw UnexpectedException{"difference presolver fixture '" + name + "' found " + to_string(results[0].solutions) +
                " solutions with the donors enabled but " + to_string(results[1].solutions) +
                " with them disabled: the global propagator does not subsume them and disabling is unsound"};

        if (results[0].recursions != results[1].recursions)
            throw UnexpectedException{"difference presolver fixture '" + name + "' searched " + to_string(results[0].recursions) +
                " nodes with the donors enabled but " + to_string(results[1].recursions) +
                " with them disabled: the search tree moved, so the global propagator does not reach the same fixpoint as the donors do"};
    }

    // The corpus: views on either end and shared between edges, aliasing,
    // constant operands, negative cycles, zero-weight cycles, and a negated view
    // that must be refused rather than mis-lifted.
    struct Fixture
    {
        string name;
        vector<pair<int, int>> domains;
        vector<EdgeSpec> edges;
        size_t expected_edges_lifted;
    };

    auto corpus() -> vector<Fixture>
    {
        return {{"chain", {{0, 5}, {0, 5}, {0, 5}, {0, 5}}, {{v(0), v(1), -1}, {v(1), v(2), -1}, {v(2), v(3), -1}}, 3},
            {"tree", {{0, 5}, {0, 5}, {0, 5}, {0, 5}}, {{v(0), v(1), -1}, {v(1), v(2), -1}, {v(1), v(3), -2}}, 3},
            {"negative_domain", {{-4, 2}, {-3, 3}, {-2, 4}}, {{v(0), v(1), -1}, {v(1), v(2), 2}, {v(2), v(0), 3}}, 3},
            {"negcycle", {{0, 6}, {0, 6}, {0, 6}}, {{v(0), v(1), 0}, {v(1), v(2), 0}, {v(2), v(0), -1}}, 3},
            {"zerocycle", {{0, 5}, {0, 5}, {0, 5}}, {{v(0), v(1), 0}, {v(1), v(2), 0}, {v(2), v(0), 0}}, 3},
            {"zerocycle_offset", {{0, 6}, {0, 6}}, {{v(0), v(1), -2}, {v(1), v(0), 2}}, 2},
            {"views", {{0, 5}, {0, 5}, {0, 5}}, {{v(0, 4), v(1, -1), 1}, {v(1, 2), v(2, 2), 0}}, 2},
            // The same variable reached through two different offset views, which
            // only cancels in the proof because the pol cites the donors' rows in
            // deview mode.
            {"view_shared_node", {{0, 5}, {0, 5}, {0, 5}}, {{v(0), v(1, 2), -1}, {v(1, -3), v(2), -1}}, 2},
            {"view_negcycle", {{0, 5}, {0, 5}}, {{v(0, 2), v(1), 0}, {v(1, 1), v(0), 0}}, 2},
            // The same negative cycle over domains too wide for the donors to
            // have crawled anywhere much before the global propagator fires, so
            // the refutation has to be made from loose bounds. That is what
            // forces the telescoping pol to do real work in the *hybrid*
            // configuration too, and with views in play it only telescopes
            // because the pol cites the donors' rows in deview mode. Confirmed
            // by mutation: dropping enable_deview_mode fails VeriPB here.
            {"view_negcycle_wide", {{0, 60}, {0, 60}}, {{v(0, 2), v(1), 0}, {v(1, 1), v(0), 0}}, 2},
            // Aliasing and constant operands are left to their own propagators,
            // so only the two real edges are lifted.
            {"alias_and_constants", {{0, 5}, {0, 5}, {0, 5}}, {{v(0), v(0), 0}, {v(0), c(4), 1}, {c(1), v(1), 0}, {v(0), v(1), -1}, {v(1), v(2), -1}},
                2},
            // A negated view is not a difference constraint at all, and must be
            // refused rather than lifted: -x - y <= d has both coefficients
            // negative. The other two edges still lift.
            {"negated_view", {{-3, 3}, {-3, 3}, {-3, 3}}, {{neg(0), v(1), 1}, {v(0), v(2), -1}, {v(2), v(1), -1}}, 2}};
    }

    auto run_equivalence_tests(bool proofs) -> void
    {
        for (const auto & f : corpus())
            run_equivalence_test(proofs, f.name, f.domains, f.edges, f.expected_edges_lifted);
    }

    auto run_tripwire_tests() -> void
    {
        for (const auto & f : corpus())
            run_tripwire_test(f.name, f.domains, f.edges);
    }

    // Every donor shape, with the count it must land in. A donor migrating from
    // one bucket to another -- most dangerously from "lifted" to any of the
    // skips -- is caught here and nowhere else.
    auto run_detection_tests() -> void
    {
        auto check = [](const string & fixture, const DifferenceLogicStats & stats, const DifferenceLogicStats & expected) {
            println(cerr,
                "difference presolver detection {}: lifted {} over {} nodes, skipped {} not-two-terms, {} coefficients, {} reified, {} "
                "negated-view, {} degenerate, {} unlabelled-comparison",
                fixture, stats.edges_lifted, stats.nodes, stats.skipped_not_two_terms, stats.skipped_coefficients, stats.skipped_reified,
                stats.skipped_negated_view, stats.skipped_degenerate, stats.skipped_unlabelled_comparison);
            check_count("edges lifted", expected.edges_lifted, stats.edges_lifted, fixture);
            check_count("nodes", expected.nodes, stats.nodes, fixture);
            check_count("skipped: not two terms", expected.skipped_not_two_terms, stats.skipped_not_two_terms, fixture);
            check_count("skipped: coefficients", expected.skipped_coefficients, stats.skipped_coefficients, fixture);
            check_count("skipped: reified", expected.skipped_reified, stats.skipped_reified, fixture);
            check_count("skipped: negated view", expected.skipped_negated_view, stats.skipped_negated_view, fixture);
            check_count("skipped: degenerate", expected.skipped_degenerate, stats.skipped_degenerate, fixture);
            check_count("skipped: unlabelled comparison", expected.skipped_unlabelled_comparison, stats.skipped_unlabelled_comparison, fixture);
            if (expected.propagator_installed != stats.propagator_installed)
                throw UnexpectedException{"the difference-logic presolver " + string{stats.propagator_installed ? "did" : "did not"} +
                    " install a propagator on fixture '" + fixture + "', but it should " + (expected.propagator_installed ? "have" : "not have") +
                    "." + detection_is_broken};
        };

        // Five plain two-term +1/-1 linears over four variables: the base case,
        // and the one whose failure means detection has stopped working
        // altogether.
        {
            auto stats = make_shared<DifferenceLogicStats>();
            Problem p;
            auto x = p.create_integer_variable_vector(4, 0_i, 6_i, "x");
            p.post(LinearLessThanEqual{WeightedSum{} + 1_i * x[0] + -1_i * x[1], -1_i});
            p.post(LinearLessThanEqual{WeightedSum{} + 1_i * x[1] + -1_i * x[2], -1_i});
            p.post(LinearLessThanEqual{WeightedSum{} + 1_i * x[2] + -1_i * x[3], -1_i});
            // Written the other way round, and with a view: still an edge.
            p.post(LinearLessThanEqual{WeightedSum{} + -1_i * x[0] + 1_i * x[3], 5_i});
            p.post(LinearLessThanEqual{WeightedSum{} + 1_i * (x[0] + 2_i) + -1_i * x[2], 0_i});
            p.add_presolver(DifferenceLogic{stats});
            solve_with(p, SolveCallbacks{.trace = [](const CurrentState &) -> bool { return false; }});
            check("five_plain_linears", *stats, DifferenceLogicStats{.edges_lifted = 5, .nodes = 4, .propagator_installed = true});
        }

        // Everything that must be skipped, one of each, plus two real edges so
        // that a propagator is still installed.
        {
            auto stats = make_shared<DifferenceLogicStats>();
            Problem p;
            auto x = p.create_integer_variable_vector(4, 0_i, 6_i, "x");
            auto b = p.create_integer_variable(0_i, 1_i, "b");

            // Three terms.
            p.post(LinearLessThanEqual{WeightedSum{} + 1_i * x[0] + -1_i * x[1] + 1_i * x[2], 4_i});
            // Two terms, wrong coefficients.
            p.post(LinearLessThanEqual{WeightedSum{} + 2_i * x[0] + -1_i * x[1], 4_i});
            // Two terms, both positive.
            p.post(LinearLessThanEqual{WeightedSum{} + 1_i * x[0] + 1_i * x[1], 9_i});
            // Half-reified: the row is emitted under HalfReifyOnConjunctionOf, so
            // lifting it as unconditional would be unsound.
            p.post(LinearLessThanEqualIf{WeightedSum{} + 1_i * x[0] + -1_i * x[1], -2_i, b == 1_i});
            // Fully reified, likewise.
            p.post(LinearLessThanEqualIff{WeightedSum{} + 1_i * x[1] + -1_i * x[2], -2_i, b == 1_i});
            // A negated view.
            p.post(LinearLessThanEqual{WeightedSum{} + 1_i * (-x[0]) + -1_i * x[1], 1_i});
            // Aliasing, and a constant operand.
            p.post(LinearLessThanEqual{WeightedSum{} + 1_i * x[0] + -1_i * x[0], 0_i});
            p.post(LinearLessThanEqual{WeightedSum{} + 1_i * x[0] + -1_i * constant_variable(4_i), 1_i});
            // A Comparison, which *is* difference shaped but whose OPB row is
            // emitted unlabelled, so no proof step could cite it.
            p.post(LessThanEqual{x[2], x[3] + 2_i});
            p.post(GreaterThan{x[3], x[2]});
            // ... and one that is not, so it is not counted as a missed
            // opportunity either.
            p.post(LessThan{x[2], constant_variable(5_i)});

            // The two real edges.
            p.post(LinearLessThanEqual{WeightedSum{} + 1_i * x[0] + -1_i * x[1], -1_i});
            p.post(LinearLessThanEqual{WeightedSum{} + 1_i * x[1] + -1_i * x[2], -1_i});

            p.add_presolver(DifferenceLogic{stats});
            solve_with(p, SolveCallbacks{.trace = [](const CurrentState &) -> bool { return false; }});
            check("every_skip", *stats,
                DifferenceLogicStats{.edges_lifted = 2,
                    .nodes = 3,
                    .propagator_installed = true,
                    .skipped_not_two_terms = 1,
                    .skipped_coefficients = 2,
                    .skipped_reified = 2,
                    .skipped_negated_view = 1,
                    .skipped_degenerate = 2,
                    .skipped_unlabelled_comparison = 2});
        }

        // A single edge is a degeneracy, not a threshold: over one edge the
        // global propagator computes exactly what that edge's own propagator
        // computes, so nothing is installed.
        {
            auto stats = make_shared<DifferenceLogicStats>();
            Problem p;
            auto x = p.create_integer_variable_vector(2, 0_i, 6_i, "x");
            p.post(LinearLessThanEqual{WeightedSum{} + 1_i * x[0] + -1_i * x[1], -1_i});
            p.add_presolver(DifferenceLogic{stats});
            solve_with(p, SolveCallbacks{.trace = [](const CurrentState &) -> bool { return false; }});
            check("single_edge", *stats, DifferenceLogicStats{.edges_lifted = 1, .nodes = 2, .propagator_installed = false});
        }

        // A model with nothing difference shaped in it: the presolver must stay
        // completely silent.
        {
            auto stats = make_shared<DifferenceLogicStats>();
            Problem p;
            auto x = p.create_integer_variable_vector(4, 0_i, 3_i, "x");
            p.post(AllDifferent{x});
            p.add_presolver(DifferenceLogic{stats});
            solve_with(p, SolveCallbacks{.trace = [](const CurrentState &) -> bool { return false; }});
            check("nothing_to_lift", *stats, DifferenceLogicStats{.edges_lifted = 0, .nodes = 0, .propagator_installed = false});
        }

        println(cerr, "difference presolver detection: ok");
    }

    auto read_file(const string & name) -> string
    {
        ifstream f{name, std::ios::binary};
        if (! f)
            throw UnexpectedException{"could not read back " + name};
        return string{istreambuf_iterator<char>{f}, istreambuf_iterator<char>{}};
    }

    // The defining property: a presolver adds no OPB content. Presolver::run has
    // no ProofModel * at all, so this should be true by construction; check it
    // anyway, since it is the entire licence for lifting other people's
    // constraints after the model has been finalised.
    auto run_opb_tests() -> void
    {
        auto solve_and_read = [](const string & basename, Config config, auto && post) -> pair<string, string> {
            auto stats = make_shared<DifferenceLogicStats>();
            Problem p;
            post(p);
            switch (config) {
                using enum Config;
            case NoPresolver: break;
            case Hybrid: p.add_presolver(DifferenceLogic{stats}); break;
            case DonorsDisabled: p.add_presolver(DifferenceLogic{stats}.disabling_lifted_donors()); break;
            }
            // Default branching, deliberately: the .pbp comparison below needs
            // determinism, and the point of the negative control is that the
            // presolver installing nothing leaves the search identical too.
            static_cast<void>(solve_with(p, SolveCallbacks{.solution = [](const CurrentState &) -> bool { return true; }},
                make_optional<ProofOptions>(ProofFileNames{basename})));
            auto opb = read_file(basename + ".opb"), pbp = read_file(basename + ".pbp");
            for (auto ext : proof_file_extensions)
                std::remove((basename + ext).c_str());
            return {opb, pbp};
        };

        // Positive case: a system the presolver does lift.
        {
            auto post = [](Problem & p) {
                auto x = p.create_integer_variable_vector(4, 0_i, 5_i, "x");
                p.post(LinearLessThanEqual{WeightedSum{} + 1_i * x[0] + -1_i * x[1], -1_i});
                p.post(LinearLessThanEqual{WeightedSum{} + 1_i * x[1] + -1_i * (x[2] + 1_i), -1_i});
                p.post(LinearLessThanEqual{WeightedSum{} + 1_i * x[2] + -1_i * x[3], -1_i});
            };
            auto [off_opb, off_pbp] = solve_and_read("difference_presolver_opb_off", Config::NoPresolver, post);
            auto [on_opb, on_pbp] = solve_and_read("difference_presolver_opb_on", Config::Hybrid, post);
            if (off_opb != on_opb)
                throw UnexpectedException{"the difference-logic presolver changed the .opb. It must not: Presolver::run is handed no ProofModel, "
                                          "and the whole design rests on the global propagator citing rows the donors already emitted"};
            if (off_pbp == on_pbp)
                throw UnexpectedException{"the difference-logic presolver left the .pbp byte-identical on a fixture it is supposed to lift three "
                                          "edges from, so it evidently propagated nothing." +
                    detection_is_broken};
            println(cerr, "difference presolver opb: lifted fixture .opb identical ({} bytes), .pbp differs ({} vs {} bytes)", off_opb.size(),
                off_pbp.size(), on_pbp.size());
        }

        // Negative control: nothing is difference shaped, so the presolver posts
        // nothing, installs nothing, and does not even perturb the branching.
        // Both files must be byte-identical.
        {
            auto post = [](Problem & p) {
                auto x = p.create_integer_variable_vector(4, 0_i, 3_i, "x");
                p.post(AllDifferent{x});
                p.post(LinearLessThanEqual{WeightedSum{} + 1_i * x[0] + 1_i * x[1] + 1_i * x[2], 4_i});
            };
            auto [off_opb, off_pbp] = solve_and_read("difference_presolver_control_off", Config::NoPresolver, post);
            auto [on_opb, on_pbp] = solve_and_read("difference_presolver_control_on", Config::Hybrid, post);
            if (off_opb != on_opb || off_pbp != on_pbp)
                throw UnexpectedException{"the difference-logic presolver changed the proof of a model containing nothing difference shaped"};
            println(cerr, "difference presolver opb: control .opb and .pbp both identical ({} and {} bytes)", off_opb.size(), off_pbp.size());
        }
    }

    // The behavioural differential a no-op presolver cannot pass. This is the
    // paper's Example 1: x - y <= 0 and y - x <= -2 are trivially unsatisfiable,
    // but no individual constraint is violated by the initial domains, so
    // per-constraint propagation can only find it by crawling both bounds two
    // units at a time -- Theta(domain size) propagations. The global propagator
    // sums the two edges round the cycle and refutes at once.
    auto run_differential_test() -> void
    {
        print(cerr, "difference presolver differential:");
        cerr << flush;

        const int n = 500;
        auto solve_it = [&](Config config) -> pair<Stats, DifferenceLogicStats> {
            auto stats = make_shared<DifferenceLogicStats>();
            Problem p;
            auto x = p.create_integer_variable(0_i, Integer(n), "x");
            auto y = p.create_integer_variable(0_i, Integer(n), "y");
            p.post(LinearLessThanEqual{WeightedSum{} + 1_i * x + -1_i * y, 0_i});
            p.post(LinearLessThanEqual{WeightedSum{} + 1_i * y + -1_i * x, -2_i});
            switch (config) {
                using enum Config;
            case NoPresolver: break;
            case Hybrid: p.add_presolver(DifferenceLogic{stats}); break;
            case DonorsDisabled: p.add_presolver(DifferenceLogic{stats}.disabling_lifted_donors()); break;
            }
            return {solve_with(p, SolveCallbacks{}), *stats};
        };

        auto [without, without_stats] = solve_it(Config::NoPresolver);
        auto [with, with_stats] = solve_it(Config::Hybrid);
        auto [disabled, disabled_stats] = solve_it(Config::DonorsDisabled);

        println(cerr, " propagations {} without, {} with, {} with donors off ({} solutions each)", without.propagations, with.propagations,
            disabled.propagations, without.solutions);

        if (0 != without.solutions || 0 != with.solutions || 0 != disabled.solutions)
            throw UnexpectedException{"difference presolver differential fixture is supposed to be unsatisfiable"};

        check_count("edges lifted", 2, with_stats.edges_lifted, "differential");
        check_count("edges lifted", 2, disabled_stats.edges_lifted, "differential");

        // A factor of ten is far inside the margin: the measured numbers are
        // around 500 against 3. Equality is what a no-op presolver would give.
        if (with.propagations * 10 >= without.propagations)
            throw UnexpectedException{"the difference-logic presolver made no measurable difference on the paper's Example 1: " +
                to_string(without.propagations) + " propagations without it against " + to_string(with.propagations) +
                " with it, where the global propagator should refute the negative cycle in one step." + detection_is_broken};

        if (disabled.propagations >= with.propagations)
            throw UnexpectedException{"disabling the donors did not reduce propagations on the paper's Example 1: " + to_string(with.propagations) +
                " with them against " + to_string(disabled.propagations) + " without"};
    }
}

auto main(int argc, char * argv[]) -> int
{
    establish_and_announce_seed(argc, argv);

    if (argc < 2)
        throw UnimplementedException{};

    string mode{argv[1]};

    if (mode == "detection") {
        run_detection_tests();
        run_differential_test();
    }
    else if (mode == "equivalence")
        run_equivalence_tests(false);
    else if (mode == "proofs") {
        if (! can_run_veripb()) {
            println(cerr, "veripb not available, skipping");
            return EXIT_SUCCESS;
        }
        run_equivalence_tests(true);
    }
    else if (mode == "tripwire")
        run_tripwire_tests();
    else if (mode == "opb")
        run_opb_tests();
    else
        throw UnimplementedException{};

    return EXIT_SUCCESS;
}
