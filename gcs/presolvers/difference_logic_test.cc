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
                                       "The most likely cause is a change to Constraint::clone() or to the Linear or\n"
                                       "Comparison class hierarchy, such that\n"
                                       "Problem::each_constraint_of_type<ReifiedLinearInequality>() (or\n"
                                       "<ReifiedCompareLessThanOrMaybeEqual>()) no longer yields the posted derived\n"
                                       "constraints (clone() currently returns the family base -- see PR #585).\n\n"
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

    // A half-reification condition, written as `vars[var] == value` so that the
    // condition variable is an ordinary member of the domain list and the
    // oracle enumerates both of its settings.
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
        for (const auto & e : edges) {
            if (e.cond && vals.at(e.cond->var) != e.cond->value)
                continue;
            if (operand_value(e.x, vals) - operand_value(e.y, vals) > e.d)
                return false;
        }
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

    // Which constraint an edge is written as. Every one of these spellings ends
    // up emitting the *same* OPB row -- `x - y <= d` under the bare @c[<id>]
    // label -- which is the whole reason the presolver can lift them all, and
    // which is what makes sweeping a fixture across the lot a real check rather
    // than five unrelated test sets: the lift and skip counts must come out
    // identical every time.
    enum class Donor
    {
        Linear,
        Le,
        Lt,
        Ge,
        Mixed
    };

    auto donor_name(Donor donor) -> string
    {
        switch (donor) {
            using enum Donor;
        case Linear: return "linear";
        case Le: return "less-equal";
        case Lt: return "less-than";
        case Ge: return "greater-equal";
        case Mixed: return "mixed";
        }
        throw UnimplementedException{};
    }

    auto all_donors() -> vector<Donor>
    {
        return {Donor::Linear, Donor::Le, Donor::Lt, Donor::Ge, Donor::Mixed};
    }

    // Post one edge in one donor's spelling. The comparison spellings put the
    // weight in a view on the larger side, which is exactly how a real model
    // writes `x <= y + d`, and (for the strict form) rely on `x - y <= d` being
    // `x < y + d + 1` over the integers.
    auto post_edge(Problem & p, const EdgeSpec & e, const vector<IntegerVariableID> & vars, Donor donor) -> void
    {
        auto x = operand_id(e.x, vars), y = operand_id(e.y, vars);
        optional<IntegerVariableCondition> cond;
        if (e.cond)
            cond = vars.at(e.cond->var) == Integer(e.cond->value);

        switch (donor) {
            using enum Donor;
        case Linear: {
            auto sum = WeightedSum{} + 1_i * x + -1_i * y;
            if (cond)
                p.post(LinearLessThanEqualIf{sum, Integer(e.d), *cond});
            else
                p.post(LinearLessThanEqual{sum, Integer(e.d)});
            return;
        }
        case Le:
            if (cond)
                p.post(LessThanEqualIf{x, y + Integer(e.d), *cond});
            else
                p.post(LessThanEqual{x, y + Integer(e.d)});
            return;
        case Lt:
            if (cond)
                p.post(LessThanIf{x, y + Integer(e.d + 1), *cond});
            else
                p.post(LessThan{x, y + Integer(e.d + 1)});
            return;
        case Ge:
            // GreaterThanEqual(a, b) normalises to left = b, right = a, so this
            // reads back as the same `x <= y + d` the Le case posts -- through
            // the swapped-operand constructor, which is the part that could
            // silently invert an edge.
            if (cond)
                p.post(GreaterThanEqualIf{y + Integer(e.d), x, *cond});
            else
                p.post(GreaterThanEqual{y + Integer(e.d), x});
            return;
        case Mixed: throw UnimplementedException{};
        }
        throw UnimplementedException{};
    }

    // Post the system one constraint per edge, in the requested spelling, and
    // attach the presolver as asked. Donor::Mixed alternates linear and
    // comparison donors so that both detection loops contribute to one graph,
    // which is where an edge-index or ordering mistake between them would show.
    auto build(Problem & p, const vector<pair<int, int>> & domains, const vector<EdgeSpec> & edges, Config config,
        const shared_ptr<DifferenceLogicStats> & stats, Donor donor) -> vector<IntegerVariableID>
    {
        vector<IntegerVariableID> vars;
        for (const auto & [lo, hi] : domains)
            vars.push_back(p.create_integer_variable(Integer(lo), Integer(hi)));

        for (size_t i = 0; i < edges.size(); ++i)
            post_edge(p, edges.at(i), vars, donor == Donor::Mixed ? (i % 2 == 0 ? Donor::Linear : Donor::Le) : donor);

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
    auto run_equivalence_test(bool proofs, Donor donor, const string & name, const vector<pair<int, int>> & domains, const vector<EdgeSpec> & edges,
        size_t expected_edges_lifted, size_t expected_half_reified) -> void
    {
        print(cerr, "difference presolver equivalence {} {} domains={} edges={}{}", donor_name(donor), name, domains, edges.size(),
            proofs ? " with proofs:" : ":");
        cerr << flush;

        set<tuple<vector<int>>> expected;
        build_expected(expected, [&](const vector<int> & vals) { return satisfied(vals, edges); }, domains);
        println(cerr, " expecting {} solutions", expected.size());

        for (auto config : {Config::NoPresolver, Config::Hybrid, Config::DonorsDisabled}) {
            auto stats = make_shared<DifferenceLogicStats>();
            Problem p;
            auto vars = build(p, domains, edges, config, stats, donor);

            set<tuple<vector<int>>> actual;
            // The presolver only reads and writes bounds, so bounds consistent,
            // not GAC.
            auto proof_name = proofs ? make_optional("difference_presolver_" + donor_name(donor) + "_" + name + "_" + config_name(config)) : nullopt;
            solve_for_tests(p, proof_name, actual, tuple{vars});
            check_results(proof_name, expected, actual);

            if (config != Config::NoPresolver) {
                check_count("edges lifted", expected_edges_lifted, stats->edges_lifted, name);
                check_count("half-reified edges lifted", expected_half_reified, stats->half_reified_edges_lifted, name);
                // Whichever spelling the fixture used, the same edges come out
                // of it -- so a comparison-donor sweep is only checking
                // anything at all if the *comparison* detection loop is what
                // produced them, and this is what says so. (Donor::Mixed's
                // split depends on which of the alternating edges happen to
                // skip, so it is pinned by an exact detection fixture instead
                // of restated here.)
                if (donor != Donor::Mixed)
                    check_count("edges lifted from comparison donors", donor == Donor::Linear ? 0 : expected_edges_lifted,
                        stats->comparison_edges_lifted, name);
            }
        }
    }

    // The tripwire. Disabling the donors' own propagators must not change the
    // search tree at all: the global propagator subsumes every unconditional
    // single-edge bound push, and disabling changes neither degrees nor
    // adjacency, so the branching heuristic sees an unchanged problem.
    // Solutions *and* recursions must match exactly. (Propagation counts of
    // course do not, and are the point of the option.)
    //
    // It is also what guards the rule that a *half-reified* donor is never
    // retired. Subsumption fails for those in one direction: a
    // LinearLessThanEqualIf also infers `!cond' from its own bounds, and the
    // global propagator makes no inference about a condition at all. Retire one
    // and the search grows, which shows up here as a recursion mismatch.
    auto run_tripwire_test(Donor donor, const string & name, const vector<pair<int, int>> & domains, const vector<EdgeSpec> & edges,
        size_t expected_edges_lifted, size_t expected_half_reified) -> void
    {
        print(cerr, "difference presolver tripwire {} {}:", donor_name(donor), name);
        cerr << flush;

        // Only unconditional donors are candidates for retirement, so a fixture
        // whose every lifted edge is conditional legitimately disables nothing.
        auto expect_disabling = expected_edges_lifted > expected_half_reified;

        Stats results[2];
        for (auto [index, config] : {pair{0, Config::Hybrid}, pair{1, Config::DonorsDisabled}}) {
            auto stats = make_shared<DifferenceLogicStats>();
            Problem p;
            static_cast<void>(build(p, domains, edges, config, stats, donor));
            results[index] = solve_with(p, SolveCallbacks{.solution = [&](const CurrentState &) -> bool { return true; }});
            if (config == Config::DonorsDisabled && expect_disabling && 0 == stats->donor_propagators_disabled)
                throw UnexpectedException{"the difference-logic presolver disabled no donor propagators on fixture '" + name +
                    "', so the tripwire compared two identical configurations." + detection_is_broken};
            if (config == Config::DonorsDisabled && ! expect_disabling && 0 != stats->donor_propagators_disabled)
                throw UnexpectedException{"the difference-logic presolver disabled " + to_string(stats->donor_propagators_disabled) +
                    " donor propagators on fixture '" + name +
                    "', every one of whose lifted edges is half-reified. A half-reified donor must never be retired: it also infers !cond from its "
                    "own bounds, and the global propagator infers nothing about a condition at all, so retiring one silently loses propagation."};
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
        size_t expected_half_reified = 0;
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
            {"negated_view", {{-3, 3}, {-3, 3}, {-3, 3}}, {{neg(0), v(1), 1}, {v(0), v(2), -1}, {v(2), v(1), -1}}, 2},
            // Half-reified donors. LinearLessThanEqualIf and LessThanEqualIf
            // both emit their row under HalfReifyOnConjunctionOf and label it
            // @c[<id>] with an empty role, exactly as the unconditional forms
            // do, so both are citable and both lift as a conditional edge (the
            // donor sweep runs each of these fixtures as each spelling in
            // turn). The last variable of each
            // fixture is the condition, and the oracle enumerates both of its
            // settings, so the false branch is checked as hard as the true one.
            {"reified_chain", {{0, 5}, {0, 5}, {0, 5}, {0, 1}}, {{v(0), v(1), -1, b(3)}, {v(1), v(2), -1, b(3)}}, 2, 2},
            {"reified_negcycle", {{0, 5}, {0, 5}, {0, 5}, {0, 1}, {0, 1}}, {{v(0), v(1), 0, b(3)}, {v(1), v(2), 0, b(4)}, {v(2), v(0), -1}}, 3, 2},
            // Mixed, with views, so the pol has to telescope in deview mode
            // *and* carry reification residuals.
            {"reified_views", {{0, 5}, {0, 5}, {0, 5}, {0, 1}}, {{v(0, 2), v(1), -1, b(3)}, {v(1, -1), v(2), 0}, {v(2), v(0), 1, b(3)}}, 3, 2},
            // The negative control: a conditional edge that is impossible over
            // these domains. Every assignment with the condition false is a
            // solution, so a presolver whose propagator ignored the condition
            // would lose all of them.
            {"reified_impossible", {{0, 4}, {0, 4}, {0, 1}}, {{v(0), v(1), -10, b(2)}, {v(1), v(0), 1}}, 2, 1},
            // The root simplification stage's one proof obligation, through the
            // presolver path: the conditional edge closes a cycle of weight -3
            // against the unconditional one, so the stage fixes the condition
            // false before search. The weight is chosen so the *donor* cannot
            // refute the condition from its own bounds --- over 0..10 an
            // x0 - x1 of -5 is perfectly possible --- so if the stage stops
            // working the condition is simply left to the search, which is a
            // completeness loss no proof would notice.
            {"reified_root_fix", {{0, 10}, {0, 10}, {0, 1}}, {{v(1), v(0), 2}, {v(0), v(1), -5, b(2)}}, 2, 1},
            // The same, with both ends of both edges behind offset views, so the
            // fixing pol only telescopes because it cites the donors' rows in
            // deview mode --- the same property view_negcycle_wide pins for the
            // refutation pol.
            {"reified_root_fix_views", {{0, 10}, {0, 10}, {0, 1}}, {{v(1, 1), v(0), 2}, {v(0, 2), v(1, -1), -5, b(2)}}, 2, 1}};
    }

    // Each fixture is run in every donor spelling. The lift counts are stated
    // once, in the corpus, because they must not depend on the spelling: an
    // `x <= y + d` and a `1*x + -1*y <= d` are the same difference constraint
    // and the same OPB row, and if a sweep ever produced different numbers,
    // that would be the bug.
    auto run_equivalence_tests(bool proofs) -> void
    {
        for (auto donor : all_donors())
            for (const auto & f : corpus())
                run_equivalence_test(proofs, donor, f.name, f.domains, f.edges, f.expected_edges_lifted, f.expected_half_reified);
    }

    auto run_tripwire_tests() -> void
    {
        for (auto donor : all_donors())
            for (const auto & f : corpus())
                run_tripwire_test(donor, f.name, f.domains, f.edges, f.expected_edges_lifted, f.expected_half_reified);
    }

    // Every donor shape, with the count it must land in. A donor migrating from
    // one bucket to another -- most dangerously from "lifted" to any of the
    // skips -- is caught here and nowhere else.
    auto run_detection_tests() -> void
    {
        auto check = [](const string & fixture, const DifferenceLogicStats & stats, const DifferenceLogicStats & expected) {
            println(cerr,
                "difference presolver detection {}: lifted {} ({} from comparisons, {} half-reified) over {} nodes, skipped {} not-two-terms, {} "
                "coefficients, {} reified, {} negated-view, {} degenerate",
                fixture, stats.edges_lifted, stats.comparison_edges_lifted, stats.half_reified_edges_lifted, stats.nodes, stats.skipped_not_two_terms,
                stats.skipped_coefficients, stats.skipped_reified, stats.skipped_negated_view, stats.skipped_degenerate);
            check_count("edges lifted", expected.edges_lifted, stats.edges_lifted, fixture);
            check_count("edges lifted from comparison donors", expected.comparison_edges_lifted, stats.comparison_edges_lifted, fixture);
            check_count("half-reified edges lifted", expected.half_reified_edges_lifted, stats.half_reified_edges_lifted, fixture);
            check_count("nodes", expected.nodes, stats.nodes, fixture);
            check_count("skipped: not two terms", expected.skipped_not_two_terms, stats.skipped_not_two_terms, fixture);
            check_count("skipped: coefficients", expected.skipped_coefficients, stats.skipped_coefficients, fixture);
            check_count("skipped: reified", expected.skipped_reified, stats.skipped_reified, fixture);
            check_count("skipped: negated view", expected.skipped_negated_view, stats.skipped_negated_view, fixture);
            check_count("skipped: degenerate", expected.skipped_degenerate, stats.skipped_degenerate, fixture);
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
            // Fully reified: the two halves are emitted under the roles r and f
            // rather than under the empty role, so neither is the row this
            // lifts, and both are counted rather than guessed at. (Half-reified
            // `If` donors *are* lifted, and are exercised in the corpus above
            // and in reified_donors below.)
            p.post(LinearLessThanEqualIff{WeightedSum{} + 1_i * x[1] + -1_i * x[2], -2_i, b == 1_i});
            p.post(LinearGreaterThanEqualIff{WeightedSum{} + 1_i * x[2] + -1_i * x[3], 2_i, b == 1_i});
            // A negated view.
            p.post(LinearLessThanEqual{WeightedSum{} + 1_i * (-x[0]) + -1_i * x[1], 1_i});
            // Aliasing, and a constant operand.
            p.post(LinearLessThanEqual{WeightedSum{} + 1_i * x[0] + -1_i * x[0], 0_i});
            p.post(LinearLessThanEqual{WeightedSum{} + 1_i * x[0] + -1_i * constant_variable(4_i), 1_i});
            // Comparisons, which are difference shaped and, since their OPB
            // rows carry an @c[<id>] label, citable: these two lift.
            p.post(LessThanEqual{x[2], x[3] + 2_i});
            p.post(GreaterThan{x[3], x[2]});
            // ... and one whose right-hand operand is a constant, which is a
            // plain bound rather than an edge.
            p.post(LessThan{x[2], constant_variable(5_i)});

            // The two real edges.
            p.post(LinearLessThanEqual{WeightedSum{} + 1_i * x[0] + -1_i * x[1], -1_i});
            p.post(LinearLessThanEqual{WeightedSum{} + 1_i * x[1] + -1_i * x[2], -1_i});

            p.add_presolver(DifferenceLogic{stats});
            solve_with(p, SolveCallbacks{.trace = [](const CurrentState &) -> bool { return false; }});
            check("every_skip", *stats,
                DifferenceLogicStats{.edges_lifted = 4,
                    .comparison_edges_lifted = 2,
                    .nodes = 4,
                    .propagator_installed = true,
                    .skipped_not_two_terms = 1,
                    .skipped_coefficients = 2,
                    .skipped_reified = 2,
                    .skipped_negated_view = 1,
                    .skipped_degenerate = 3});
        }

        // Every comparison spelling the presolver lifts, and every reason it
        // declines one. This is the fixture that fails if the comparison
        // detection loop stops working: the linear loop would still lift its
        // edges and the presolver would still look busy.
        {
            auto stats = make_shared<DifferenceLogicStats>();
            Problem p;
            auto x = p.create_integer_variable_vector(5, 0_i, 9_i, "x");
            auto b = p.create_integer_variable(0_i, 1_i, "b");

            // The four unconditional spellings, including both swapped-operand
            // constructors, and a view offset on either side.
            p.post(LessThanEqual{x[0], x[1] + 2_i});
            p.post(LessThan{x[1] + 1_i, x[2]});
            p.post(GreaterThanEqual{x[3], x[2]});
            p.post(GreaterThan{x[4], x[3] - 1_i});
            // Half-reified, which joins the graph as a conditional edge and
            // whose donor must therefore never be retired.
            p.post(LessThanEqualIf{x[0], x[4], b == 1_i});
            // Fully reified: the halves are labelled @c[<id>][r] and
            // @c[<id>][f], neither of which is the row cited, so counted.
            p.post(LessThanEqualIff{x[0], x[2], b == 1_i});
            // Stated negatively. Also a difference row, also citable, and also
            // deliberately not lifted --- see the comment in the presolver.
            p.post(ReifiedCompareLessThanOrMaybeEqual{x[0], x[1], reif::MustNotHold{}, true});
            // A negated view, which is not a difference constraint at all.
            p.post(LessThanEqual{-x[0], x[1]});
            // Aliasing (`0 <= 3`, vacuous) and a constant operand (a bound).
            p.post(LessThanEqual{x[0], x[0] + 3_i});
            p.post(LessThan{x[0], constant_variable(9_i)});

            p.add_presolver(DifferenceLogic{stats});
            solve_with(p, SolveCallbacks{.trace = [](const CurrentState &) -> bool { return false; }});
            check("comparison_donors", *stats,
                DifferenceLogicStats{.edges_lifted = 5,
                    .comparison_edges_lifted = 5,
                    .half_reified_edges_lifted = 1,
                    .nodes = 5,
                    .propagator_installed = true,
                    .skipped_reified = 2,
                    .skipped_negated_view = 1,
                    .skipped_degenerate = 2});
        }

        // Both detection loops feeding one graph. The comparison loop runs
        // second, so its edges land at higher posted indices than the linears';
        // the proof-line vector is indexed by that same number, and a mismatch
        // between the two would make the propagator cite the wrong donor's row.
        {
            auto stats = make_shared<DifferenceLogicStats>();
            Problem p;
            auto x = p.create_integer_variable_vector(4, 0_i, 9_i, "x");
            p.post(LinearLessThanEqual{WeightedSum{} + 1_i * x[0] + -1_i * x[1], -1_i});
            p.post(LessThanEqual{x[1] + 1_i, x[2]});
            p.post(LinearLessThanEqual{WeightedSum{} + 1_i * x[2] + -1_i * x[3], -1_i});
            p.add_presolver(DifferenceLogic{stats});
            solve_with(p, SolveCallbacks{.trace = [](const CurrentState &) -> bool { return false; }});
            check("mixed_donors", *stats,
                DifferenceLogicStats{.edges_lifted = 3, .comparison_edges_lifted = 1, .nodes = 4, .propagator_installed = true});
        }

        // Half-reified donors, in every shape the propagator distinguishes: two
        // real conditional edges, one conditional edge that is degenerate (and
        // so left to the donor, since its `!cond' is exactly what the donor
        // already infers), one conditional edge with a constant operand, and one
        // conditional negated view that must be refused just as the
        // unconditional one is.
        {
            auto stats = make_shared<DifferenceLogicStats>();
            Problem p;
            auto x = p.create_integer_variable_vector(4, 0_i, 6_i, "x");
            auto b = p.create_integer_variable(0_i, 1_i, "b");

            p.post(LinearLessThanEqualIf{WeightedSum{} + 1_i * x[0] + -1_i * x[1], -1_i, b == 1_i});
            p.post(LinearLessThanEqualIf{WeightedSum{} + 1_i * x[1] + -1_i * x[2], -1_i, b == 0_i});
            p.post(LinearLessThanEqualIf{WeightedSum{} + 1_i * x[0] + -1_i * x[0], -1_i, b == 1_i});
            p.post(LinearLessThanEqualIf{WeightedSum{} + 1_i * x[2] + -1_i * constant_variable(4_i), 1_i, b == 1_i});
            p.post(LinearLessThanEqualIf{WeightedSum{} + 1_i * (-x[0]) + -1_i * x[1], 1_i, b == 1_i});
            // One unconditional edge as well, so the mixture is what is
            // installed and the donor-disabling rule has something to bite on.
            p.post(LinearLessThanEqual{WeightedSum{} + 1_i * x[2] + -1_i * x[3], -1_i});

            p.add_presolver(DifferenceLogic{stats});
            solve_with(p, SolveCallbacks{.trace = [](const CurrentState &) -> bool { return false; }});
            check("reified_donors", *stats,
                DifferenceLogicStats{.edges_lifted = 3,
                    .half_reified_edges_lifted = 2,
                    .nodes = 4,
                    .propagator_installed = true,
                    .skipped_negated_view = 1,
                    .skipped_degenerate = 2});
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

    // How many rows of an OPB carry a constraint @label. Variable encodings are
    // @i[...] and proof flags @b[...] / @x[...], so this counts constraint rows
    // and nothing else.
    auto count_labelled_constraint_rows(const string & opb) -> size_t
    {
        size_t count = 0;
        for (size_t pos = 0; pos != string::npos;) {
            auto line_end = opb.find('\n', pos);
            if (opb.compare(pos, 3, "@c[") == 0)
                ++count;
            pos = line_end == string::npos ? string::npos : line_end + 1;
        }
        return count;
    }

    // Every row ReifiedCompareLessThanOrMaybeEqual emits must carry an @label.
    // The presolver's whole licence for lifting a comparison is that it can
    // cite the donor's row by name, and an unlabelled row cannot be cited at
    // all -- a `pol` would name something the OPB never defines.
    //
    // Checked here on the .opb text rather than left to the presolver's own
    // proofs, for two reasons. A form the presolver does not lift today
    // (MustNotHold, NotIf) would lose its label with nothing noticing, and a
    // regression that dropped the label from a form the presolver *does* lift
    // would only show up in a proof, in a model that both uses that form and
    // makes the propagator derive something from it.
    auto run_comparison_label_tests() -> void
    {
        auto rows_for = [](const string & basename, auto && post) -> size_t {
            Problem p;
            auto x = p.create_integer_variable_vector(2, 0_i, 5_i, "x");
            auto b = p.create_integer_variable(0_i, 1_i, "b");
            post(p, x, b);
            // No .scp: the MustNotHold and NotIf forms have no cake spelling
            // and s_expr() throws on them, which is precisely why their @label
            // is free to be the bare @c[<id>] --- and why the OPB is the only
            // place their labelling can be checked.
            ProofFileNames names{basename};
            names.s_expr_file = nullopt;
            static_cast<void>(
                solve_with(p, SolveCallbacks{.trace = [](const CurrentState &) -> bool { return false; }}, make_optional<ProofOptions>(names)));
            auto opb = read_file(basename + ".opb");
            for (auto ext : proof_file_extensions)
                std::remove((basename + ext).c_str());
            return count_labelled_constraint_rows(opb);
        };

        // One row per form, except the iff, whose two halves are @c[id][r] and
        // @c[id][f].
        auto check = [&](const string & form, size_t expected, size_t actual) {
            println(cerr, "difference presolver comparison labels: {} emits {} labelled row(s)", form, actual);
            if (expected != actual)
                throw UnexpectedException{"a " + form + " comparison emitted " + to_string(actual) + " @label'd OPB rows, expected " +
                    to_string(expected) +
                    ". Every row ReifiedCompareLessThanOrMaybeEqual emits must go out through "
                    "ProofModel::add_labelled_constraint, never the void-returning add_constraint: an unlabelled row cannot be cited, and the "
                    "difference-logic presolver lifts these constraints into a propagator whose pols cite exactly them by name. Fix "
                    "gcs/constraints/comparison/comparison.cc."};
        };

        check("must-hold", 1,
            rows_for("difference_presolver_label_hold", [](Problem & p, const auto & x, const auto &) { p.post(LessThanEqual{x[0], x[1]}); }));
        check("if", 1, rows_for("difference_presolver_label_if", [](Problem & p, const auto & x, const auto & b) {
            p.post(LessThanEqualIf{x[0], x[1], b == 1_i});
        }));
        check("must-not-hold", 1, rows_for("difference_presolver_label_not_hold", [](Problem & p, const auto & x, const auto &) {
            p.post(ReifiedCompareLessThanOrMaybeEqual{x[0], x[1], reif::MustNotHold{}, true});
        }));
        check("not-if", 1, rows_for("difference_presolver_label_not_if", [](Problem & p, const auto & x, const auto & b) {
            p.post(ReifiedCompareLessThanOrMaybeEqual{x[0], x[1], reif::NotIf{b == 1_i}, true});
        }));
        check("iff", 2, rows_for("difference_presolver_label_iff", [](Problem & p, const auto & x, const auto & b) {
            p.post(LessThanEqualIff{x[0], x[1], b == 1_i});
        }));
    }

    // The defining property: a presolver adds no OPB content. Presolver::run has
    // no ProofModel * at all, so this should be true by construction; check it
    // anyway, since it is the entire licence for lifting other people's
    // constraints after the model has been finalised.
    auto run_opb_tests() -> void
    {
        run_comparison_label_tests();

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

        // Positive case: a system the presolver does lift, once written as
        // linears and once as comparisons. The second is the one that says the
        // comparison donors add no OPB content of their own either --- they
        // must not, for exactly the same reason, and it is worth stating
        // separately because it is a different detection path.
        for (auto [what, post] : vector<pair<string, void (*)(Problem &)>>{//
                 {"linear",
                     [](Problem & p) {
                         auto x = p.create_integer_variable_vector(4, 0_i, 5_i, "x");
                         p.post(LinearLessThanEqual{WeightedSum{} + 1_i * x[0] + -1_i * x[1], -1_i});
                         p.post(LinearLessThanEqual{WeightedSum{} + 1_i * x[1] + -1_i * (x[2] + 1_i), -1_i});
                         p.post(LinearLessThanEqual{WeightedSum{} + 1_i * x[2] + -1_i * x[3], -1_i});
                     }},
                 {"comparison", [](Problem & p) {
                      auto x = p.create_integer_variable_vector(4, 0_i, 5_i, "x");
                      p.post(LessThan{x[0], x[1]});
                      p.post(LessThan{x[1], x[2] + 1_i});
                      p.post(LessThan{x[2], x[3]});
                  }}}) {
            auto [off_opb, off_pbp] = solve_and_read("difference_presolver_opb_" + what + "_off", Config::NoPresolver, post);
            auto [on_opb, on_pbp] = solve_and_read("difference_presolver_opb_" + what + "_on", Config::Hybrid, post);
            if (off_opb != on_opb)
                throw UnexpectedException{"the difference-logic presolver changed the .opb on the " + what +
                    " fixture. It must not: Presolver::run is handed no ProofModel, "
                    "and the whole design rests on the global propagator citing rows the donors already emitted"};
            if (off_pbp == on_pbp)
                throw UnexpectedException{"the difference-logic presolver left the .pbp byte-identical on the " + what +
                    " fixture, which it is supposed to lift three edges from, so it evidently propagated nothing." + detection_is_broken};
            println(cerr, "difference presolver opb: lifted {} fixture .opb identical ({} bytes), .pbp differs ({} vs {} bytes)", what,
                off_opb.size(), off_pbp.size(), on_pbp.size());
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

        // The root simplification stage, from the presolver entry point, adds no
        // OPB content either --- and it is the sub-step that most looks as though
        // it would want to. Fixing a Boolean at the root is a real inference, so
        // the .pbp gains a pol and a rup; dropping a redundant edge is a decision
        // about which propagator runs and leaves no trace anywhere. Neither may
        // touch the .opb: the model must always contain every posted constraint,
        // which is also what keeps workflow-2 chain verification intact, since
        // cake_pb_cp re-derives the .opb from the .scp and knows nothing about
        // our internal pruning.
        {
            auto simplification = make_shared<DifferenceSimplificationStats>();
            auto solve_with_simplification = [&](const string & basename, bool simplify) -> pair<string, string> {
                Problem p;
                auto x = p.create_integer_variable_vector(3, 0_i, 6_i, "x");
                auto b = p.create_integer_variable(0_i, 1_i, "b");
                // x0 - x1 <= 2 and x1 - x2 <= 2 unconditionally, so x0 - x2 <= 4,
                // which makes the posted x0 - x2 <= 5 redundant. Then
                // b -> x2 - x0 <= -5 closes a cycle of weight -1. The weight is
                // chosen so the donor's *own* propagator cannot refute b from
                // bounds --- over 0..6 an x0 - x2 of 5 is perfectly possible ---
                // because if it could, b would already be false by the time the
                // simplification stage looked and the fixture would be testing
                // nothing.
                p.post(LinearLessThanEqual{WeightedSum{} + 1_i * x[0] + -1_i * x[1], 2_i});
                p.post(LinearLessThanEqual{WeightedSum{} + 1_i * x[1] + -1_i * x[2], 2_i});
                p.post(LinearLessThanEqual{WeightedSum{} + 1_i * x[0] + -1_i * x[2], 5_i});
                p.post(LinearLessThanEqualIf{WeightedSum{} + 1_i * x[2] + -1_i * x[0], -5_i, b == 1_i});
                p.add_presolver(DifferenceLogic{}.simplifying_at_root(simplify).reporting_simplification_to(simplify ? simplification : nullptr));
                static_cast<void>(solve_with(p, SolveCallbacks{.solution = [](const CurrentState &) -> bool { return true; }},
                    make_optional<ProofOptions>(ProofFileNames{basename})));
                auto opb = read_file(basename + ".opb"), pbp = read_file(basename + ".pbp");
                for (auto ext : proof_file_extensions)
                    std::remove((basename + ext).c_str());
                return {opb, pbp};
            };

            auto [off_opb, off_pbp] = solve_with_simplification("difference_presolver_simplify_off", false);
            auto [on_opb, on_pbp] = solve_with_simplification("difference_presolver_simplify_on", true);
            if (off_opb != on_opb)
                throw UnexpectedException{"the difference-logic root simplification stage changed the .opb. It must not: every one of its "
                                          "conclusions is either internal to the propagator or a cutting-planes consequence of rows the model "
                                          "already contains, and Presolver::run is handed no ProofModel to add anything with"};
            if (! simplification->ran)
                throw UnexpectedException{"the root simplification stage did not run from the presolver entry point, so this fixture checked "
                                          "nothing at all"};
            if (0 == simplification->conditions_fixed || 0 == simplification->redundant_edges_removed)
                throw UnexpectedException{"the root simplification stage ran from the presolver entry point but fixed " +
                    to_string(simplification->conditions_fixed) + " conditions and removed " + to_string(simplification->redundant_edges_removed) +
                    " redundant edges, where this fixture is built so that both are nonzero. An OPB byte-diff that a no-op passes is not a test."};
            if (off_pbp == on_pbp)
                throw UnexpectedException{"the root simplification stage left the .pbp byte-identical on a fixture where it fixes a Boolean at the "
                                          "root, which it cannot do without emitting a pol and a rup"};
            println(cerr, "difference presolver opb: simplification .opb identical ({} bytes), .pbp differs ({} vs {} bytes), fixed {}, dropped {}",
                off_opb.size(), off_pbp.size(), on_pbp.size(), simplification->conditions_fixed, simplification->redundant_edges_removed);
        }
    }

    // The behavioural differential a no-op presolver cannot pass. This is the
    // paper's Example 1: x - y <= 0 and y - x <= -2 are trivially unsatisfiable,
    // but no individual constraint is violated by the initial domains, so
    // per-constraint propagation can only find it by crawling both bounds two
    // units at a time -- Theta(domain size) propagations. The global propagator
    // sums the two edges round the cycle and refutes at once.
    //
    // Run for each donor spelling: `x <= y` and `y <= x - 2` is the same
    // pathology written the way a scheduling model would write it, and it is
    // the shape the measurement in dev_docs/difference-logic.md uses.
    auto run_differential_test(Donor donor) -> void
    {
        print(cerr, "difference presolver differential {}:", donor_name(donor));
        cerr << flush;

        const int n = 500;
        auto solve_it = [&](Config config) -> pair<Stats, DifferenceLogicStats> {
            auto stats = make_shared<DifferenceLogicStats>();
            Problem p;
            auto x = p.create_integer_variable(0_i, Integer(n), "x");
            auto y = p.create_integer_variable(0_i, Integer(n), "y");
            vector<IntegerVariableID> vars{x, y};
            post_edge(p, EdgeSpec{v(0), v(1), 0}, vars, donor == Donor::Mixed ? Donor::Linear : donor);
            post_edge(p, EdgeSpec{v(1), v(0), -2}, vars, donor == Donor::Mixed ? Donor::Le : donor);
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
        if (donor != Donor::Linear && donor != Donor::Mixed)
            check_count("edges lifted from comparison donors", 2, with_stats.comparison_edges_lifted, "differential");

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
        for (auto donor : all_donors())
            run_differential_test(donor);
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
