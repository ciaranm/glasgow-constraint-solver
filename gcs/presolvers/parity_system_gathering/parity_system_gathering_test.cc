// Tests for the parity-system gathering presolver.
//
// READ THIS BEFORE "FIXING" A FAILURE HERE.
//
// This presolver adds no OPB content and changes no solution set. A version of
// it that silently gathered *nothing* -- because, say, ParityOdd stopped
// publishing its chain naming, so find_parity_chain returned nullopt for every
// donor, or because clone() started returning some other type so the
// enumeration matched nothing -- would pass:
//
//   * every solution-set equivalence check (a no-op presolver preserves them);
//   * every VeriPB run (there would be nothing new to verify).
//
// So the assertions on ParitySystemGatheringStats below, and the `strength`
// differentials, are the only things standing between a silent regression and
// shipping. If one of those fails, DETECTION IS BROKEN. Do not update the
// expected numbers to match what the code now does; fix
// gcs/presolvers/parity_system_gathering/parity_system_gathering.cc.
//
// There are two detection paths over two unrelated class hierarchies -- ParityOdd
// and ReifiedEquals -- and either can regress while the other keeps the presolver
// looking busy. That is what boolean_rows_offered is asserted for on every
// fixture, including where it is zero, and what the bool_bridge_unsat strength
// fixture exists for: it is unsatisfiable only once an equality has been used to
// identify two XOR rows' variables, so it separates "the Boolean family is
// counted" from "the Boolean family is doing work".

#include <gcs/constraints/equals.hh>
#include <gcs/constraints/innards/constraints_test_utils.hh>
#include <gcs/constraints/parity.hh>
#include <gcs/exception.hh>
#include <gcs/presolvers/parity_system_gathering.hh>
#include <gcs/problem.hh>
#include <gcs/solve.hh>

#include <cstdlib>
#include <iostream>
#include <memory>
#include <optional>
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
using std::make_shared;
using std::nullopt;
using std::pair;
using std::set;
using std::shared_ptr;
using std::size_t;
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
    const string detection_is_broken = " DETECTION IS BROKEN: this presolver is invisible except through its stats block, so"
                                       " do not update the expected number. Fix the presolver.";

    // Each row is a list of positions in the variable array; an odd number of
    // the variables at those positions must be non-zero.
    using Rows = vector<vector<int>>;

    // A Boolean Equals / NotEquals donor, which over {0, 1} operands is a 2-XOR.
    // `condition` set posts the `If` form instead, which is not liftable and is
    // here to check that it is refused and counted rather than lifted wrongly.
    struct BoolDonor
    {
        bool equality;
        int a, b;
        std::optional<int> condition = nullopt;
    };
    using BoolDonors = vector<BoolDonor>;

    enum class Config
    {
        NoPresolver,
        DonorsKept,
        DonorsRetired
    };

    auto config_name(Config c) -> string
    {
        switch (c) {
            using enum Config;
        case NoPresolver: return "none";
        case DonorsKept: return "kept";
        case DonorsRetired: return "retired";
        }
        throw NonExhaustiveSwitch{};
    }

    // What the presolver should report on a fixture. Every ParityOdd posted
    // falls into exactly one of rows_gathered and the two skip buckets a test
    // fixture can provoke, so these account for all of them.
    struct Expected
    {
        size_t rows_gathered;
        size_t atoms;
        size_t components_installed;
        size_t skipped_empty_row = 0;
        size_t skipped_alone_in_component = 0;
        size_t boolean_rows_offered = 0;
        size_t skipped_reified = 0;
        size_t skipped_wide_operands = 0;
    };

    auto check_count(const string & what, size_t expected, size_t actual, const string & fixture) -> void
    {
        if (expected != actual)
            throw UnexpectedException{"parity gathering fixture '" + fixture + "' reported " + to_string(actual) + " " + what + ", expected " +
                to_string(expected) + "." + detection_is_broken};
    }

    auto build(Problem & p, const vector<pair<int, int>> & domains, const Rows & rows, const BoolDonors & bools, Config config,
        const shared_ptr<ParitySystemGatheringStats> & stats) -> vector<IntegerVariableID>
    {
        vector<IntegerVariableID> vars;
        for (const auto & [lo, hi] : domains)
            vars.push_back(p.create_integer_variable(Integer(lo), Integer(hi)));

        for (const auto & row : rows) {
            vector<IntegerVariableID> operands;
            for (const auto & pos : row)
                operands.push_back(vars.at(pos));
            p.post(ParityOdd{operands});
        }

        for (const auto & b : bools) {
            if (b.condition) {
                if (b.equality)
                    p.post(EqualsIf{vars.at(b.a), vars.at(b.b), vars.at(*b.condition) != 0_i});
                else
                    p.post(NotEqualsIf{vars.at(b.a), vars.at(b.b), vars.at(*b.condition) != 0_i});
            }
            else if (b.equality)
                p.post(Equals{vars.at(b.a), vars.at(b.b)});
            else
                p.post(NotEquals{vars.at(b.a), vars.at(b.b)});
        }

        switch (config) {
            using enum Config;
        case NoPresolver: break;
        case DonorsKept: p.add_presolver(ParitySystemGathering{stats}.keeping_donor_propagators()); break;
        case DonorsRetired: p.add_presolver(ParitySystemGathering{stats}); break;
        }

        return vars;
    }

    auto satisfied(const vector<int> & vals, const Rows & rows, const BoolDonors & bools) -> bool
    {
        for (const auto & row : rows) {
            int trues = 0;
            for (const auto & pos : row)
                if (vals.at(pos) != 0)
                    ++trues;
            if (trues % 2 != 1)
                return false;
        }

        for (const auto & b : bools) {
            if (b.condition && 0 == vals.at(*b.condition))
                continue;
            if (b.equality != (vals.at(b.a) == vals.at(b.b)))
                return false;
        }

        return true;
    }

    // Solution-set equivalence across all three configurations, against an
    // independent oracle. Sound and complete in both directions: a presolver
    // that over-prunes loses a solution and one that is unsound gains one, and
    // no proof would catch either, since a proof only certifies what was
    // derived.
    auto run_equivalence_test(bool proofs, const string & name, const vector<pair<int, int>> & domains, const Rows & rows, const BoolDonors & bools,
        const Expected & expected_stats) -> void
    {
        print(
            cerr, "parity gathering equivalence {} domains={} rows={} bools={}{}", name, domains, rows, bools.size(), proofs ? " with proofs:" : ":");
        cerr << flush;

        set<tuple<vector<int>>> expected;
        build_expected(expected, [&](const vector<int> & vals) { return satisfied(vals, rows, bools); }, domains);
        println(cerr, " expecting {} solutions", expected.size());

        for (auto config : {Config::NoPresolver, Config::DonorsKept, Config::DonorsRetired}) {
            auto stats = make_shared<ParitySystemGatheringStats>();
            Problem p;
            auto vars = build(p, domains, rows, bools, config, stats);

            set<tuple<vector<int>>> actual;
            auto proof_name = proofs ? make_optional("parity_gathering_" + name + "_" + config_name(config)) : nullopt;
            solve_for_tests(p, proof_name, actual, tuple{vars});
            check_results(proof_name, expected, actual);

            if (config == Config::NoPresolver)
                continue;

            check_count("rows gathered", expected_stats.rows_gathered, stats->rows_gathered, name);
            check_count("atoms", expected_stats.atoms, stats->atoms, name);
            check_count("components installed", expected_stats.components_installed, stats->components_installed, name);
            check_count("empty rows skipped", expected_stats.skipped_empty_row, stats->skipped_empty_row, name);
            check_count("rows skipped as alone", expected_stats.skipped_alone_in_component, stats->skipped_alone_in_component, name);
            check_count("Boolean rows offered", expected_stats.boolean_rows_offered, stats->boolean_rows_offered, name);
            check_count("Boolean donors skipped as reified", expected_stats.skipped_reified, stats->skipped_reified, name);
            check_count("Boolean donors skipped for wide operands", expected_stats.skipped_wide_operands, stats->skipped_wide_operands, name);

            // Only ever non-zero with proofs off, and then it would mean the
            // chain lookup had stopped working -- which is the failure mode this
            // whole file exists to catch, so say so specifically.
            check_count("donors skipped for an uncitable chain", 0, stats->skipped_uncitable_chain, name);

            if (config == Config::DonorsRetired && expected_stats.components_installed != 0 && 0 == stats->donor_propagators_disabled)
                throw UnexpectedException{"parity gathering fixture '" + name + "' gathered " + to_string(stats->rows_gathered) +
                    " rows but retired no donor propagators." + detection_is_broken};
            if (config == Config::DonorsKept && 0 != stats->donor_propagators_disabled)
                throw UnexpectedException{"parity gathering fixture '" + name + "' retired donor propagators with keeping_donor_propagators() set"};
        }
    }

    // The tripwire. Retiring the donors' own propagators must not change the
    // search at all: the system propagator subsumes a single XOR's unit
    // propagation outright (a donor row with one literal left is a unit row of
    // the reduced system), and disabling a propagator changes neither degrees
    // nor adjacency, so the branching heuristic sees an unchanged problem.
    // Solutions *and* recursions must match exactly. Propagation counts of
    // course do not, and are the point of the option.
    auto run_tripwire_test(const string & name, const vector<pair<int, int>> & domains, const Rows & rows, const BoolDonors & bools) -> void
    {
        print(cerr, "parity gathering tripwire {}:", name);
        cerr << flush;

        Stats results[2];
        for (auto [index, config] : {pair{0, Config::DonorsKept}, pair{1, Config::DonorsRetired}}) {
            auto stats = make_shared<ParitySystemGatheringStats>();
            Problem p;
            static_cast<void>(build(p, domains, rows, bools, config, stats));
            results[index] = solve_with(p, SolveCallbacks{.solution = [&](const CurrentState &) -> bool { return true; }});
            if (config == Config::DonorsRetired && 0 == stats->donor_propagators_disabled)
                throw UnexpectedException{"parity gathering fixture '" + name +
                    "' retired no donor propagators, so the tripwire compared two identical configurations." + detection_is_broken};
        }

        println(cerr, " kept {} solutions / {} recursions / {} propagations, retired {} / {} / {}", results[0].solutions, results[0].recursions,
            results[0].propagations, results[1].solutions, results[1].recursions, results[1].propagations);

        if (results[0].solutions != results[1].solutions)
            throw UnexpectedException{"parity gathering fixture '" + name + "' found " + to_string(results[0].solutions) +
                " solutions with the donors kept but " + to_string(results[1].solutions) +
                " with them retired: the system propagator does not subsume them and retiring is unsound"};

        if (results[0].recursions != results[1].recursions)
            throw UnexpectedException{"parity gathering fixture '" + name + "' searched " + to_string(results[0].recursions) +
                " recursions with the donors kept but " + to_string(results[1].recursions) +
                " with them retired. Retiring changes neither degrees nor adjacency, so the tree must be identical node for node; it differing "
                "means the system propagator does not subsume a single XOR's unit propagation after all."};
    }

    // The strength differential. The other two tests would both pass for a
    // presolver that gathered the rows and then inferred nothing from them, so
    // this is where the point of the whole exercise gets checked: on a system
    // that is unsatisfiable while no single row of it conflicts, Gauss-Jordan
    // refutes it without searching and unit propagation cannot.
    auto run_strength_test(const string & name, const vector<pair<int, int>> & domains, const Rows & rows, const BoolDonors & bools) -> void
    {
        print(cerr, "parity gathering strength {}:", name);
        cerr << flush;

        Stats results[2];
        for (auto [index, config] : {pair{0, Config::NoPresolver}, pair{1, Config::DonorsRetired}}) {
            auto stats = make_shared<ParitySystemGatheringStats>();
            Problem p;
            static_cast<void>(build(p, domains, rows, bools, config, stats));
            results[index] = solve_with(p, SolveCallbacks{.solution = [&](const CurrentState &) -> bool { return true; }});
        }

        println(cerr, " no presolver {} solutions / {} recursions, gathered {} / {}", results[0].solutions, results[0].recursions,
            results[1].solutions, results[1].recursions);

        if (0 != results[0].solutions || 0 != results[1].solutions)
            throw UnexpectedException{"parity gathering strength fixture '" + name +
                "' is meant to be unsatisfiable, and is not: it cannot separate the two configurations."};

        if (results[1].recursions >= results[0].recursions)
            throw UnexpectedException{"parity gathering fixture '" + name + "' took " + to_string(results[1].recursions) +
                " recursions with the system gathered and " + to_string(results[0].recursions) +
                " without, so gathering bought no strength at all. The whole point is that the conjunction refutes what no single row does." +
                detection_is_broken};
    }
}

auto main(int, char *[]) -> int
{
    const vector<pair<int, int>> four_bits{{0, 1}, {0, 1}, {0, 1}, {0, 1}};
    const vector<pair<int, int>> three_bits{{0, 1}, {0, 1}, {0, 1}};
    const vector<pair<int, int>> six_bits{{0, 1}, {0, 1}, {0, 1}, {0, 1}, {0, 1}, {0, 1}};

    // Three rows over a cycle summing to the empty row with an odd right-hand
    // side: unsatisfiable, and no two of the three conflict, so nothing short of
    // the system sees it. This is the camouflage fixture, and the one the
    // strength differential runs on.
    const Rows camouflage{{0, 1}, {1, 2}, {0, 2}};

    for (bool proofs : {false, true}) {
        if (proofs && ! can_run_veripb())
            continue;

        // One component, every row sharing with the next.
        run_equivalence_test(
            proofs, "chain", four_bits, {{0, 1}, {1, 2}, {2, 3}}, {}, Expected{.rows_gathered = 3, .atoms = 4, .components_installed = 1});

        run_equivalence_test(proofs, "camouflage", three_bits, camouflage, {}, Expected{.rows_gathered = 3, .atoms = 3, .components_installed = 1});

        // Two components that share nothing: two propagators, not one over the
        // lot. Eliminating over rows that cannot inform each other is waste, and
        // a version that merged them would report one component here.
        run_equivalence_test(proofs, "two_components", six_bits, {{0, 1}, {1, 2}, {3, 4}, {4, 5}}, {},
            Expected{.rows_gathered = 4, .atoms = 6, .components_installed = 2});

        // A single row is left to its own ParityOdd: over one row the system
        // propagator computes exactly what it does, more slowly.
        run_equivalence_test(proofs, "singleton", three_bits, {{0, 1, 2}}, {},
            Expected{.rows_gathered = 0, .atoms = 0, .components_installed = 0, .skipped_alone_in_component = 1});

        // A row whose atoms all cancel is `x XOR x = 1`, which is false. It has
        // no atoms, so it shares none and is alone by construction -- and its
        // own propagator is what refutes it.
        run_equivalence_test(proofs, "all_cancel", three_bits, {{0, 0}, {1, 2}, {0, 1}}, {},
            Expected{.rows_gathered = 2, .atoms = 3, .components_installed = 1, .skipped_alone_in_component = 1});

        // An empty row asserts that zero is odd. Left to its own propagator, and
        // counted; the other two rows still form a system.
        run_equivalence_test(proofs, "empty_row", three_bits, {{}, {0, 1}, {1, 2}}, {},
            Expected{.rows_gathered = 2, .atoms = 3, .components_installed = 1, .skipped_empty_row = 1});

        // Wider domains: the atoms are `v != 0`, so only zero versus non-zero
        // matters, and a variable contributes one column however wide it is.
        run_equivalence_test(proofs, "wide_domains", {{0, 3}, {-2, 2}, {0, 1}}, {{0, 1}, {1, 2}}, {},
            Expected{.rows_gathered = 2, .atoms = 3, .components_installed = 1});

        // The Boolean family's whole point: without the NotEquals in the middle
        // these are two components of one row each, both left to their own
        // propagators. With it they are one system of three rows. A version that
        // gathered only ParityOdd would report zero rows gathered here.
        run_equivalence_test(proofs, "bool_bridge", four_bits, {{0, 1}, {2, 3}}, {BoolDonor{false, 1, 2}},
            Expected{.rows_gathered = 3, .atoms = 4, .components_installed = 1, .boolean_rows_offered = 1});

        // An equality, which is the *even* 2-XOR and so is lifted with one
        // literal negated. Getting that negation backwards would show up as a
        // solution-set mismatch, not merely a weaker system.
        run_equivalence_test(proofs, "bool_equals", three_bits, {{0, 1}}, {BoolDonor{true, 1, 2}},
            Expected{.rows_gathered = 2, .atoms = 3, .components_installed = 1, .boolean_rows_offered = 1});

        // Both together, and an equality between two variables the XOR rows
        // already mention -- so the row is redundant as a constraint while still
        // joining the components.
        run_equivalence_test(proofs, "bool_both", four_bits, {{0, 1}, {2, 3}}, {BoolDonor{true, 0, 2}, BoolDonor{false, 1, 3}},
            Expected{.rows_gathered = 4, .atoms = 4, .components_installed = 1, .boolean_rows_offered = 2});

        // An operand reaching outside {0, 1}: equality there says far more than
        // parity does, so lifting it would be unsound rather than weak.
        run_equivalence_test(proofs, "bool_wide_operand", {{0, 1}, {0, 1}, {0, 3}}, {{0, 1}}, {BoolDonor{true, 1, 2}},
            Expected{.rows_gathered = 0, .atoms = 0, .components_installed = 0, .skipped_alone_in_component = 1, .skipped_wide_operands = 1});

        // A half-reified equality is not a parity row until its condition is
        // decided. Refused and counted.
        run_equivalence_test(proofs, "bool_reified", four_bits, {{0, 1}}, {BoolDonor{true, 1, 2, make_optional(3)}},
            Expected{.rows_gathered = 0, .atoms = 0, .components_installed = 0, .skipped_alone_in_component = 1, .skipped_reified = 1});
    }

    run_tripwire_test("chain", four_bits, {{0, 1}, {1, 2}, {2, 3}}, {});
    run_tripwire_test("camouflage", three_bits, camouflage, {});
    run_tripwire_test("two_components", six_bits, {{0, 1}, {1, 2}, {3, 4}, {4, 5}}, {});
    run_tripwire_test("bool_bridge", four_bits, {{0, 1}, {2, 3}}, {BoolDonor{false, 1, 2}});

    run_strength_test("camouflage", three_bits, camouflage, {});

    // The Boolean family's own strength differential: two rows that conflict only
    // once the equality has been used to identify their variables. Neither row
    // nor the equality conflicts with either other alone.
    run_strength_test("bool_bridge_unsat", four_bits, {{0, 1}, {2, 3}}, {BoolDonor{true, 0, 2}, BoolDonor{false, 1, 3}});

    return EXIT_SUCCESS;
}
