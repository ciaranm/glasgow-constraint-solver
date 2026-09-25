/**
 * Instances a random fuzz campaign over the scheduling constraints found
 * Disjunctive writing a proof VeriPB rejects on, or throwing out of the
 * propagator with proofs on, each cut down by a greedy minimiser to what it
 * still needs and fixed alongside this file.
 *
 * Every one of them is a shape the rule-by-rule tests do not draw: a start that
 * is a view or a constant, or a length whose declared lower bound is zero. What
 * they have in common is a certificate built for one kind of task being handed
 * another. Each fixture enumerates every solution with a proof, checks them
 * against brute force, and verifies the proof; each was checked to fail without
 * its fix.
 *
 * The branching is part of the fixture. Most of these need a particular search
 * path to reach the node that goes wrong, and the tests' usual randomised
 * branching would find it only sometimes, so each fixture names a
 * deterministic heuristic.
 */

#include <gcs/constraints/disjunctive.hh>
#include <gcs/constraints/innards/constraints_test_utils.hh>
#include <gcs/constraints/linear.hh>
#include <gcs/problem.hh>
#include <gcs/search_heuristics.hh>
#include <gcs/solve.hh>

#include <cstdlib>
#include <iostream>
#include <optional>
#include <set>
#include <string>
#include <utility>
#include <vector>
#include <version>

#if defined(__cpp_lib_print) && defined(__cpp_lib_format)
#include <print>
#else
#include <fmt/core.h>
#include <fmt/ostream.h>
#endif

using std::cerr;
using std::make_optional;
using std::nullopt;
using std::optional;
using std::pair;
using std::set;
using std::string;
using std::vector;

#if defined(__cpp_lib_print) && defined(__cpp_lib_format)
using std::println;
#else
using fmt::println;
#endif

using namespace gcs;
using namespace gcs::test_innards;

namespace
{
    /// A variable by index, plus an offset: a plain variable, or a view of one.
    /// No index at all is the constant `offset`.
    struct Term
    {
        optional<int> var;
        int offset = 0;
    };

    auto var(int v, int offset = 0) -> Term
    {
        return Term{v, offset};
    }
    auto constant(int c) -> Term
    {
        return Term{nullopt, c};
    }

    struct Task
    {
        Term start, length;
    };

    /// `from + length <= to`.
    struct Precedence
    {
        Term from, length, to;
    };

    enum class Branching
    {
        Default,
        InOrderSmallestFirst,
        DomSmallestFirst
    };

    struct Fixture
    {
        string name;
        vector<pair<int, int>> domains;
        vector<Task> tasks;
        bool strict;
        DisjunctiveRules rules;
        Branching branching;
        vector<Precedence> precedences = {};
    };

    auto fail(const string & message) -> void
    {
        println(cerr, "disjunctive_regression_test: {}", message);
        exit(EXIT_FAILURE);
    }

    auto value(const Term & t, const vector<int> & vals) -> int
    {
        return t.var ? vals.at(*t.var) + t.offset : t.offset;
    }

    auto run(const Fixture & f, bool proofs) -> void
    {
        auto is_satisfying = [&](const vector<int> & vals) {
            for (size_t i = 0; i < f.tasks.size(); ++i)
                for (size_t j = i + 1; j < f.tasks.size(); ++j) {
                    auto si = value(f.tasks[i].start, vals), li = value(f.tasks[i].length, vals);
                    auto sj = value(f.tasks[j].start, vals), lj = value(f.tasks[j].length, vals);
                    if (! f.strict && (li == 0 || lj == 0))
                        continue;
                    if (! (si + li <= sj || sj + lj <= si))
                        return false;
                }
            for (const auto & p : f.precedences)
                if (value(p.from, vals) + value(p.length, vals) > value(p.to, vals))
                    return false;
            return true;
        };

        set<vector<int>> expected, actual;
        build_expected(expected, is_satisfying, f.domains);

        Problem p;
        vector<IntegerVariableID> vars;
        for (const auto & [lo, hi] : f.domains)
            vars.push_back(p.create_integer_variable(Integer{lo}, Integer{hi}));
        auto id = [&](const Term & t) -> IntegerVariableID {
            if (! t.var)
                return constant_variable(Integer{t.offset});
            return t.offset == 0 ? vars.at(*t.var) : vars.at(*t.var) + Integer{t.offset};
        };
        vector<IntegerVariableID> starts, lengths;
        for (const auto & t : f.tasks) {
            starts.push_back(id(t.start));
            lengths.push_back(id(t.length));
        }
        p.post(Disjunctive{starts, lengths}.with_strict(f.strict).with_rules(f.rules));
        for (const auto & prec : f.precedences)
            p.post(LinearLessThanEqual{WeightedSum{} + 1_i * id(prec.from) + 1_i * id(prec.length) + -1_i * id(prec.to), 0_i});

        SolveCallbacks callbacks{.solution = [&](const CurrentState & s) -> bool {
            vector<int> vals;
            for (const auto & v : vars)
                vals.push_back(static_cast<int>(s(v).raw_value));
            actual.insert(vals);
            return true;
        }};
        switch (f.branching) {
        case Branching::Default: break;
        case Branching::InOrderSmallestFirst: callbacks.branch = branch_with(variable_order::in_order(vars), value_order::smallest_first()); break;
        case Branching::DomSmallestFirst: callbacks.branch = branch_with(variable_order::dom(p), value_order::smallest_first()); break;
        }

        auto proof_name = "disjunctive_regression_" + f.name;
        solve_with(p, callbacks, proofs ? make_optional<ProofOptions>(ProofFileNames{proof_name}) : nullopt);

        if (actual != expected)
            fail(f.name + ": found " + std::to_string(actual.size()) + " solutions, expected " + std::to_string(expected.size()));
        if (proofs && ! run_veripb(proof_name + ".opb", proof_name + ".pbp"))
            fail(f.name + ": veripb rejected the proof");
        println(cerr, "disjunctive regression {}: {} solutions{}", f.name, actual.size(), proofs ? ", proof verified" : "");
    }

    /// In the order DisjunctiveRules declares them.
    auto rules(bool time_table, bool detectable, bool set_based, bool overload, bool edge_finding, bool edge_finding_lb, bool edge_finding_ub,
        bool nfnl, bool not_first, bool not_last) -> DisjunctiveRules
    {
        DisjunctiveRules r;
        r.time_table = time_table;
        r.detectable_precedences = detectable;
        r.detectable_precedences_set = set_based;
        r.overload = overload;
        r.edge_finding = edge_finding;
        r.edge_finding_lb = edge_finding_lb;
        r.edge_finding_ub = edge_finding_ub;
        r.not_first_not_last = nfnl;
        r.not_first = not_first;
        r.not_last = not_last;
        return r;
    }

    /// The published not-first / not-last rule over a Temporary vocabulary,
    /// as `examples/rcpsp` runs it.
    auto published_temporary_rules() -> DisjunctiveRules
    {
        DisjunctiveRules r;
        r.overload = true;
        r.not_first_not_last = true;
        r.not_first_not_last_published = true;
        r.overload_vocabulary_at = innards::ProofLevel::Temporary;
        return r;
    }
}

auto main(int argc, char * argv[]) -> int
{
    auto proofs = can_run_veripb();
    // `--only NAME` runs one fixture, which is how each was checked to fail
    // without its fix: a throw from one would otherwise hide the rest.
    optional<string> only;
    for (int a = 1; a + 1 < argc; ++a)
        if (string{argv[a]} == "--only")
            only = argv[a + 1];

    const vector<Fixture> fixtures{
        // Edge-finding cited a guarded window-energy row over the start's own
        // order literals for a task whose start is a view: it threw.
        Fixture{.name = "edge_finding_view_start",
            .domains = {{6, 8}, {1, 1}, {4, 8}},
            .tasks = {Task{var(0), constant(2)}, Task{var(1, 3), constant(4)}, Task{var(2), constant(4)}},
            .strict = true,
            .rules = rules(true, false, false, false, true, true, true, false, true, true),
            .branching = Branching::InOrderSmallestFirst},

        // The set-based detectable precedence counted a task at its current
        // length, and its certificate derived the energy row at the declared
        // one, which is zero: it threw.
        Fixture{.name = "set_precedence_length_from_zero",
            .domains = {{0, 1}, {3, 4}, {7, 8}, {3, 4}},
            .tasks = {Task{var(1), var(0)}, Task{var(2), constant(3)}, Task{var(3), constant(4)}},
            .strict = false,
            .rules = rules(true, true, true, true, true, true, true, true, false, true),
            .branching = Branching::InOrderSmallestFirst},

        // The same rule's successor, counted at the declared length and so no
        // longer detectable at it: the certificate's refutation had no degree.
        Fixture{.name = "set_precedence_successor",
            .domains = {{0, 1}, {5, 10}, {5, 8}, {1, 2}, {6, 9}, {2, 2}, {2, 2}, {10, 10}},
            .tasks = {Task{var(0), constant(1)}, Task{var(1), constant(3)}, Task{var(2), constant(4)}, Task{var(4), var(3)},
                Task{var(5), constant(3)}},
            .strict = false,
            .rules = rules(true, true, true, false, true, false, true, false, false, true),
            .branching = Branching::Default,
            .precedences = {Precedence{var(4), var(3), var(7)}}},

        // A constant start, among the overload check's and edge-finding's
        // candidates. The activity flags and bridges are over a start's order
        // literals, and a constant has none: it threw.
        Fixture{.name = "constant_start",
            .domains = {{5, 5}, {11, 11}, {13, 13}, {6, 11}, {4, 4}, {2, 2}, {3, 3}, {8, 8}, {1, 1}},
            .tasks = {Task{var(1), constant(2)}, Task{var(3), constant(2)}, Task{constant(8), constant(3)}},
            .strict = true,
            .rules = rules(false, true, false, true, true, true, true, true, false, false),
            .branching = Branching::InOrderSmallestFirst},

        // A constant start pushed by a time-table chain, which is a conflict:
        // the chain's pols named the constant's own order literal, and it has
        // none. It threw.
        Fixture{.name = "constant_start_push_chain",
            .domains = {{3, 3}, {1, 1}, {9, 13}, {4, 4}, {7, 7}, {7, 7}, {4, 4}},
            .tasks = {Task{var(2), constant(1)}, Task{var(4), constant(3)}, Task{constant(10), constant(3)}},
            .strict = false,
            .rules = rules(false, true, true, true, true, true, true, true, true, true),
            .branching = Branching::InOrderSmallestFirst},

        // A zero-length escape pinned false without a reason, for a task whose
        // length is declared from zero: the pin is not a model fact, and the
        // set-based precedence's clause cited it anyway.
        Fixture{.name = "zero_declared_escape",
            .domains = {{5, 6}, {0, 1}, {10, 11}, {6, 8}, {-1, -1}, {12, 12}, {3, 3}, {3, 3}, {2, 2}, {6, 9}},
            .tasks = {Task{var(2), var(1)}, Task{var(3), constant(3)}, Task{var(9), var(8)}},
            .strict = false,
            .rules = rules(true, true, true, false, false, true, false, false, true, true),
            .branching = Branching::InOrderSmallestFirst},

        // The published not-first / not-last rule's shortcut, for a contained
        // task with no room in the derived window, cited the cached escape
        // row. Under a Temporary vocabulary that row belonged to an earlier
        // firing and had been deleted (issue #1084).
        Fixture{.name = "published_shortcut_temporary_escape",
            .domains = {{4, 8}, {4, 8}, {3, 7}, {1, 2}, {1, 3}},
            .tasks = {Task{var(0), constant(2)}, Task{var(1), var(3)}, Task{var(2), var(4)}},
            .strict = false,
            .rules = published_temporary_rules(),
            .branching = Branching::Default},
    };

    for (const auto & f : fixtures) {
        if (only && *only != f.name)
            continue;
        run(f, false);
        if (proofs)
            run(f, true);
    }

    println(cerr, "disjunctive_regression_test: all fixtures pass");
    return EXIT_SUCCESS;
}
