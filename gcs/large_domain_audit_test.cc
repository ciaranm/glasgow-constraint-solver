/* The large-domain audit lane: issue #833.
 *
 * Every constraint class is posted once over a deliberately wide domain, then
 * installed and propagated at the root and nowhere else. The question this asks
 * is not "does it get the right answer" -- the other tests do that -- but "does
 * the amount of work it does depend on how *wide* a variable's domain is". A
 * build with -DGCS_LARGE_DOMAIN_GUARD=ON turns that dependence into a
 * LargeDomainGuardTripped, so the answer is a deterministic pass or fail rather
 * than a wedged core or a bad_alloc.
 *
 * Each row carries the outcome we currently expect, so this lane is green from
 * the day it lands and each later piece of #833 flips rows rather than
 * introducing failures. The three outcomes say different things:
 *
 *   Clean           -- the constraint has a position where a wide domain is
 *                      meaningful, and it survives one.
 *   KnownTrip       -- likewise, and it does not. This is the work #833 is
 *                      about, and the comment on the row says which hazard.
 *   HazardNotReached -- the source has a per-value site, but this probe does
 *                      not reach it: the site is behind a condition (a fixed
 *                      count, a domain with holes, a rule that only fires
 *                      deeper in search) that a one-shot root probe does not
 *                      meet. Asserted to survive, because that is what it does,
 *                      and labelled so nobody reads it as a clean bill of
 *                      health. Turning one of these into a Clean or a KnownTrip
 *                      means building a sharper probe, and is tracked as a gap.
 *   NoWidePosition  -- no variable this constraint takes can meaningfully be
 *                      wide: successor variables index an array, Boolean
 *                      variables are {0,1}. Probed at its widest legal domain
 *                      and required to be clean, but a pass here is a weaker
 *                      statement than a Clean, and the label records that so a
 *                      reader does not mistake structural immunity for a
 *                      fallback that works.
 *
 * With the guard off this file still builds and runs, and every probe passes
 * trivially without the guard's checks -- so it also serves as a cheap "does
 * every constraint install and propagate at the root at all" smoke test.
 * Registered as a ctest case only when the guard is on; see gcs/CMakeLists.txt.
 */

#include <gcs/gcs.hh>

#include <gcs/constraints/all_different.hh>
#include <gcs/constraints/at_most_one.hh>
#include <gcs/constraints/lex_smart_table.hh>
#include <gcs/constraints/table.hh>

#include <gcs/constraints/all_different/all_different_except.hh>
#include <gcs/constraints/all_different/symmetric_all_different.hh>
#include <gcs/constraints/circuit/subcircuit.hh>
#include <gcs/constraints/power/power_table.hh>
#include <gcs/constraints/regular/regular_bacchus.hh>
#include <gcs/constraints/regular/regular_legacy.hh>
#include <gcs/constraints/sort/arg_sort.hh>
#include <gcs/constraints/table/negative_table.hh>

#include <gcs/innards/large_domain_guard.hh>

#include <catch2/catch_test_macros.hpp>

#include <version>

#if defined(__cpp_lib_print) && defined(__cpp_lib_format)
#include <format>
#include <print>
using std::format;
using std::println;
#else
#include <fmt/core.h>
using fmt::format;
using fmt::println;
#endif

#include <exception>
#include <filesystem>
#include <fstream>
#include <functional>
#include <new>
#include <string>
#include <vector>

using namespace gcs;
using namespace gcs::innards;

using std::function;
using std::string;
using std::vector;

namespace
{
    // The probes' wide position is 0..probe_width. The audit runs at 10^9: wide
    // enough that any per-value work is hopeless, and the width the issue's
    // MiniZinc probes used, so the two sets of numbers are comparable. The proof
    // survey below re-runs the same probes at two much smaller widths, because a
    // proof can only be measured where it can actually be written.
    const auto wide_lo = 0_i;
    auto probe_width = 1000000000_i;

    enum class Expect
    {
        Clean,
        KnownTrip,
        NoWidePosition,
        HazardNotReached
    };

    struct Result
    {
        bool tripped = false;
        bool broken = false; ///< the probe itself failed to run, so it says nothing
        string detail = {};
    };

    /* Install and propagate at the root, and nowhere else.
     *
     * Both callbacks return false, which stops the search at the first node
     * whichever way that node goes: `trace` runs once root propagation has
     * produced something to branch on, and `solution` runs instead if root
     * propagation happened to fix everything. Neither is reached until root
     * propagation has finished, so a constraint that never finishes propagating
     * is exactly what this catches. Constraints are installed lazily by
     * Problem::create_propagators, so an install-time hazard -- which is most of
     * them -- is inside this call too, not inside build().
     */
    auto probe(const function<auto(Problem &)->void> & build) -> Result
    {
        try {
            Problem problem;
            build(problem);
            solve_with(problem,
                SolveCallbacks{.solution = [](const CurrentState &) { return false; },
                    .trace = [](const CurrentState &) { return false; },
                    .stats_report = silent_stats_report()});
            return {false, false, {}};
        }
        catch (const LargeDomainGuardTripped & e) {
            return {true, false, e.what()};
        }
        catch (const std::bad_alloc &) {
            // An allocation the guard does not cover. Still a trip as far as
            // this lane is concerned, and worth a distinct message because it
            // means there is a hazard site with no check on it yet.
            return {true, false, "std::bad_alloc, at a site the guard does not check"};
        }
        catch (const std::exception & e) {
            // A probe that cannot be posted or solved says nothing about the
            // constraint, so it is its own outcome rather than a pass or a
            // fail: one badly-built probe must not truncate the audit.
            return {false, true, e.what()};
        }
    }

    struct Probe
    {
        string name;
        Expect expect;
        function<auto(Problem &)->void> build;
    };

    auto wide_var(Problem & p) -> IntegerVariableID
    {
        return p.create_integer_variable(wide_lo, probe_width);
    }

    auto wide(Problem & p, int n) -> vector<IntegerVariableID>
    {
        vector<IntegerVariableID> result;
        for (int i = 0; i < n; ++i)
            result.push_back(wide_var(p));
        return result;
    }

    auto narrow(Problem & p, int n, Integer lo, Integer hi) -> vector<IntegerVariableID>
    {
        vector<IntegerVariableID> result;
        for (int i = 0; i < n; ++i)
            result.push_back(p.create_integer_variable(lo, hi));
        return result;
    }

    auto all_probes() -> vector<Probe>
    {
        vector<Probe> probes;
        auto add = [&](string name, Expect expect, function<auto(Problem &)->void> build) {
            probes.push_back(Probe{move(name), expect, move(build)});
        };

        // --- Arithmetic. These are the six that already implement the policy
        // #833 asks for, as consistency::Auto: tabulate within a budget, else BC.
        add("Abs", Expect::Clean, [](Problem & p) {
            auto v = wide(p, 2);
            p.post(Abs{v[0], v[1]});
        });
        add("Plus", Expect::Clean, [](Problem & p) {
            auto v = wide(p, 3);
            p.post(Plus{v[0], v[1], v[2]});
        });
        add("Minus", Expect::Clean, [](Problem & p) {
            auto v = wide(p, 3);
            p.post(Minus{v[0], v[1], v[2]});
        });
        add("Multiply", Expect::Clean, [](Problem & p) {
            auto v = wide(p, 3);
            p.post(Multiply{v[0], v[1], v[2]});
        });
        add("Divide", Expect::Clean, [](Problem & p) {
            auto v = wide(p, 3);
            p.post(Divide{v[0], v[1], v[2]});
        });
        add("Modulus", Expect::Clean, [](Problem & p) {
            auto v = wide(p, 3);
            p.post(Modulus{v[0], v[1], v[2]});
        });
        add("Power", Expect::KnownTrip, [](Problem & p) { // H2: reaches PowerTable's product enumeration
            auto v = wide(p, 3);
            p.post(Power{v[0], p.create_integer_variable(0_i, 3_i), v[2]});
        });
        add("PowerTable", Expect::KnownTrip, [](Problem & p) {
            // H2: PowerTable::prepare enumerates the product of two domains.
            auto v = wide(p, 3);
            p.post(PowerTable{v[0], p.create_integer_variable(0_i, 3_i), v[2]});
        });

        // --- Comparison and equality: bounds reasoning throughout.
        add("LessThan", Expect::Clean, [](Problem & p) {
            auto v = wide(p, 2);
            p.post(LessThan{v[0], v[1]});
        });
        add("GreaterThan", Expect::Clean, [](Problem & p) {
            auto v = wide(p, 2);
            p.post(GreaterThan{v[0], v[1]});
        });
        add("ReifiedCompareLessThanOrMaybeEqual", Expect::Clean, [](Problem & p) {
            auto v = wide(p, 2);
            auto r = p.create_integer_variable(0_i, 1_i);
            p.post(LessThanIf{v[0], v[1], r == 1_i});
        });
        add("Equals", Expect::Clean, [](Problem & p) {
            auto v = wide(p, 2);
            p.post(Equals{v[0], v[1]});
        });
        add("NotEquals", Expect::Clean, [](Problem & p) {
            auto v = wide(p, 2);
            p.post(NotEquals{v[0], v[1]});
        });
        add("ReifiedEquals", Expect::Clean, [](Problem & p) {
            auto v = wide(p, 2);
            auto r = p.create_integer_variable(0_i, 1_i);
            p.post(EqualsIff{v[0], v[1], r == 1_i});
        });

        // --- Linear.
        add("LinearEquality", Expect::Clean, [](Problem & p) {
            auto v = wide(p, 3);
            p.post(LinearEquality{WeightedSum{} + 1_i * v[0] + 1_i * v[1] + -1_i * v[2], 0_i});
        });
        add("ReifiedLinearEquality", Expect::Clean, [](Problem & p) {
            auto v = wide(p, 3);
            auto r = p.create_integer_variable(0_i, 1_i);
            p.post(LinearEqualityIff{WeightedSum{} + 1_i * v[0] + 1_i * v[1] + -1_i * v[2], 0_i, r == 1_i});
        });
        add("ReifiedLinearInequality", Expect::Clean, [](Problem & p) {
            auto v = wide(p, 3);
            p.post(LinearLessThanEqual{WeightedSum{} + 1_i * v[0] + 1_i * v[1] + -1_i * v[2], 0_i});
        });

        // --- Logical and parity: {0,1} variables only.
        add("And", Expect::NoWidePosition, [](Problem & p) {
            auto v = narrow(p, 3, 0_i, 1_i);
            p.post(And{v});
        });
        add("Or", Expect::NoWidePosition, [](Problem & p) {
            auto v = narrow(p, 3, 0_i, 1_i);
            p.post(Or{v});
        });
        add("ParityOdd", Expect::NoWidePosition, [](Problem & p) {
            auto v = narrow(p, 3, 0_i, 1_i);
            p.post(ParityOdd{v});
        });

        // --- All-different family.
        add("AllDifferent", Expect::KnownTrip, [](Problem & p) {
            // H2: AllDifferent::prepare builds the compressed value set under
            // GAC, with a linear find per value.
            p.post(AllDifferent{wide(p, 4)});
        });
        add("AllDifferent/VC", Expect::Clean, [](Problem & p) { p.post(AllDifferent{wide(p, 4)}.with_consistency(consistency::VC{})); });
        add("AllDifferentExcept", Expect::KnownTrip, [](Problem & p) { p.post(AllDifferentExcept{wide(p, 4), {0_i}}); });
        add("SymmetricAllDifferent", Expect::NoWidePosition, [](Problem & p) { p.post(SymmetricAllDifferent{narrow(p, 4, 0_i, 3_i)}); });
        add("AllEqual", Expect::Clean, [](Problem & p) { p.post(AllEqual{wide(p, 3)}); });
        add("AllEqual/holes", Expect::KnownTrip, [](Problem & p) {
            // all_equal.cc:114 prunes every variable to the intersection of all
            // the domains once any of them has holes. It takes the difference as
            // intervals (each_interval_minus) but then walks each interval a
            // value at a time, so it needs a *large* difference as well as a
            // hole. Bounds propagation runs first and would collapse a merely
            // narrow partner, so the hole has to be spread across the full width:
            // a two-value domain at the extremes leaves the whole middle of the
            // other variable to remove.
            auto holey = p.create_integer_variable(vector<Integer>{wide_lo, probe_width});
            auto full = wide_var(p);
            p.post(AllEqual{vector<IntegerVariableID>{holey, full}});
        });

        // --- Counting family.
        add("Among", Expect::KnownTrip, [](Problem & p) {
            // H1a: removes everything outside a small given value set, one value
            // at a time. That branch needs the count pinned -- with slack in it
            // the propagator has nothing to conclude -- so the count is fixed to
            // the whole scope, forcing every variable into the value set.
            auto v = wide(p, 3);
            p.post(Among{v, {1_i, 2_i}, p.create_integer_variable(3_i, 3_i)});
        });
        add("Count", Expect::KnownTrip, [](Problem & p) {
            // H1c: a genuine per-value support scan over the value variable.
            auto v = wide(p, 3);
            p.post(Count{v, v[0], p.create_integer_variable(0_i, 3_i)});
        });
        add("NValue", Expect::KnownTrip, [](Problem & p) {
            // H2 in prepare, and H2' in the encoding: one proof flag per value
            // of the union of the domains.
            auto v = wide(p, 3);
            p.post(NValue{p.create_integer_variable(1_i, 3_i), v});
        });
        add("AtMostOne", Expect::KnownTrip, [](Problem & p) {
            // The value variable has to be distinct from the scope: an aliased
            // one is rejected at post time, so it would probe nothing.
            auto v = wide(p, 3);
            p.post(AtMostOne{v, wide_var(p)});
        });
        add("AtMostOneSmartTable", Expect::KnownTrip, [](Problem & p) {
            auto v = wide(p, 3);
            p.post(AtMostOneSmartTable{v, wide_var(p)});
        });
        add("GlobalCardinality", Expect::KnownTrip, [](Problem & p) {
            // The counterexample to "just default to BC": this already defaults
            // to consistency::BC and still enumerates values. Reaching that needs
            // the just-met-demand branch (bounds_global_cardinality.cc:127), where
            // the number of variables that *can* take a cover value equals that
            // value's count lower bound -- so each is forced to it by removing
            // every other value one at a time. Three variables, one cover value,
            // and a count pinned at three does it.
            auto v = wide(p, 3);
            p.post(GlobalCardinality{v, {1_i}, {p.create_integer_variable(3_i, 3_i)}});
        });
        add("In", Expect::KnownTrip, [](Problem & p) {
            auto v = wide(p, 1);
            p.post(In{v[0], vector<Integer>{1_i, 2_i, 3_i}});
        });
        add("ValuePrecede", Expect::Clean, [](Problem & p) { p.post(ValuePrecede{1_i, 2_i, wide(p, 4)}); });
        add("SeqPrecedeChain", Expect::Clean, [](Problem & p) { p.post(SeqPrecedeChain{narrow(p, 4, 0_i, 3_i)}); });

        // --- Min / max / element.
        add("ArrayMinMax", Expect::KnownTrip, [](Problem & p) {
            // H1b (a missing hull bound) and H1a (the union scan) at once.
            auto v = wide(p, 4);
            p.post(ArrayMax{vector<IntegerVariableID>{v[0], v[1], v[2]}, v[3]});
        });
        add("Element", Expect::KnownTrip, [](Problem & p) {
            // The array entries have to be *narrow* for this to bite. The GAC
            // sweep erases each entry's domain from the result's still-unsupported
            // set (element.cc:583), so a wide entry erases the lot in one
            // erase_range and leaves nothing, while a narrow one leaves the rest
            // of the result's domain to be walked a value at a time
            // (element.cc:621).
            auto result = wide_var(p);
            p.post(Element{result, p.create_integer_variable(0_i, 2_i), narrow(p, 3, 1_i, 3_i)});
        });
        add("Element/BC", Expect::Clean, [](Problem & p) {
            // The same instance as the GAC probe above, so the pair is
            // comparable: the weaker arm is what makes it clean, not an easier
            // instance.
            auto result = wide_var(p);
            p.post(Element{result, p.create_integer_variable(0_i, 2_i), narrow(p, 3, 1_i, 3_i)}.with_consistency(consistency::BC{}));
        });

        // --- Ordering.
        add("IncreasingChain", Expect::Clean, [](Problem & p) { p.post(Increasing{wide(p, 4)}); });
        add("LexCompareGreaterThanOrMaybeEqual", Expect::Clean, [](Problem & p) {
            auto a = wide(p, 3), b = wide(p, 3);
            p.post(LexGreaterEqual{a, b});
        });
        add("LexSmartTable", Expect::KnownTrip, [](Problem & p) { // H1c: the smart-table encoding walks values
            auto a = wide(p, 3), b = wide(p, 3);
            p.post(LexSmartTable{a, b});
        });
        add("Sort", Expect::Clean, [](Problem & p) {
            auto x = wide(p, 3), y = wide(p, 3);
            p.post(Sort{x, y});
        });
        add("ArgSort", Expect::Clean, [](Problem & p) {
            auto x = wide(p, 3);
            p.post(ArgSort{x, narrow(p, 3, 0_i, 2_i)});
        });

        // --- Extensional.
        add("Table", Expect::KnownTrip, [](Problem & p) {
            // H3: the residue rows are sized by the variable's bounds rather
            // than by the table's own value range.
            auto v = wide(p, 3);
            SimpleTuples tuples{{1_i, 2_i, 3_i}, {4_i, 5_i, 6_i}};
            p.post(Table{v, tuples});
        });
        add("NegativeTable", Expect::Clean, [](Problem & p) {
            // Genuinely clean rather than merely unreached: it is watched-literal
            // over tuples and never iterates a domain, so it takes none of the
            // residue path the positive table dies in.
            auto v = wide(p, 3);
            SimpleTuples tuples{{1_i, 2_i, 3_i}, {4_i, 5_i, 6_i}};
            p.post(NegativeTable{v, tuples});
        });
        add("SmartTable", Expect::KnownTrip, [](Problem & p) {
            auto v = wide(p, 2);
            // Built a step at a time rather than from a nested braced list. GCC
            // cannot see that a SmartEntry variant's inactive alternative is
            // never destroyed, and reports a maybe-uninitialized vector<Integer>
            // inside the variant's destructor -- which the -Werror CI lane turns
            // into a build failure. This is the spelling the smart_table tests
            // already use.
            vector<SmartEntry> tuple;
            tuple.push_back(SmartTable::equals(v[0], v[1]));
            SmartTuples tuples;
            tuples.push_back(move(tuple));
            p.post(SmartTable{v, tuples});
        });

        // --- Automata. The alphabet is given by the automaton, so the hazard is
        // the variables' own width rather than the number of states.
        add("Regular", Expect::KnownTrip, [](Problem & p) {
            auto v = wide(p, 3);
            p.post(Regular{v, 2, {{{1_i, 1L}}, {{1_i, 1L}}, {{1_i, 1L}}}, {1L}});
        });
        add("RegularLegacy", Expect::KnownTrip, [](Problem & p) {
            auto v = wide(p, 3);
            p.post(RegularLegacy{v, 2, {{{1_i, 1L}}, {{1_i, 1L}}, {{1_i, 1L}}}, {1L}});
        });
        add("RegularBacchus", Expect::KnownTrip, [](Problem & p) {
            auto v = wide(p, 3);
            p.post(RegularBacchus{v, 2, {{{1_i, 1L}}, {{1_i, 1L}}, {{1_i, 1L}}}, {1L}});
        });
        add("MDD", Expect::KnownTrip, [](Problem & p) {
            auto v = wide(p, 2);
            p.post(MDD{v, {{{{1_i, 0L}}}, {{{1_i, 0L}}}}, {1L, 1L, 1L}, {0L}});
        });

        // --- Scheduling.
        add("Cumulative", Expect::KnownTrip, [](Problem & p) {
            // H3: the overload check's arrays are sized by the horizon.
            auto starts = wide(p, 3);
            p.post(Cumulative{starts, vector<Integer>{2_i, 2_i, 2_i}, vector<Integer>{1_i, 1_i, 1_i}, 2_i});
        });
        add("Disjunctive", Expect::KnownTrip, [](Problem & p) {
            auto starts = wide(p, 3);
            p.post(Disjunctive{starts, vector<Integer>{2_i, 2_i, 2_i}});
        });
        add("Disjunctive2D", Expect::Clean, [](Problem & p) {
            // Clean rather than unreached: it is pairwise, with no value loop and
            // no span-indexed array anywhere, and it installs no 1D Disjunctive
            // child that would have one.
            auto xs = wide(p, 2), ys = wide(p, 2);
            p.post(Disjunctive2D{xs, ys, narrow(p, 2, 1_i, 1_i), narrow(p, 2, 1_i, 1_i)});
        });

        // --- Packing and knapsack.
        add("BinPacking", Expect::Clean, [](Problem & p) {
            auto items = narrow(p, 3, 0_i, 1_i);
            p.post(BinPacking{items, vector<Integer>{1_i, 1_i, 1_i}, wide(p, 2)});
        });
        add("Knapsack", Expect::KnownTrip, [](Problem & p) {
            auto v = narrow(p, 3, 0_i, 1_i);
            auto totals = wide(p, 2);
            p.post(Knapsack{vector<Integer>{1_i, 2_i, 3_i}, vector<Integer>{1_i, 2_i, 3_i}, v, totals[0], totals[1]});
        });

        // --- Graph and permutation constraints. Every variable indexes into an
        // array of nodes, so none of them can meaningfully be wide.
        add("Circuit", Expect::NoWidePosition, [](Problem & p) { p.post(Circuit{narrow(p, 4, 0_i, 3_i)}); });
        add("SubCircuit", Expect::NoWidePosition, [](Problem & p) { p.post(SubCircuit{narrow(p, 4, 0_i, 3_i)}); });
        add("Inverse", Expect::NoWidePosition, [](Problem & p) { p.post(Inverse{narrow(p, 3, 0_i, 2_i), narrow(p, 3, 0_i, 2_i)}); });
        add("Subgraph", Expect::NoWidePosition, [](Problem & p) {
            auto ns = narrow(p, 3, 0_i, 1_i), es = narrow(p, 2, 0_i, 1_i);
            p.post(Subgraph{{{0, 1}, {1, 2}}, ns, es});
        });
        add("Tree", Expect::NoWidePosition, [](Problem & p) {
            auto r = p.create_integer_variable(0_i, 2_i);
            auto ns = narrow(p, 3, 0_i, 1_i), es = narrow(p, 2, 0_i, 1_i);
            p.post(Tree{{{0, 1}, {1, 2}}, r, ns, es});
        });
        add("DTree", Expect::NoWidePosition, [](Problem & p) {
            auto r = p.create_integer_variable(0_i, 2_i);
            auto ns = narrow(p, 3, 0_i, 1_i), es = narrow(p, 2, 0_i, 1_i);
            p.post(DTree{{{0, 1}, {1, 2}}, r, ns, es});
        });
        add("Path", Expect::NoWidePosition, [](Problem & p) {
            auto r = p.create_integer_variable(0_i, 2_i), t = p.create_integer_variable(0_i, 2_i);
            auto ns = narrow(p, 3, 0_i, 1_i), es = narrow(p, 2, 0_i, 1_i);
            p.post(Path{{{0, 1}, {1, 2}}, r, t, ns, es});
        });
        add("DPath", Expect::NoWidePosition, [](Problem & p) {
            auto r = p.create_integer_variable(0_i, 2_i), t = p.create_integer_variable(0_i, 2_i);
            auto ns = narrow(p, 3, 0_i, 1_i), es = narrow(p, 2, 0_i, 1_i);
            p.post(DPath{{{0, 1}, {1, 2}}, r, t, ns, es});
        });
        add("Reachable", Expect::NoWidePosition, [](Problem & p) {
            auto r = p.create_integer_variable(0_i, 2_i);
            auto ns = narrow(p, 3, 0_i, 1_i), es = narrow(p, 2, 0_i, 1_i);
            p.post(Reachable{{{0, 1}, {1, 2}}, r, ns, es});
        });
        add("DReachable", Expect::NoWidePosition, [](Problem & p) {
            auto r = p.create_integer_variable(0_i, 2_i);
            auto ns = narrow(p, 3, 0_i, 1_i), es = narrow(p, 2, 0_i, 1_i);
            p.post(DReachable{{{0, 1}, {1, 2}}, r, ns, es});
        });

        // --- The remaining two take a wide position and reason about it by bounds.
        add("DifferenceConstraints", Expect::Clean, [](Problem & p) {
            auto v = wide(p, 3);
            p.post(DifferenceConstraints{vector<DifferenceEdge>{{v[0], v[1], 0_i}, {v[1], v[2], 1_i}}});
        });
        add("Nogoods", Expect::Clean, [](Problem & p) {
            auto v = wide(p, 2);
            p.post(Nogoods{vector<Nogood>{{v[0] == 0_i, v[1] == 0_i}}});
        });

        add("MinDistance", Expect::Clean, [](Problem & p) {
            // Its per-value loops are all over the *position* variables, and
            // prepare() define_bound()s those to 0..n-1 of the distance matrix
            // (min_distance.cc:92-93), so they cannot be wide. The wide position
            // here is the objective z, which it reasons about by bounds.
            auto x = narrow(p, 2, 0_i, 1_i);
            auto z = wide_var(p);
            p.post(MinDistance{x, z, MinDistance::Matrix{{0_i, 1_i}, {1_i, 0_i}}});
        });

        return probes;
    }
}

namespace
{
    /* How does the *proof* grow with the domain's width?
     *
     * Out of scope for fixing: several of these have no viable fix today, and a
     * propagator is never weakened for proof size (propagator-performance.md).
     * The reason to measure it anyway is that the bad cases are evidence. Where
     * an inference's justification emits one near-identical step per value --
     * the same derivation with a different constant substituted in -- a VeriPB
     * feature that could express the family in one step would take an O(n) or
     * better bite out of it. This survey is where the candidates for such a
     * feature come from, so it reports OPB rows and proof steps separately: OPB
     * growth is an encoding that is per-value (a modelling problem, which no
     * checker feature helps), while proof-step growth at a *fixed* encoding is
     * the copy-paste that one might.
     *
     * Run it by hand, from a build with the guard OFF so that the wide probes
     * are not stopped before they write anything:
     *
     *     ./build/large_domain_audit_test "[.proofscaling]"
     */
    struct ProofSizes
    {
        long long opb_rows = 0;
        long long proof_steps = 0;
        bool measured = false;
        string detail = {};
    };

    auto count_lines(const std::filesystem::path & f) -> long long
    {
        std::ifstream in{f};
        if (! in)
            return 0;
        long long n = 0;
        for (string line; std::getline(in, line);)
            ++n;
        return n;
    }

    auto proof_sizes(const function<auto(Problem &)->void> & build, Integer width) -> ProofSizes
    {
        auto restore = probe_width;
        probe_width = width;
        ProofSizes result;
        auto names = ProofFileNames{"large_domain_proof_scaling"};
        try {
            Problem problem;
            build(problem);
            solve_with(problem,
                SolveCallbacks{.solution = [](const CurrentState &) { return false; },
                    .trace = [](const CurrentState &) { return false; },
                    .stats_report = silent_stats_report()},
                ProofOptions{names});
            result.measured = true;
        }
        catch (const std::exception & e) {
            // Whatever was written before it gave up is not a measurement, so
            // the row says so rather than reporting a truncated count.
            result.detail = e.what();
        }

        result.opb_rows = count_lines(names.opb_file);
        result.proof_steps = count_lines(names.proof_file);
        for (const auto & f : {names.opb_file, names.proof_file})
            std::filesystem::remove(f);
        for (const auto & f : {names.variables_map_file, names.s_expr_file})
            if (f)
                std::filesystem::remove(*f);

        probe_width = restore;
        return result;
    }

    auto growth(long long small, long long large) -> string
    {
        if (small <= 0)
            return "-";
        return format("{:.1f}x", static_cast<double>(large) / static_cast<double>(small));
    }

    auto describe(Expect e) -> string
    {
        switch (e) {
            using enum Expect;
        case Clean: return "Clean";
        case KnownTrip: return "KnownTrip";
        case NoWidePosition: return "NoWidePosition";
        case HazardNotReached: return "HazardNotReached";
        }
        return "?";
    }
}

TEST_CASE("Large domain audit")
{
    // The lane prints its table as it goes, so a run is the audit rather than
    // just a pass or a fail: dev_docs/large-domains.md quotes this output.
    println("{:<40} {:<16} {:<16} {}", "constraint", "expected", "actual", "");
    for (const auto & probe_case : all_probes()) {
        auto result = probe(probe_case.build);
        auto actual = result.broken ? "BROKEN PROBE" : (result.tripped ? "trips" : "survives");
        auto expected_trip = (probe_case.expect == Expect::KnownTrip);
        auto agrees = (! result.broken) && (result.tripped == expected_trip);
        println("{:<40} {:<16} {:<16} {}", probe_case.name, describe(probe_case.expect), actual, agrees ? "" : "<-- MISMATCH");

        INFO("constraint: " << probe_case.name);
        INFO("detail: " << result.detail);
        CHECK_FALSE(result.broken);
        // A KnownTrip that stops tripping is good news needing the table
        // updated, not a regression; a Clean that starts tripping is the
        // regression. Both are failures here on purpose: each row's outcome is
        // pinned, so the table cannot drift away from what the code does.
        CHECK(result.tripped == expected_trip);
    }
}

TEST_CASE("Large domain proof scaling", "[.proofscaling]")
{
    // Two widths a factor of ten apart, both small enough that every probe can
    // actually write a proof. A row whose count grows by about ten is linear in
    // the domain; one that barely moves does not depend on the width at all.
    const auto narrow_width = 1000_i, wider_width = 10000_i;

    println("{:<40} {:>10} {:>10} {:>8} {:>10} {:>10} {:>8}", "constraint", "opb@1e3", "opb@1e4", "growth", "pbp@1e3", "pbp@1e4", "growth");
    for (const auto & probe_case : all_probes()) {
        auto small = proof_sizes(probe_case.build, narrow_width);
        auto large = proof_sizes(probe_case.build, wider_width);
        if (! (small.measured && large.measured)) {
            println("{:<40} {:>10} {}", probe_case.name, "unmeasured", small.measured ? large.detail : small.detail);
            continue;
        }
        println("{:<40} {:>10} {:>10} {:>8} {:>10} {:>10} {:>8}", probe_case.name, small.opb_rows, large.opb_rows,
            growth(small.opb_rows, large.opb_rows), small.proof_steps, large.proof_steps, growth(small.proof_steps, large.proof_steps));
    }

    // A survey, not a gate: it asserts only that it got all the way through, so
    // that a constraint which cannot be proof-logged at all still shows up as a
    // row rather than ending the run.
    SUCCEED("proof scaling survey complete");
}
