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
            // Two bare wide variables never reach the interior pruning: the
            // image of v1's domain is then the whole of v2's, so
            // each_interval_minus yields nothing and both hole loops are
            // skipped. The two rows below are the ones that reach them.
            auto v = wide(p, 2);
            p.post(Abs{v[0], v[1]});
        });
        add("Abs/hole", Expect::Clean, [](Problem & p) {
            // The image loop, abs.cc. The removed values have to be a hole in
            // the *image* rather than merely outside v2's bounds, because bounds
            // propagation clips the latter first -- which is exactly what the
            // loop's clipped_lo / clipped_hi are for. So v1's image is {0, w}
            // and everything strictly between is left for the loop, which now
            // removes it as the one run it is.
            auto v1 = p.create_integer_variable(vector<Integer>{-probe_width, 0_i, probe_width});
            auto v2 = wide_var(p);
            p.post(Abs{v1, v2});
        });
        add("Abs/hole-preimage", Expect::Clean, [](Problem & p) {
            // The mirrored preimage loop, which the row above does not reach --
            // v2 contiguous makes its preimage contiguous, so that difference is
            // empty. Hole in v2 instead, and the two halves of v1 either side of
            // zero are what is left over: two runs, and two removals.
            auto v2 = p.create_integer_variable(vector<Integer>{0_i, probe_width});
            auto v1 = p.create_integer_variable(-probe_width, probe_width);
            p.post(Abs{v1, v2});
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
            // Wide *and non-overlapping*, because that is the only shape in which
            // the interesting rule fires. Two operands over the same wide interval
            // -- what this probe used to be -- always intersect, so
            // infer_cond_when_undecided returned StillUndecided and the no-overlap
            // reason walk this row exists to test was never reached: the same
            // "more extreme than necessary" mistake the probe-sharpening pass
            // corrected elsewhere, and the reason #864 went unnoticed here.
            //
            // The walk is not one of State's iterators, so before #864 was fixed
            // this probe still reported Clean: it cost 78 GB and 160 s and merely
            // had the RAM to finish. Its guard coverage is hand-added in
            // equals.cc, in the same way as Element's and AllEqual's.
            auto lo = p.create_integer_variable(wide_lo, probe_width / 2_i);
            auto hi = p.create_integer_variable(probe_width / 2_i + 1_i, probe_width);
            auto r = p.create_integer_variable(0_i, 1_i);
            p.post(EqualsIff{lo, hi, r == 1_i});
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
        add("AllEqual/holes", Expect::Clean, [](Problem & p) {
            // all_equal.cc:114 prunes every variable to the intersection of all
            // the domains once any of them has holes. It takes the difference as
            // intervals (each_interval_minus) but then walks each interval a
            // value at a time, so it needs a *large* difference as well as a
            // hole. Bounds propagation runs first and would collapse a merely
            // narrow partner, so the hole has to be spread across the full width:
            // a two-value domain at the extremes leaves the whole middle of the
            // other variable to remove -- which is now one range removal.
            //
            // Note this row used to trip on the `In` that create_integer_variable
            // posts to carve the hole, rather than on AllEqual at all. With that
            // fixed the row still trips, but now on the site the comment describes.
            auto holey = p.create_integer_variable(vector<Integer>{wide_lo, probe_width});
            auto full = wide_var(p);
            p.post(AllEqual{vector<IntegerVariableID>{holey, full}});
        });

        // --- Counting family.
        add("Among", Expect::Clean, [](Problem & p) {
            // Was H1a: it removed everything outside a small given value set one
            // value at a time. Now the complement of the value set goes in as
            // ranges, so a wide domain costs two removals. That branch needs the
            // count pinned -- with slack in it the propagator has nothing to
            // conclude -- so the count is fixed to the whole scope, forcing every
            // variable into the value set. The two values of interest sit at the
            // bottom, which leaves a range on each side of them and so exercises
            // both sides of the proof's per-value-of-interest case split.
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
        add("GlobalCardinality", Expect::Clean, [](Problem & p) {
            // Was the counterexample to "just default to BC": this already
            // defaults to consistency::BC and still enumerated values, so under
            // the governing rule it was a broken fallback arm rather than a
            // missing one. Reaching it needs the just-met-demand branch, where the
            // number of variables that *can* take a cover value equals that
            // value's count lower bound -- so each is forced to it. Three
            // variables, one cover value, and a count pinned at three does it.
            // Forcing a variable to a value is now two range removals.
            auto v = wide(p, 3);
            p.post(GlobalCardinality{v, {1_i}, {p.create_integer_variable(3_i, 3_i)}});
        });
        add("GlobalCardinality/hall", Expect::KnownTrip, [](Problem & p) {
            // The second per-value site, in part 2's Hall reasoning: when the
            // variables that can meet a hall set are exactly as many as the set
            // demands, each is pruned to the set by removing everything outside it
            // one value at a time. The probe above cannot reach this -- one cover
            // value means there is no multi-value hall to form -- so it needs its
            // own row rather than being covered by association.
            //
            // Not fixed with the other site because its justification is not
            // range-shaped: the pol builds an at-most-one over the hall set plus
            // the single removed value, so the removed value is named in the
            // derivation rather than merely concluded.
            auto v = wide(p, 2);
            p.post(GlobalCardinality{v, {1_i, 2_i}, {p.create_integer_variable(1_i, 1_i), p.create_integer_variable(1_i, 1_i)}});
        });
        add("GlobalCardinality/closed", Expect::Clean, [](Problem & p) {
            // The third per-value site, and the only one neither row above can
            // reach: with_closed() installs a propagator of its own, which used
            // to restrict every variable to the cover by walking its domain and
            // grouping the runs the cover does not contain, and now takes that
            // difference at interval level (#877). Nothing else in the lane
            // calls with_closed, in either arm.
            //
            // The default BC level on purpose. The closed propagator is
            // installed identically whichever level is chosen, so this row is
            // about that propagator alone; a GAC row would trip on the GAC arm's
            // own sites (#876) and say nothing about this one.
            //
            // The count is left as a range so that the closed restriction is
            // the only thing in the probe that can remove a value. Pinning it at
            // 2 reaches this site too -- checked, it trips before the fix and
            // survives after, exactly as this row does -- but it also puts the
            // bounds arm's just-met-demand branch within reach, and a row two
            // sites can satisfy says less about either.
            auto v = wide(p, 2);
            p.post(GlobalCardinality{v, {1_i}, {p.create_integer_variable(0_i, 2_i)}}.with_closed(true));
        });
        add("In", Expect::Clean, [](Problem & p) {
            // Its conclusions were always interval-level; what was per-value was
            // finding them, by walking the domain to group maximal runs. A merge
            // against the permitted set yields the same runs without the walk.
            //
            // This one is load-bearing beyond its own row: create_integer_variable
            // over a vector posts an In, so any probe that builds a holey variable
            // that way was tripping here first, whatever else it meant to test.
            auto v = wide(p, 1);
            p.post(In{v[0], vector<Integer>{1_i, 2_i, 3_i}});
        });
        add("In/vars", Expect::Clean, [](Problem & p) {
            // In's other two constructors take variables in the value list, and
            // with one of those non-constant the propagator takes a different
            // branch entirely -- the branch that was still walking dom(var) a
            // value at a time (#874). So the row above reported Clean for a
            // constraint one of whose three spellings tripped instantly, which
            // is what a row naming a probe rather than a constraint is for.
            //
            // Singleton *variables* rather than constants: prepare() folds a
            // ConstantIntegerVariableID into the value list, and this probe would
            // then be the row above again. What that leaves for step 1 is
            // everything strictly between them -- one run, and one removal.
            auto v = wide_var(p);
            auto bottom = p.create_integer_variable(wide_lo, wide_lo);
            auto top = p.create_integer_variable(probe_width, probe_width);
            p.post(In{v, vector<IntegerVariableID>{bottom, top}});
        });
        add("In/vars-single-support", Expect::Clean, [](Problem & p) {
            // Step 3, which the row above cannot reach: when exactly one source
            // still overlaps dom(var) and no constant does, that source has to
            // equal var, so everything it holds outside dom(var) comes off. Two
            // sources, then, one covering var and one sitting entirely above it:
            // the second is not a supporter, and the first loses its top half --
            // as the one range it is, where it used to go a value at a time.
            auto v = p.create_integer_variable(wide_lo, probe_width / 2_i);
            auto covers = wide_var(p);
            auto above = p.create_integer_variable(probe_width / 2_i + 1_i, probe_width);
            p.post(In{v, vector<IntegerVariableID>{covers, above}});
        });
        add("ValuePrecede", Expect::Clean, [](Problem & p) { p.post(ValuePrecede{1_i, 2_i, wide(p, 4)}); });
        add("SeqPrecedeChain", Expect::Clean, [](Problem & p) { p.post(SeqPrecedeChain{narrow(p, 4, 0_i, 3_i)}); });

        // --- Min / max / element.
        add("ArrayMinMax", Expect::KnownTrip, [](Problem & p) {
            // H1b (a missing hull bound) and H1a (the union scan) at once.
            auto v = wide(p, 4);
            p.post(ArrayMax{vector<IntegerVariableID>{v[0], v[1], v[2]}, v[3]});
        });
        add("Element", Expect::Clean, [](Problem & p) {
            // The array entries have to be *narrow* for this to bite. The GAC
            // sweep erases each entry's domain from the result's still-unsupported
            // set, so a wide entry erases the lot in one erase_range and leaves
            // nothing, while a narrow one leaves the rest of the result's domain
            // behind. That remainder used to be walked a value at a time; it is
            // now removed as the two ranges it is.
            auto result = wide_var(p);
            p.post(Element{result, p.create_integer_variable(0_i, 2_i), narrow(p, 3, 1_i, 3_i)});
        });
        add("Element/view-result", Expect::Clean, [](Problem & p) {
            // The GAC row above with the result wrapped, and nothing else changed.
            // It is the first probe in this file to wrap anything, and it exists
            // because the rule used to answer the question "can I say a range about
            // these?" with a *type* test: a view anywhere sent the whole rule down
            // a per-value walk of the remainder, so this shape walked 10^9 values
            // while the bare one beside it removed two ranges (#924). Nothing else
            // here would have caught that, because nothing else here wraps.
            //
            // Worth generalising rather than leaving as one row: every constraint
            // whose proof reasons about intervals has the same question to answer,
            // and every probe in this file answers it about bare variables only.
            auto result = wide_var(p);
            p.post(Element{result + 1_i, p.create_integer_variable(0_i, 2_i), narrow(p, 3, 1_i, 3_i)});
        });
        add("Element/BC", Expect::Clean, [](Problem & p) {
            // The same instance as the GAC probe above, so the pair is
            // comparable: the weaker arm is what makes it clean, not an easier
            // instance.
            auto result = wide_var(p);
            p.post(Element{result, p.create_integer_variable(0_i, 2_i), narrow(p, 3, 1_i, 3_i)}.with_consistency(consistency::BC{}));
        });
        add("Element/holey", Expect::Clean, [](Problem & p) {
            // Neither row above reaches the sweep's other half. They erase each
            // entry's domain from the result's still-unsupported set, and an
            // entry that is one contiguous run goes in as a single erase_range
            // however wide it is -- so a narrow entry exercises the remainder
            // and a wide entry exercises the fast path, and nothing exercises an
            // entry that is wide *and* has a hole in it, which is the shape that
            // used to be walked a value at a time (#878). One value knocked out
            // of a full-width entry is enough: domain_size stops matching
            // hi - lo + 1 while the domain is still 10^9 wide.
            //
            // Three entries and a free index on purpose. With the index fixed
            // the equality propagator takes over instead, which is a different
            // path with its own holey handling and would have made this row
            // about that one.
            auto result = wide_var(p);
            auto entries = wide(p, 3);
            for (const auto & e : entries)
                p.post(NotEquals{e, ConstantIntegerVariableID{5_i}});
            p.post(Element{result, p.create_integer_variable(0_i, 2_i), entries});
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
        add("Table", Expect::Clean, [](Problem & p) {
            // Was a KnownTrip on two counts: residue rows sized by the variable
            // rather than the table, and a support scan that walked the
            // variable's whole domain. Both fixed, so a wide domain now costs
            // two range removals and a walk bounded by the table.
            auto v = wide(p, 3);
            SimpleTuples tuples{{1_i, 2_i, 3_i}, {4_i, 5_i, 6_i}};
            p.post(Table{v, tuples});
        });
        add("Table/sparse", Expect::Clean, [](Problem & p) {
            // The compact probe above says nothing about this one. There the
            // table's values are adjacent, so trimming the domain to the table's
            // *range* is enough; here the two values sit a million apart, the
            // range is as wide as the domain, and what bounds the scan is
            // removing the gap between them. Before that existed this took
            // 0.163s and 37 MB without proofs, and 3.6 GB of proof and still
            // growing with them.
            auto v = wide(p, 2);
            SimpleTuples tuples{{1_i, 1_i}, {1000000_i, 1000000_i}};
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
        add("Dag", Expect::NoWidePosition, [](Problem & p) {
            auto ns = narrow(p, 3, 0_i, 1_i), es = narrow(p, 3, 0_i, 1_i);
            p.post(Dag{{{0, 1}, {1, 2}, {2, 0}}, ns, es});
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
    /* Branching heuristics, which the constraint lane above cannot see.
     *
     * The rows above all use the default branch heuristic, and the default is
     * one of the lazy ones, so nothing there ever asks a value order to do
     * something expensive. Heuristics also sit outside the guard's remit in a
     * second way: they are not propagators, so no amount of sharpening a
     * constraint's probe reaches them. That combination is how #879 -- seven of
     * the thirteen value orders doing work proportional to the domain's width,
     * at *every* branching decision rather than once at the root -- survived the
     * whole of the rest of this lane.
     *
     * These rows need no separate stopping rule. solve_with_state() calls
     * branch_generator.begin() before the trace callback, and begin() runs the
     * value order up to its first co_yield -- so probe()'s "stop at the root"
     * has already made exactly one branching decision by the time it returns.
     * One call of one heuristic over a 10^9 domain is precisely what is being
     * measured here.
     *
     * The probe problem is two unconstrained wide variables. Nothing propagates,
     * so whatever work a row does is the heuristic's own; two rather than one so
     * that a variable order has something to choose between.
     */
    struct HeuristicProbe
    {
        string name;
        Expect expect;
        function<auto(const Problem &)->BranchHeuristic> branch;
    };

    auto heuristic_probe(const HeuristicProbe & probe_case) -> Result
    {
        try {
            Problem problem;
            auto vars = wide(problem, 2);
            solve_with(problem,
                SolveCallbacks{.solution = [](const CurrentState &) { return false; },
                    .trace = [](const CurrentState &) { return false; },
                    .branch = probe_case.branch(problem),
                    .stats_report = silent_stats_report()});
            return {false, false, {}};
        }
        catch (const LargeDomainGuardTripped & e) {
            return {true, false, e.what()};
        }
        catch (const std::bad_alloc &) {
            return {true, false, "std::bad_alloc, at a site the guard does not check"};
        }
        catch (const std::exception & e) {
            return {false, true, e.what()};
        }
    }

    auto all_heuristic_probes() -> vector<HeuristicProbe>
    {
        vector<HeuristicProbe> probes;

        // Every value order is measured against the same variable order, and
        // every variable order against the same value order, so a row names one
        // heuristic and nothing else. smallest_in is the value order used for
        // the variable-order rows because it reads one bound and stops.
        auto add_value_order = [&](string name, Expect expect, BranchValueGenerator val) {
            probes.push_back(HeuristicProbe{"value_order::" + name, expect,
                [val = move(val)](const Problem & p) { return branch_with(variable_order::in_order(p.all_normal_variables()), val); }});
        };

        auto add_variable_order = [&](string name, Expect expect, function<auto(const Problem &)->BranchVariableHeuristic> var) {
            probes.push_back(HeuristicProbe{
                "variable_order::" + name, expect, [var = move(var)](const Problem & p) { return branch_with(var(p), value_order::smallest_in()); }});
        };

        // The six that read a bound, or hand values out lazily so that the
        // search reads one and stops. dev_docs/large-domains.md calls the lazy
        // case legitimate explicitly: asking for a generator over a billion
        // values and reading one of them is not work proportional to the width.
        add_value_order("smallest_in", Expect::Clean, value_order::smallest_in());
        add_value_order("smallest_out", Expect::Clean, value_order::smallest_out());
        add_value_order("largest_in", Expect::Clean, value_order::largest_in());
        add_value_order("largest_out", Expect::Clean, value_order::largest_out());
        add_value_order("smallest_first", Expect::Clean, value_order::smallest_first());
        add_value_order("largest_first", Expect::Clean, value_order::largest_first());

        // The three splits and the median, which used to walk to their chosen
        // position a value at a time and now ask the domain's interval set for
        // it (#879). split_smallest_first is the one that mattered most: it is
        // the heuristic one naturally reaches *for* a wide domain.
        add_value_order("split_smallest_first", Expect::Clean, value_order::split_smallest_first());
        add_value_order("split_largest_first", Expect::Clean, value_order::split_largest_first());
        add_value_order("split_random", Expect::Clean, value_order::split_random(1234));
        add_value_order("median", Expect::Clean, value_order::median());

        // The two that draw a random position, likewise.
        add_value_order("random_out", Expect::Clean, value_order::random_out(1234));
        add_value_order("reject_random_interval", Expect::Clean, value_order::reject_random_interval(1234));

        // A shuffled enumeration of the domain, which is O(width) if it is
        // produced up front. Drawn lazily instead, so like smallest_first it
        // costs what the search reads rather than what the domain holds.
        add_value_order("random", Expect::Clean, value_order::random(1234));

        // Variable orders read domain *sizes* and bounds, never values --
        // including dom_wdeg, whose weighting schemes take domain_size() into
        // the score. Rows rather than a comment saying so, because that is the
        // property #833 wants checkable rather than argued.
        add_variable_order("in_order", Expect::Clean, [](const Problem & p) { return variable_order::in_order(p.all_normal_variables()); });
        add_variable_order("dom", Expect::Clean, [](const Problem & p) { return variable_order::dom(p); });
        add_variable_order("dom_then_deg", Expect::Clean, [](const Problem & p) { return variable_order::dom_then_deg(p); });
        add_variable_order(
            "dom_wdeg", Expect::Clean, [](const Problem & p) { return variable_order::dom_wdeg(p, WeightingScheme::CurrentArityCurrentDomain); });
        add_variable_order("with_smallest_value", Expect::Clean, [](const Problem & p) { return variable_order::with_smallest_value(p); });
        add_variable_order("with_largest_value", Expect::Clean, [](const Problem & p) { return variable_order::with_largest_value(p); });
        add_variable_order("random", Expect::Clean, [](const Problem & p) { return variable_order::random(p, 1234); });

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

TEST_CASE("Large domain heuristic audit")
{
    // Same pinning rule as the constraint lane: a row that stops tripping is a
    // failure too, so the table cannot drift away from what the code does.
    println("");
    println("{:<40} {:<16} {:<16} {}", "heuristic", "expected", "actual", "");
    for (const auto & probe_case : all_heuristic_probes()) {
        auto result = heuristic_probe(probe_case);
        auto actual = result.broken ? "BROKEN PROBE" : (result.tripped ? "trips" : "survives");
        auto expected_trip = (probe_case.expect == Expect::KnownTrip);
        auto agrees = (! result.broken) && (result.tripped == expected_trip);
        println("{:<40} {:<16} {:<16} {}", probe_case.name, describe(probe_case.expect), actual, agrees ? "" : "<-- MISMATCH");

        INFO("heuristic: " << probe_case.name);
        INFO("detail: " << result.detail);
        CHECK_FALSE(result.broken);
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
