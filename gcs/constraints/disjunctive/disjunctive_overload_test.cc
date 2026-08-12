/* Overload checking for Disjunctive, and its certificate.
 *
 * The trap #655 established applies here unchanged: this rule fires nowhere in
 * the existing corpus, so a green suite says nothing about it. Every fixture
 * below therefore comes with a *control* --- the same instance with the rule
 * off --- and the test fails if the control already reaches the conclusion,
 * because then the fixture is measuring something else. The comparison is at
 * the *root*: this rule is conflict-only, so an instance it refutes is
 * unsatisfiable without it too, and only searched for rather than reasoned
 * about. Comparing satisfiability would therefore compare nothing.
 *
 * The sharp fixture is three tasks of duration three whose starts all lie in
 * [0, 5], so each must run entirely inside a window eight wide while together
 * they need nine. No two mandatory parts overlap and no precedence is
 * detectable between any pair, so time-tabling and detectable precedences are
 * both silent: the refutation is the overload check's alone.
 *
 * Unlike presence falsification (see disjunctive_mutations.hh), an overload's
 * reason context is not contradictory until the argument makes it so, so
 * corrupting the *route* is a real test here and not merely a shorter sound
 * derivation. That is why the mutation lanes below skip halves of the endgame
 * rather than only corrupting its destination.
 */

#include <gcs/constraints/disjunctive.hh>
#include <gcs/constraints/innards/constraints_test_utils.hh>
#include <gcs/problem.hh>
#include <gcs/solve.hh>

#include <cstdlib>
#include <fstream>
#include <iostream>
#include <optional>
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
using std::ifstream;
using std::make_optional;
using std::nullopt;
using std::optional;
using std::pair;
using std::string;
using std::vector;

#if defined(__cpp_lib_print) && defined(__cpp_lib_format)
using std::println;
#else
using fmt::println;
#endif

using namespace gcs;
using namespace gcs::innards;

namespace
{
    struct Instance
    {
        vector<pair<int, int>> start_ranges;
        vector<int> lengths;
    };

    auto fail(const string & message) -> void
    {
        println(cerr, "disjunctive_overload_test: {}", message);
        exit(EXIT_FAILURE);
    }

    auto post(Problem & p, const Instance & inst, DisjunctiveRules rules, DisjunctiveProofMutation mutation) -> vector<IntegerVariableID>
    {
        vector<IntegerVariableID> starts;
        vector<Integer> lengths;
        for (const auto & [lo, hi] : inst.start_ranges)
            starts.push_back(p.create_integer_variable(Integer{lo}, Integer{hi}));
        for (auto l : inst.lengths)
            lengths.push_back(Integer{l});
        p.post(Disjunctive{starts, lengths}.with_rules(rules).with_proof_mutation(mutation));
        return starts;
    }

    /// What root propagation alone came to, and how many overload markers the
    /// proof carries. Satisfiability is no use as a control here: the rule is
    /// conflict-only, so an instance it refutes is unsatisfiable with the rule
    /// off as well --- just found by searching rather than by reasoning. What
    /// separates the rules is whether the *root* closes.
    struct Probe
    {
        bool refuted_at_root = false;
        bool satisfiable = false;
        int markers = 0;
        int solutions = 0;
    };

    auto proof_lines(const string & basename) -> int
    {
        ifstream f{basename + ".pbp"};
        string line;
        auto count = 0;
        while (getline(f, line))
            if (line.find(';') != string::npos)
                ++count;
        return count;
    }

    auto count_markers(const string & basename, const string & marker) -> int
    {
        ifstream f{basename + ".pbp"};
        string line;
        auto count = 0;
        while (getline(f, line))
            if (line.find(marker) != string::npos)
                ++count;
        return count;
    }

    auto count_overload_markers(const string & basename) -> int
    {
        return count_markers(basename, "disjunctive overload w=");
    }

    /// How many of those were certified by sorting the window rather than by
    /// re-encoding time. The two are alternative arguments over one unchanged
    /// encoding, so which was taken is not visible in the answer --- only in
    /// the proof.
    auto count_sorted_markers(const string & basename) -> int
    {
        return count_markers(basename, "disjunctive overload by sorting network");
    }

    auto probe(const Instance & inst, DisjunctiveRules rules, const optional<string> & proof_name,
        DisjunctiveProofMutation mutation = disjunctive_proof_mutation::None{}, bool enumerate = false) -> Probe
    {
        Problem p;
        post(p, inst, rules, mutation);
        Probe result;
        // Refuted at the root means propagation reached a contradiction before
        // any branching: no search node and no solution. The solution check is
        // not redundant, an all-fixed instance being answered without ever
        // branching.
        auto reached_a_node = false;
        solve_with(p,
            SolveCallbacks{.solution = [&](const CurrentState &) -> bool {
                               result.satisfiable = true;
                               ++result.solutions;
                               return enumerate;
                           },
                .trace = [&](const CurrentState &) -> bool {
                    reached_a_node = true;
                    // Stopping at the first node is what makes "refuted at the
                    // root" observable; enumerating needs the search to run on.
                    return enumerate;
                }},
            proof_name ? make_optional<ProofOptions>(ProofFileNames{*proof_name}) : nullopt);
        result.refuted_at_root = ! reached_a_node && ! result.satisfiable;
        if (proof_name)
            result.markers = count_overload_markers(*proof_name);
        return result;
    }

    const DisjunctiveRules all_rules{.overload = true};
    const DisjunctiveRules no_overload{.overload = false};
}

auto main(int argc, char * argv[]) -> int
{
    // Proofs only where veripb is installed, as every constraint test does:
    // a run without it still checks the propagation, and says so by writing no
    // proof rather than by writing one nothing looks at.
    auto proofs = gcs::test_innards::can_run_veripb();

    // Three tasks of three, every start in [0, 5]: none may begin before 0 and
    // all must be done by 8, so eight time units have to hold nine of work.
    // Every *pair* fits in eight, so no pairwise rule sees anything, and no
    // task has a mandatory part (latest start 5 is past earliest end 3), so
    // time-tabling is silent too.
    const Instance sharp{{{0, 5}, {0, 5}, {0, 5}}, {3, 3, 3}};

    // Mutation mode: emit one deliberately corrupted proof of `sharp` and stop,
    // for run_test_and_expect_verify_failure.bash to hand to veripb.
    {
        optional<DisjunctiveProofMutation> mutation;
        string proof_basename = "disjunctive_overload_mutation";
        for (auto a = 1; a < argc; ++a) {
            string arg = argv[a];
            if (arg == "--mutate=emit_nothing")
                mutation = disjunctive_proof_mutation::OverloadEmitNothing{};
            else if (arg == "--mutate=skip_fold")
                mutation = disjunctive_proof_mutation::SkipOverloadFold{};
            else if (arg == "--mutate=skip_energy")
                mutation = disjunctive_proof_mutation::SkipOverloadEnergy{};
            else if (arg == "--mutate=rup_bridge")
                mutation = disjunctive_proof_mutation::RupOverloadBridge{};
            else if (arg == "--proof-files-basename" && a + 1 < argc)
                proof_basename = argv[++a];
        }

        if (mutation) {
            auto result = probe(sharp, all_rules, make_optional(proof_basename), *mutation);
            if (result.markers == 0)
                fail("mutation mode: no overload was justified, so the proof is empty");
            println(cerr, "wrote a deliberately corrupted proof to {}.pbp", proof_basename);
            return EXIT_SUCCESS;
        }
    }

    // The rule refutes it, and --- the half that makes the fixture worth
    // having --- nothing else does.
    {
        auto with_rule = probe(sharp, all_rules, proofs ? make_optional("disjunctive_overload_sharp") : nullopt);
        if (with_rule.satisfiable)
            fail("sharp: a solution was reported, but nine units do not fit in eight");
        if (! with_rule.refuted_at_root)
            fail("sharp: the rule did not close the root");
        if (proofs && with_rule.markers != 1)
            fail("sharp: expected exactly one overload marker, got " + std::to_string(with_rule.markers));
        if (proofs && ! gcs::test_innards::run_veripb("disjunctive_overload_sharp.opb", "disjunctive_overload_sharp.pbp"))
            fail("sharp: veripb rejected the overload certificate");

        auto without_rule = probe(sharp, no_overload, nullopt);
        if (without_rule.refuted_at_root)
            fail("sharp: the root closed with the rule off, so the fixture says nothing about the rule");
    }

    // The margin of one: widen the window by a single unit and it fits, so
    // nothing above is refuting on a technicality.
    {
        const Instance loose{{{0, 6}, {0, 6}, {0, 6}}, {3, 3, 3}};
        auto result = probe(loose, all_rules, proofs ? make_optional("disjunctive_overload_loose") : nullopt);
        if (result.refuted_at_root)
            fail("loose: the root closed, but nine units fit in exactly nine");
        if (proofs && result.markers != 0)
            fail("loose: an overload was claimed where the work fits");
        if (proofs && ! gcs::test_innards::run_veripb("disjunctive_overload_loose.opb", "disjunctive_overload_loose.pbp"))
            fail("loose: veripb rejected the proof");
    }

    // Both vocabulary placements certify the same refutation. They differ only
    // in whether the activity flags outlive the firing that made them, so a
    // difference here would be a bug in one of them rather than a fact about
    // the instance.
    if (proofs)
        for (auto at : {ProofLevel::Top, ProofLevel::Temporary}) {
            DisjunctiveRules rules{.overload = true};
            rules.overload_vocabulary_at = at;
            auto name = string{"disjunctive_overload_"} + (at == ProofLevel::Top ? "top" : "temporary");
            auto result = probe(sharp, rules, make_optional(name));
            if (! result.refuted_at_root)
                fail(name + ": the root did not close");
            if (result.markers != 1)
                fail(name + ": expected exactly one overload marker, got " + std::to_string(result.markers));
            if (! gcs::test_innards::run_veripb(name + ".opb", name + ".pbp"))
                fail(name + ": veripb rejected the certificate");
        }

    // The same refutation, certified by sorting the window instead. Both
    // arguments run over the one unchanged pairwise encoding, so a difference
    // here is a bug in one of them rather than a fact about the instance.
    if (proofs) {
        DisjunctiveRules rules{.overload = true};
        rules.overload_certificate = DisjunctiveOverloadCertificate::SortingNetwork;
        auto result = probe(sharp, rules, make_optional("disjunctive_overload_sorted"));
        if (! result.refuted_at_root)
            fail("sorted: the root did not close");
        if (result.markers != 1)
            fail("sorted: expected exactly one overload marker, got " + std::to_string(result.markers));
        if (count_sorted_markers("disjunctive_overload_sorted") != 1)
            fail("sorted: the sorting-network certificate was asked for and not emitted");
        if (! gcs::test_innards::run_veripb("disjunctive_overload_sorted.opb", "disjunctive_overload_sorted.pbp"))
            fail("sorted: veripb rejected the sorting-network certificate");
    }

    // A window wide enough that the crossover picks the network on its own:
    // three tasks of ten whose starts lie in [0, 19], so thirty units of work
    // have to fit in a window twenty-nine wide. Certified both ways, and the
    // default has to choose the network without being told.
    {
        const Instance wide{{{0, 19}, {0, 19}, {0, 19}}, {10, 10, 10}};

        // The crossover is set here rather than taken from the default: the
        // default is three hundred, measured over searches where keeping the
        // at-most-ones amortises the time-indexed route, and a window that
        // reached it would be far too big to put in a fixture. What is being
        // tested is that the switch fires on the window's shape, not what the
        // shipped number happens to be.
        DisjunctiveRules crossing{.overload = true};
        crossing.overload_crossover = 9;
        auto by_default = probe(wide, crossing, proofs ? make_optional("disjunctive_overload_wide") : nullopt);
        if (by_default.satisfiable)
            fail("wide: a solution was reported, but thirty units do not fit in twenty-nine");
        if (! by_default.refuted_at_root)
            fail("wide: the rule did not close the root");
        if (proofs) {
            if (count_sorted_markers("disjunctive_overload_wide") != by_default.markers)
                fail("wide: the crossover did not pick the network on a window twenty-nine wide with three tasks");
            // And the shipped default, on the same window, picks the other one.
            auto shipped = probe(wide, all_rules, make_optional("disjunctive_overload_wide_default"));
            if (count_sorted_markers("disjunctive_overload_wide_default") != 0)
                fail("wide: the shipped crossover picked the network on a window nowhere near three hundred tasks' worth of span");
            if (! shipped.refuted_at_root)
                fail("wide: the shipped default did not close the root");
            if (! gcs::test_innards::run_veripb("disjunctive_overload_wide.opb", "disjunctive_overload_wide.pbp"))
                fail("wide: veripb rejected the certificate the crossover picked");
        }

        auto without_rule = probe(wide, no_overload, nullopt);
        if (without_rule.refuted_at_root)
            fail("wide: the root closed with the rule off, so the fixture says nothing about the rule");

        // And the other certificate on the same window, which is what says the
        // crossover is choosing between two things that both work.
        if (proofs) {
            DisjunctiveRules rules{.overload = true};
            rules.overload_certificate = DisjunctiveOverloadCertificate::TimeIndexed;
            auto result = probe(wide, rules, make_optional("disjunctive_overload_wide_time_indexed"));
            if (! result.refuted_at_root)
                fail("wide_time_indexed: the root did not close");
            if (count_sorted_markers("disjunctive_overload_wide_time_indexed") != 0)
                fail("wide_time_indexed: a sorting network was emitted where time indexing was asked for");
            if (! gcs::test_innards::run_veripb("disjunctive_overload_wide_time_indexed.opb", "disjunctive_overload_wide_time_indexed.pbp"))
                fail("wide_time_indexed: veripb rejected the time-indexed certificate");
        }
    }

    // Many firings, which is the only way the kept per-time at-most-ones can
    // be reused: four tasks of three in a window of twelve fit exactly, so
    // every solution is a permutation and the search meets an overloaded
    // subwindow whenever it puts a task down out of step. Enumerating rather
    // than stopping at the first solution is what makes it fire repeatedly.
    if (proofs) {
        const Instance permutations{{{0, 9}, {0, 9}, {0, 9}, {0, 9}}, {3, 3, 3, 3}};

        auto run = [&](bool cache, const string & name) -> pair<Probe, int> {
            DisjunctiveRules rules{.overload = true};
            rules.overload_cache_bridge = cache;
            auto result = probe(permutations, rules, make_optional(name), disjunctive_proof_mutation::None{}, true);
            if (! gcs::test_innards::run_veripb(name + ".opb", name + ".pbp"))
                fail(name + ": veripb rejected the certificate");
            return {result, proof_lines(name)};
        };

        auto [cached, cached_lines] = run(true, "disjunctive_overload_cached");
        auto [derived, derived_lines] = run(false, "disjunctive_overload_uncached");

        if (cached.markers < 2)
            fail("permutations: the rule fired " + std::to_string(cached.markers) + " times, so nothing was there to reuse");
        if (cached.solutions != derived.solutions || cached.markers != derived.markers)
            fail("permutations: keeping the at-most-ones changed the search, which it must not");
        // The whole point of the option. If keeping them ever stops paying,
        // this is where that shows up rather than in a benchmark nobody runs.
        if (cached_lines >= derived_lines)
            fail("permutations: keeping the at-most-ones cost " + std::to_string(cached_lines) + " lines against " + std::to_string(derived_lines) +
                " for deriving them again");
    }

    // A window the rule must not touch: two tasks that genuinely fit, where a
    // sloppy sweep would still find "a" window if it counted a task whose lct
    // falls outside it.
    {
        const Instance fits{{{0, 0}, {5, 5}, {2, 2}}, {2, 3, 3}};
        auto result = probe(fits, all_rules, proofs ? make_optional("disjunctive_overload_fits") : nullopt);
        if (result.refuted_at_root)
            fail("fits: refuted a feasible schedule");
        if (proofs && result.markers != 0)
            fail("fits: an overload was claimed on a schedule that fits");
        if (proofs && ! gcs::test_innards::run_veripb("disjunctive_overload_fits.opb", "disjunctive_overload_fits.pbp"))
            fail("fits: veripb rejected the proof");
    }

    return EXIT_SUCCESS;
}
