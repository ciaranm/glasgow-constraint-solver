/* Not-first / not-last for Disjunctive, and its certificate.
 *
 * The certificate is edge-finding's, with a different threshold and the negated
 * conclusion on the other guard, so this test's job is the *firing set* rather
 * than the derivation: a task with one end inside a window is edge-finding's,
 * and what this rule is for is a task that SPANS the window, whose guaranteed
 * energy inside it is a hump in its start rather than monotone. Both fixtures
 * below push a spanning task, `sharp` upwards and `mirror` downwards, and each
 * comes with a control that has the rule off.
 *
 * Two things about this rule shape what can be tested and are worth knowing
 * before adding a fixture (`dev_docs/disjunctive-proof-logging.md` has the
 * measurement behind them):
 *
 *  - **Where the rule adds a push, that push is never tight.** Searching
 *    800,000 random unary instances found no firing whose target was the bound
 *    enumeration gives unless time-tabling or detectable precedences already
 *    reached it. So a fixture the rule is load-bearing on cannot also be one
 *    where one-past-the-conclusion is false, and the `tight_nf` / `tight_nl`
 *    fixtures below --- which do land exactly on the enumerated bound --- have
 *    the pairwise rules turned off to get there.
 *  - **At one contained task the push is exactly a detectable precedence's**,
 *    to that task's earliest end, under a weaker detection condition. That is
 *    where the tight pushes are, which is the same fact from the other side.
 *
 * Both are why the mutation lanes run on a *generated* instance rather than on
 * any fixture here: see the comment on `mutating` below.
 *
 * `--search` generates random unary instances, verifies a proof per instance,
 * and checks the rule removes no solutions.
 */

#include <gcs/constraints/disjunctive.hh>
#include <gcs/constraints/innards/constraints_test_utils.hh>
#include <gcs/problem.hh>
#include <gcs/solve.hh>

#include <cstdlib>
#include <fstream>
#include <iostream>
#include <optional>
#include <random>
#include <string>
#include <utility>
#include <variant>
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
using std::mt19937;
using std::nullopt;
using std::optional;
using std::pair;
using std::string;
using std::to_string;
using std::uniform_int_distribution;
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
        println(cerr, "disjunctive_nfnl_test: {}", message);
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

    /// What root propagation alone came to. As for edge-finding, what a control
    /// has to compare is the *bound*: an instance the rule prunes is usually
    /// still satisfiable, and comparing satisfiability would compare nothing.
    struct Probe
    {
        vector<pair<int, int>> root_bounds;
        int markers = 0;
        int solutions = 0;
    };

    auto count_markers(const string & basename, const string & marker) -> int
    {
        std::ifstream f{basename + ".pbp"};
        string line;
        auto count = 0;
        while (getline(f, line))
            if (line.find(marker) != string::npos)
                ++count;
        return count;
    }

    auto probe(const Instance & inst, DisjunctiveRules rules, const optional<string> & proof_name,
        DisjunctiveProofMutation mutation = disjunctive_proof_mutation::None{}, bool enumerate = false, const string & marker = "disjunctive not-")
        -> Probe
    {
        Problem p;
        auto starts = post(p, inst, rules, mutation);
        Probe result;
        auto reached_a_node = false;
        solve_with(p,
            SolveCallbacks{.solution = [&](const CurrentState &) -> bool {
                               ++result.solutions;
                               return enumerate;
                           },
                .trace = [&](const CurrentState & s) -> bool {
                    if (! reached_a_node) {
                        reached_a_node = true;
                        // The first node is the root, after propagation to a
                        // fixpoint: what the rule inferred without searching.
                        for (const auto & v : starts)
                            result.root_bounds.emplace_back(
                                static_cast<int>(s.lower_bound(v).raw_value), static_cast<int>(s.upper_bound(v).raw_value));
                    }
                    return enumerate;
                }},
            proof_name ? make_optional<ProofOptions>(ProofFileNames{*proof_name}) : nullopt);
        if (proof_name)
            result.markers = count_markers(*proof_name, marker);
        return result;
    }

    const DisjunctiveRules with_nfnl{.not_first_not_last = true};
    const DisjunctiveRules without_nfnl{};

    /// The tight fixtures' rules. Time-tabling and detectable precedences are off
    /// because a tight firing is a single-task window, and a single-task window's
    /// push is exactly where a detectable precedence pushes: with those rules on
    /// the sweep never sees the bound left to move. Nothing about the certificate
    /// depends on them --- the mandatory-overlap check that makes the propagator
    /// a *checker* is unconditional, so the solutions are still checked.
    const DisjunctiveRules tight_rules{.time_table = false, .detectable_precedences = false, .not_first_not_last = true};

    /// Random unary instances with enough slack to be satisfiable and enough
    /// pressure for the rule to have something to say --- the same generator
    /// edge-finding's test uses, so the two rules are measured on one family.
    auto generate(mt19937 & rnd, int n) -> Instance
    {
        Instance inst;
        uniform_int_distribution<int> dur{1, 4}, slack{0, 6};
        auto total = 0;
        for (auto i = 0; i < n; ++i) {
            auto l = dur(rnd);
            inst.lengths.push_back(l);
            total += l;
        }
        for (auto i = 0; i < n; ++i) {
            auto lo = uniform_int_distribution<int>{0, total / 2}(rnd);
            inst.start_ranges.emplace_back(lo, lo + inst.lengths[i] + slack(rnd));
        }
        return inst;
    }
}

auto main(int argc, char * argv[]) -> int
{
    auto proofs = gcs::test_innards::can_run_veripb();

    // Window [5, 8), three wide, with Theta = {1, 2} carrying two units, which
    // fits. Task 0 starts at 3 and ends at 13 at the latest, so it spans the
    // window: edge-finding's closed form does not apply to it and its sweep skips
    // it. If task 0 started before ect(Theta) = 6 the guarded row over the window
    // carries two of its units, and two plus two does not fit in three --- so its
    // lower bound rises to 6.
    //
    // The sweep then runs again over the moved bound and fires a second time,
    // now on the window [6, 8) with Theta = {2}, taking the bound to 7. So the
    // fixture is worth two markers and lands at 7: the first firing is the one
    // this rule exists for, and the second is what the first unlocked.
    //
    // No task has a mandatory part (every latest start is at or past its
    // earliest end) and every earliest end is at or before every latest start,
    // which at capacity one is exactly "no detectable precedence": so
    // time-tabling and detectable precedences are both silent, and the control
    // says so.
    const Instance sharp{{{3, 9}, {5, 7}, {6, 7}}, {4, 1, 1}};

    // The mirror, about the window [8, 10): two unit tasks fill it exactly, and
    // task 0 spans it. If task 0 ended after max lst(Theta) = 9 the row carries
    // one of its units, and two plus one does not fit in two --- so its upper
    // bound drops to 6.
    const Instance mirror{{{2, 9}, {8, 9}, {8, 9}}, {3, 1, 1}};

    // A single unit of slack in the window and the rule has nothing to say, so
    // neither fixture above is firing on a technicality.
    const Instance loose{{{3, 9}, {5, 8}, {6, 7}}, {4, 1, 1}};

    // The two tight fixtures: `tight_nf` pushes task 0's lower bound to 11 and
    // `tight_nl` task 0's upper bound to 4, and in each case that is the bound
    // enumeration gives, so the rule is not merely sound here but exact. Both
    // windows hold one task, which is where the exact pushes are --- and is why
    // the pairwise rules have to be off for the rule to be the one making them.
    const Instance tight_nf{{{8, 13}, {9, 10}, {8, 15}}, {4, 2, 2}};
    const Instance tight_nl{{{0, 6}, {8, 8}, {9, 13}}, {4, 1, 4}};

    // The mutation fixture, and it is a generated instance rather than a
    // hand-built one on purpose. On every fixture above at least one route
    // corruption still verifies: the fixtures are small enough that the closing
    // RUP finishes the job from whatever the corrupted derivation left behind,
    // which is sound and VeriPB is right to accept. Scanning generated instances
    // for one where all five lanes are rejected found this in a few hundred
    // tries --- 222 instances fired the rule at all, and one rejected every
    // lane. The two most fragile are `drop_contained` (35 of 222) and
    // `drop_pushed` (20), and the reason is this rule's own: its thresholds are
    // `min ect` and `max lst`, quantities pairwise reasoning can often reach on
    // its own, where edge-finding's `a + p(Theta)` is not.
    const Instance mutating{{{0, 4}, {3, 10}, {2, 10}, {1, 9}, {2, 8}, {4, 10}}, {3, 2, 3, 3, 2, 1}};

    // Mutation mode: emit one deliberately corrupted proof and stop, for
    // run_test_and_expect_verify_failure.bash to hand to veripb.
    {
        optional<DisjunctiveProofMutation> mutation;
        string proof_basename = "disjunctive_nfnl_mutation";
        for (auto a = 1; a < argc; ++a) {
            string arg = argv[a];
            if (arg == "--mutate=emit_nothing")
                mutation = disjunctive_proof_mutation::EdgeFindingEmitNothing{};
            else if (arg == "--mutate=skip_fold")
                mutation = disjunctive_proof_mutation::SkipEdgeFindingFold{};
            else if (arg == "--mutate=drop_contained")
                mutation = disjunctive_proof_mutation::DropContainedEnergy{};
            else if (arg == "--mutate=one_too_far")
                mutation = disjunctive_proof_mutation::EdgeFindingOneTooFar{};
            else if (arg == "--mutate=drop_pushed")
                mutation = disjunctive_proof_mutation::DropPushedEnergy{};
            else if (arg == "--proof-files-basename" && a + 1 < argc)
                proof_basename = argv[++a];
        }

        if (mutation) {
            auto result = probe(mutating, with_nfnl, make_optional(proof_basename), *mutation);
            if (result.markers == 0)
                fail("mutation mode: no not-first push was justified, so the proof is empty");
            println(cerr, "wrote a deliberately corrupted proof to {}.pbp", proof_basename);
            return EXIT_SUCCESS;
        }
    }

    // --search: generated instances, a proof verified per instance, and a
    // solution count against the rule off.
    if (argc > 1 && string{argv[1]} == "--search") {
        auto seed = argc > 2 ? static_cast<unsigned>(std::stoul(argv[2])) : 0u;
        mt19937 rnd{seed};
        auto fired = 0, checked = 0;
        for (auto attempt = 0; attempt < 60; ++attempt) {
            auto inst = generate(rnd, 4 + static_cast<int>(attempt % 3));
            auto name = "disjunctive_nfnl_gen_" + to_string(attempt);
            auto on = probe(inst, with_nfnl, proofs ? make_optional(name) : nullopt, disjunctive_proof_mutation::None{}, true);
            auto off = probe(inst, without_nfnl, nullopt, disjunctive_proof_mutation::None{}, true);
            if (on.solutions != off.solutions)
                fail("generated instance " + to_string(attempt) + ": " + to_string(on.solutions) + " solutions with the rule on against " +
                    to_string(off.solutions) + " with it off");
            if (proofs) {
                ++checked;
                if (on.markers > 0)
                    ++fired;
                if (! gcs::test_innards::run_veripb(name + ".opb", name + ".pbp"))
                    fail("generated instance " + to_string(attempt) + ": veripb rejected the proof");
            }
        }
        println(cerr, "checked {} generated proofs, {} of them carrying a not-first / not-last push", checked, fired);
        if (proofs && fired == 0)
            fail("--search: no generated instance fired the rule, so nothing was tested");
        return EXIT_SUCCESS;
    }

    // The lb push, on a spanning task, and --- the half that makes the fixture
    // worth having --- that nothing else makes it.
    {
        auto on = probe(sharp, with_nfnl, proofs ? make_optional("disjunctive_nfnl_sharp") : nullopt);
        if (on.root_bounds.at(0).first != 7)
            fail("sharp: expected the pushed task's lower bound at 7, got " + to_string(on.root_bounds.at(0).first));
        if (proofs && on.markers != 2)
            fail("sharp: expected exactly two not-first markers, got " + to_string(on.markers));
        if (proofs && ! gcs::test_innards::run_veripb("disjunctive_nfnl_sharp.opb", "disjunctive_nfnl_sharp.pbp"))
            fail("sharp: veripb rejected the certificate");

        auto off = probe(sharp, without_nfnl, nullopt);
        if (off.root_bounds.at(0).first >= 6)
            fail("sharp: the bound moved with the rule off, so the fixture says nothing about the rule");
    }

    // The ub push, which is the same certificate with the negated conclusion on
    // the other guard --- and the one a test that measured only not-first would
    // miss.
    {
        auto on = probe(mirror, with_nfnl, proofs ? make_optional("disjunctive_nfnl_mirror") : nullopt);
        if (on.root_bounds.at(0).second != 6)
            fail("mirror: expected the pushed task's upper bound at 6, got " + to_string(on.root_bounds.at(0).second));
        if (proofs && on.markers != 1)
            fail("mirror: expected exactly one not-last marker, got " + to_string(on.markers));
        if (proofs && ! gcs::test_innards::run_veripb("disjunctive_nfnl_mirror.opb", "disjunctive_nfnl_mirror.pbp"))
            fail("mirror: veripb rejected the certificate");

        auto off = probe(mirror, without_nfnl, nullopt);
        if (off.root_bounds.at(0).second <= 6)
            fail("mirror: the bound moved with the rule off, so the fixture says nothing about the rule");
    }

    // Each half is what makes its own fixture's push, and neither makes the
    // other's. A symmetric rule measured in one direction only is the mistake
    // this exists to prevent.
    {
        DisjunctiveRules first_only{.not_first_not_last = true};
        first_only.not_last = false;
        DisjunctiveRules last_only{.not_first_not_last = true};
        last_only.not_first = false;

        if (probe(sharp, first_only, nullopt).root_bounds.at(0).first != 7)
            fail("not-first alone did not make the sharp fixture's push");
        if (probe(sharp, last_only, nullopt).root_bounds.at(0).first == 7)
            fail("not-last made the sharp fixture's push, so the halves are not what they say");
        if (probe(mirror, last_only, nullopt).root_bounds.at(0).second != 6)
            fail("not-last alone did not make the mirror fixture's push");
        if (probe(mirror, first_only, nullopt).root_bounds.at(0).second == 6)
            fail("not-first made the mirror fixture's push, so the halves are not what they say");
    }

    // The margin of one: a single unit more room in the window and there is
    // nothing to claim.
    {
        auto result = probe(loose, with_nfnl, proofs ? make_optional("disjunctive_nfnl_loose") : nullopt);
        if (proofs && result.markers != 0)
            fail("loose: a push was claimed where the work fits");
        if (proofs && ! gcs::test_innards::run_veripb("disjunctive_nfnl_loose.opb", "disjunctive_nfnl_loose.pbp"))
            fail("loose: veripb rejected the proof");
    }

    // The two tight fixtures: the push lands exactly where enumeration says the
    // bound is. Everywhere the rule is load-bearing it is loose, so this is the
    // only place its conclusion can be checked against the truth rather than
    // only against being sound.
    {
        auto nf = probe(tight_nf, tight_rules, proofs ? make_optional("disjunctive_nfnl_tight_nf") : nullopt);
        if (nf.root_bounds.at(0).first != 11)
            fail("tight_nf: expected the pushed task's lower bound at 11, got " + to_string(nf.root_bounds.at(0).first));
        if (proofs && ! gcs::test_innards::run_veripb("disjunctive_nfnl_tight_nf.opb", "disjunctive_nfnl_tight_nf.pbp"))
            fail("tight_nf: veripb rejected the certificate");

        auto nl = probe(tight_nl, tight_rules, proofs ? make_optional("disjunctive_nfnl_tight_nl") : nullopt);
        if (nl.root_bounds.at(0).second != 4)
            fail("tight_nl: expected the pushed task's upper bound at 4, got " + to_string(nl.root_bounds.at(0).second));
        if (proofs && ! gcs::test_innards::run_veripb("disjunctive_nfnl_tight_nl.opb", "disjunctive_nfnl_tight_nl.pbp"))
            fail("tight_nl: veripb rejected the certificate");
    }

    // Both vocabulary placements certify the same push: they differ only in
    // whether the flags and the guarded rows outlive the firing that made them.
    if (proofs)
        for (auto at : {ProofLevel::Top, ProofLevel::Temporary}) {
            DisjunctiveRules rules{.not_first_not_last = true};
            rules.overload_vocabulary_at = at;
            auto name = string{"disjunctive_nfnl_"} + (at == ProofLevel::Top ? "top" : "temporary");
            auto result = probe(sharp, rules, make_optional(name));
            if (result.root_bounds.at(0).first != 7)
                fail(name + ": the push did not land");
            if (! gcs::test_innards::run_veripb(name + ".opb", name + ".pbp"))
                fail(name + ": veripb rejected the certificate");
        }

    // Alongside edge-finding and the overload check, which share every piece of
    // the vocabulary with it and reach the guarded rows at different guards.
    // Running all three is what would catch a cache keyed on too little.
    if (proofs) {
        DisjunctiveRules rules{.not_first_not_last = true};
        rules.edge_finding = true;
        rules.overload = true;
        auto result = probe(sharp, rules, make_optional("disjunctive_nfnl_with_everything"));
        if (result.root_bounds.at(0).first < 7)
            fail("with_everything: the push did not land");
        if (! gcs::test_innards::run_veripb("disjunctive_nfnl_with_everything.opb", "disjunctive_nfnl_with_everything.pbp"))
            fail("with_everything: veripb rejected the certificate");
    }

    return EXIT_SUCCESS;
}
