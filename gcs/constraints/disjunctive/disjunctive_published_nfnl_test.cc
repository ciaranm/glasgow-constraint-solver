/* The published not-first / not-last condition for Disjunctive, and its
 * certificate (#757).
 *
 * `disjunctive_nfnl_test.cc` covers the detection the window-energy lemma can
 * derive over the window the sweep enumerated. This one covers the rule as the
 * literature states it, which argues over a window the negated conclusion
 * *derives* instead --- `[ect_j, lct(Theta))` for not-first, and
 * `[est(Theta), ub(s_j))` for not-last. The two detections are incomparable, so
 * neither test's fixtures serve the other.
 *
 * What is new in the certificate, and so what this test is mostly about, is the
 * derived two-literal clause that puts the contained set inside that window: it
 * carries the conclusion literal at the guard's own coefficient, so the
 * conclusion accumulates across Theta and the summed pol derives it. That is
 * #754's mechanism, and the `drop_clause` / `rup_clause` mutation lanes are
 * aimed straight at it.
 *
 * The certificate has two paths and both are fixtured. Where every contained
 * task fits inside the derived window it is an energy argument, the same shape
 * edge-finding's is (`sharp`, `mirror`). Where one does not --- which the
 * narrower window makes common, not exotic --- the two guards on that one task
 * are already contradictory and the whole derivation is the clause plus the
 * reason's row for the bound it contradicts (`shortcut_nf`, `shortcut_nl`).
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
        println(cerr, "disjunctive_published_nfnl_test: {}", message);
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
        DisjunctiveProofMutation mutation = disjunctive_proof_mutation::None{}, bool enumerate = false,
        const string & marker = "disjunctive published not-") -> Probe
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

    /// The published condition replaces the certifiable detection rather than
    /// strengthening it, so it needs the sweep the other rule owns: setting it
    /// without `not_first_not_last` would run nothing at all, which is what
    /// `rcpsp` does too.
    const DisjunctiveRules published{.not_first_not_last = true, .not_first_not_last_published = true};
    const DisjunctiveRules nothing{};

    /// The shortcut fixtures' rules. A contained task too long for the derived
    /// window is one whose earliest end is past the pushed task's whole range,
    /// which at two tasks is also a detectable precedence --- so the pairwise
    /// rules have to be off for this rule to be the one making the push.
    /// Nothing about the certificate depends on them: the mandatory-overlap
    /// check that makes the propagator a *checker* is unconditional.
    const DisjunctiveRules shortcut_rules{
        .time_table = false, .detectable_precedences = false, .not_first_not_last = true, .not_first_not_last_published = true};

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

    // The energy path, not-first. Window [5, 8) holds Theta = {1, 2}, two units
    // in three, which fits --- so the sweep's own detection has nothing to say
    // over it. The published one argues over [ect_0, 8) = [7, 8) instead: if
    // task 0 started before ect(Theta) = 6 then both contained tasks would have
    // to start at or after task 0's earliest end, and two unit tasks do not fit
    // in one time point. So task 0's lower bound rises to 6.
    const Instance sharp{{{3, 9}, {5, 7}, {6, 7}}, {4, 1, 1}};

    // The mirror, and the half a test measuring only not-first would miss.
    // Theta = {1, 2} sits in [8, 10) and task 0 spans it; the derived window is
    // [est(Theta), ub(s_0)) = [8, 9), and two units do not fit in one, so task
    // 0's upper bound drops to max lst(Theta) - p_0 = 6.
    const Instance mirror{{{2, 9}, {8, 9}, {8, 9}}, {3, 1, 1}};

    // The shortcut path. Theta = {1} carries three units and the derived window
    // [ect_0, lct(Theta)) = [7, 9) is two wide, so task 1 cannot be in it at
    // all: its guard "starts at or after 7" and the reason's "starts at or
    // before 6" are contradictory on their own, and the certificate is the
    // clause plus that one row. Task 0's lower bound goes to ect_1 = 8, which
    // is where enumeration puts it.
    const Instance shortcut_nf{{{3, 12}, {5, 6}}, {4, 3}};

    // Its mirror, reflected in time: the derived window [11, 13) is two wide
    // and task 1 needs three, so task 0's upper bound drops to
    // lst(Theta) - p_0 = 8. Also the bound enumeration gives.
    const Instance shortcut_nl{{{4, 13}, {11, 12}}, {4, 3}};

    // One more unit of room in the window and the condition has nothing to
    // claim, so neither fixture above is firing on a technicality.
    const Instance loose{{{3, 9}, {5, 8}, {6, 7}}, {4, 1, 1}};

    // The mutation fixture, generated rather than hand-built for the reason
    // `disjunctive_nfnl_test.cc` records: on a small fixture the closing RUP
    // finishes the job from whatever a corrupted derivation left behind, which
    // is sound and VeriPB is right to accept.
    //
    // Scanning generated instances for one where all six lanes are rejected
    // found this at the eighth try. Over 300 instances, 172 fired the rule at
    // all and 24 of those rejected every lane; the two most fragile are
    // `skip_fold` (36 of 172) and `drop_energy` (58), for the same reason
    // not-first / not-last's own lanes are fragile --- the thresholds are
    // `min ect` and `max lst`, which pairwise reasoning can often reach on its
    // own. The two aimed at what is new here hold up much better:
    // `drop_clause` 127 and `rup_clause` 130.
    const Instance mutating{{{6, 14}, {9, 13}, {6, 14}, {0, 4}, {3, 11}, {5, 11}, {2, 11}}, {3, 1, 2, 3, 4, 3, 3}};

    // Mutation mode: emit one deliberately corrupted proof and stop, for
    // run_test_and_expect_verify_failure.bash to hand to veripb.
    {
        optional<DisjunctiveProofMutation> mutation;
        string proof_basename = "disjunctive_published_nfnl_mutation";
        for (auto a = 1; a < argc; ++a) {
            string arg = argv[a];
            if (arg == "--mutate=emit_nothing")
                mutation = disjunctive_proof_mutation::PublishedEmitNothing{};
            else if (arg == "--mutate=skip_fold")
                mutation = disjunctive_proof_mutation::SkipPublishedFold{};
            else if (arg == "--mutate=drop_energy")
                mutation = disjunctive_proof_mutation::DropPublishedEnergy{};
            else if (arg == "--mutate=drop_clause")
                mutation = disjunctive_proof_mutation::DropPublishedClause{};
            else if (arg == "--mutate=rup_clause")
                mutation = disjunctive_proof_mutation::RupPublishedClause{};
            else if (arg == "--mutate=one_too_far")
                mutation = disjunctive_proof_mutation::EdgeFindingOneTooFar{};
            else if (arg == "--proof-files-basename" && a + 1 < argc)
                proof_basename = argv[++a];
        }

        if (mutation) {
            auto result = probe(mutating, published, make_optional(proof_basename), *mutation);
            if (result.markers == 0)
                fail("mutation mode: no published push was justified, so the proof is empty");
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
            auto name = "disjunctive_published_nfnl_gen_" + to_string(attempt);
            auto on = probe(inst, published, proofs ? make_optional(name) : nullopt, disjunctive_proof_mutation::None{}, true);
            auto off = probe(inst, nothing, nullopt, disjunctive_proof_mutation::None{}, true);
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
        println(cerr, "checked {} generated proofs, {} of them carrying a published not-first / not-last push", checked, fired);
        if (proofs && fired == 0)
            fail("--search: no generated instance fired the rule, so nothing was tested");
        return EXIT_SUCCESS;
    }

    // The energy path, and --- the half that makes a fixture worth having ---
    // that nothing else makes the push.
    {
        auto on = probe(sharp, published, proofs ? make_optional("disjunctive_published_nfnl_sharp") : nullopt);
        if (on.root_bounds.at(0).first < 6)
            fail("sharp: expected the pushed task's lower bound at 6 or better, got " + to_string(on.root_bounds.at(0).first));
        if (proofs && on.markers == 0)
            fail("sharp: no published marker, so the fixture says nothing about the rule");
        if (proofs && ! gcs::test_innards::run_veripb("disjunctive_published_nfnl_sharp.opb", "disjunctive_published_nfnl_sharp.pbp"))
            fail("sharp: veripb rejected the certificate");

        auto off = probe(sharp, nothing, nullopt);
        if (off.root_bounds.at(0).first >= 6)
            fail("sharp: the bound moved with the rule off, so the fixture says nothing about the rule");
    }

    // The mirror, which is the same certificate with the derived edge on the
    // other side of the window.
    {
        auto on = probe(mirror, published, proofs ? make_optional("disjunctive_published_nfnl_mirror") : nullopt);
        if (on.root_bounds.at(0).second > 6)
            fail("mirror: expected the pushed task's upper bound at 6 or better, got " + to_string(on.root_bounds.at(0).second));
        if (proofs && on.markers == 0)
            fail("mirror: no published marker, so the fixture says nothing about the rule");
        if (proofs && ! gcs::test_innards::run_veripb("disjunctive_published_nfnl_mirror.opb", "disjunctive_published_nfnl_mirror.pbp"))
            fail("mirror: veripb rejected the certificate");

        auto off = probe(mirror, nothing, nullopt);
        if (off.root_bounds.at(0).second <= 6)
            fail("mirror: the bound moved with the rule off, so the fixture says nothing about the rule");
    }

    // Each half makes its own fixture's push and neither makes the other's. A
    // symmetric rule measured in one direction only is the mistake this exists
    // to prevent.
    {
        auto first_only = published;
        first_only.not_last = false;
        auto last_only = published;
        last_only.not_first = false;

        if (probe(sharp, first_only, nullopt).root_bounds.at(0).first < 6)
            fail("not-first alone did not make the sharp fixture's push");
        if (probe(sharp, last_only, nullopt).root_bounds.at(0).first >= 6)
            fail("not-last made the sharp fixture's push, so the halves are not what they say");
        if (probe(mirror, last_only, nullopt).root_bounds.at(0).second > 6)
            fail("not-last alone did not make the mirror fixture's push");
        if (probe(mirror, first_only, nullopt).root_bounds.at(0).second <= 6)
            fail("not-first made the mirror fixture's push, so the halves are not what they say");
    }

    // The shortcut path, both ways round, and in each case the push lands
    // exactly where enumeration puts the bound.
    {
        auto nf = probe(shortcut_nf, shortcut_rules, proofs ? make_optional("disjunctive_published_nfnl_shortcut_nf") : nullopt);
        if (nf.root_bounds.at(0).first != 8)
            fail("shortcut_nf: expected the pushed task's lower bound at 8, got " + to_string(nf.root_bounds.at(0).first));
        if (proofs && nf.markers == 0)
            fail("shortcut_nf: no published marker");
        if (proofs && ! gcs::test_innards::run_veripb("disjunctive_published_nfnl_shortcut_nf.opb", "disjunctive_published_nfnl_shortcut_nf.pbp"))
            fail("shortcut_nf: veripb rejected the certificate");

        auto nl = probe(shortcut_nl, shortcut_rules, proofs ? make_optional("disjunctive_published_nfnl_shortcut_nl") : nullopt);
        if (nl.root_bounds.at(0).second != 8)
            fail("shortcut_nl: expected the pushed task's upper bound at 8, got " + to_string(nl.root_bounds.at(0).second));
        if (proofs && nl.markers == 0)
            fail("shortcut_nl: no published marker");
        if (proofs && ! gcs::test_innards::run_veripb("disjunctive_published_nfnl_shortcut_nl.opb", "disjunctive_published_nfnl_shortcut_nl.pbp"))
            fail("shortcut_nl: veripb rejected the certificate");
    }

    // The margin of one: a single unit more room and there is nothing to claim.
    {
        auto result = probe(loose, published, proofs ? make_optional("disjunctive_published_nfnl_loose") : nullopt);
        if (proofs && result.markers != 0)
            fail("loose: a push was claimed where the work fits");
        if (proofs && ! gcs::test_innards::run_veripb("disjunctive_published_nfnl_loose.opb", "disjunctive_published_nfnl_loose.pbp"))
            fail("loose: veripb rejected the proof");
    }

    // Both vocabulary placements certify the same push: they differ only in
    // whether the flags and the guarded rows outlive the firing that made them.
    if (proofs)
        for (auto at : {ProofLevel::Top, ProofLevel::Temporary}) {
            auto rules = published;
            rules.overload_vocabulary_at = at;
            auto name = string{"disjunctive_published_nfnl_"} + (at == ProofLevel::Top ? "top" : "temporary");
            auto result = probe(sharp, rules, make_optional(name));
            if (result.root_bounds.at(0).first < 6)
                fail(name + ": the push did not land");
            if (! gcs::test_innards::run_veripb(name + ".opb", name + ".pbp"))
                fail(name + ": veripb rejected the certificate");
        }

    // Alongside edge-finding, the set-based precedences and the overload check,
    // which share every piece of the vocabulary with it and reach the guarded
    // rows at different guards. Running them together is what would catch a
    // cache keyed on too little.
    if (proofs) {
        auto rules = published;
        rules.edge_finding = true;
        rules.detectable_precedences_set = true;
        rules.overload = true;
        auto result = probe(sharp, rules, make_optional("disjunctive_published_nfnl_with_everything"));
        if (result.root_bounds.at(0).first < 6)
            fail("with_everything: the push did not land");
        if (! gcs::test_innards::run_veripb("disjunctive_published_nfnl_with_everything.opb", "disjunctive_published_nfnl_with_everything.pbp"))
            fail("with_everything: veripb rejected the certificate");
    }

    return EXIT_SUCCESS;
}
