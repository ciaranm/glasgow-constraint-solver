/* Vilim's set-based detectable precedence for Disjunctive, and its certificate.
 *
 * #734 pushes `lb(s_j)` to the latest single predecessor's earliest end. This
 * pushes to `ect(Omega)`, the *set's* earliest completion time, which is larger
 * exactly when the predecessors cannot all fit before that point. So this
 * test's job is twofold: that the push is the set's rather than any single
 * predecessor's, and that the certificate for it is tight.
 *
 * The certificate is #757's mechanism, mirrored, and the two halves of this
 * rule use both orientations of it: the lb push argues over
 * `[est(Omega'), T - 1)`, whose **right** edge the negated conclusion derives,
 * and the ub push over `[L + 1, lct(Omega'))`, whose **left** edge it does.
 * Either way the guarded rows are the standard contained-task ones and what is
 * new is only how one guard is discharged --- by a derived two-literal clause
 * rather than by the reason. `drop_clause` is the lane aimed at exactly that.
 *
 * Unlike not-first / not-last, this rule's pushes are often **tight**: both
 * fixtures below land exactly on the bound enumeration gives, so the
 * conclusion can be checked against the truth and not only against being
 * sound. That is also what makes `one_too_far` a real test here.
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
        println(cerr, "disjunctive_set_precedences_test: {}", message);
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
        const string & marker = "disjunctive set-based") -> Probe
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

    const DisjunctiveRules with_set{.detectable_precedences_set = true};
    const DisjunctiveRules without_set{};

    /// Random unary instances, the same generator edge-finding's and
    /// not-first/not-last's tests use, so the three rules are measured on one
    /// family.
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

    // Task 2 has tasks 0, 1 and 3 as detected predecessors: it cannot finish
    // before any of them starts. The pairwise rule reaches only
    // max ect_k = max(5, 2, 5) = 5, which is below task 2's earliest start of 6
    // and so pushes nothing at all. The set rule takes the cut {0, 3} --- both
    // start at 3 and carry two units each --- so ect(Omega) = 3 + 4 = 7, and
    // task 2's lower bound rises 6 -> 7.
    //
    // Time-tabling and pairwise detectable precedences are both silent here
    // (the control below says so), and 7 is exactly the earliest start any
    // feasible schedule gives task 2, so the push is tight as well as sound.
    const Instance sharp{{{3, 5}, {0, 0}, {6, 13}, {3, 8}}, {2, 2, 4, 2}};

    // The mirror, and it fires twice. Task 3 starts in [2, 5] and tasks 0 and 1
    // are its detected successors: neither can finish before task 3's latest
    // start. Both have lct 10 and carry five units between them, so the cut's
    // latest start is 10 - 5 = 5 and task 3's upper bound drops 5 -> 4. That
    // makes task 2 a detected successor as well, and the cut {0, 1, 2} needs
    // seven units before lct 10, taking the bound to 2.
    //
    // The pairwise rule reaches only min lst_k - p_3 = 7 - 1 = 6, which is
    // above the bound already held: it pushes nothing at all, which is what
    // the control says.
    const Instance mirror{{{4, 8}, {3, 7}, {3, 8}, {2, 5}}, {2, 3, 2, 1}};

    // `sharp` with task 3's earliest start moved two later, so the cut {0, 3}
    // and the single task {3} reach the same place: the set rule then adds
    // nothing over the pairwise one, and emits nothing. The margin `sharp`
    // fires on is exactly this, so it is not firing on a technicality.
    const Instance loose{{{3, 5}, {0, 0}, {6, 13}, {5, 8}}, {2, 2, 4, 2}};

    // The mutation fixture, generated rather than hand-built for the reason
    // #731, #752 and #757 all record: a small fixture lets the closing RUP
    // finish from whatever a corrupted derivation left behind, which is sound
    // and VeriPB is right to accept. On `sharp` only four of the six lanes
    // bite --- `skip_fold` and `drop_energy` survive, because with two tasks in
    // the derived window the fold is a single bridge row the closing RUP
    // reconstructs. **|Omega'| >= 3 is the threshold**, the same one #757's
    // simulation found, and this instance (|Omega'| = 3, a ub push on task 3 to
    // 6) is what scanning turned up: of 25 generated instances that fired the
    // rule with a cut of three or more, exactly one rejected every lane.
    const Instance mutating{{{6, 11}, {6, 10}, {6, 8}, {1, 7}, {6, 12}, {7, 10}}, {2, 1, 1, 2, 2, 2}};

    // Mutation mode: emit one deliberately corrupted proof and stop, for
    // run_test_and_expect_verify_failure.bash to hand to veripb.
    {
        optional<DisjunctiveProofMutation> mutation;
        string proof_basename = "disjunctive_set_precedences_mutation";
        for (auto a = 1; a < argc; ++a) {
            string arg = argv[a];
            if (arg == "--mutate=emit_nothing")
                mutation = disjunctive_proof_mutation::SetPrecedenceEmitNothing{};
            else if (arg == "--mutate=skip_fold")
                mutation = disjunctive_proof_mutation::SkipSetPrecedenceFold{};
            else if (arg == "--mutate=drop_energy")
                mutation = disjunctive_proof_mutation::DropSetPrecedenceEnergy{};
            else if (arg == "--mutate=drop_clause")
                mutation = disjunctive_proof_mutation::DropSetPrecedenceClause{};
            else if (arg == "--mutate=rup_clause")
                mutation = disjunctive_proof_mutation::RupSetPrecedenceClause{};
            else if (arg == "--mutate=one_too_far")
                mutation = disjunctive_proof_mutation::PushOneTooFar{};
            else if (arg == "--proof-files-basename" && a + 1 < argc)
                proof_basename = argv[++a];
        }

        if (mutation) {
            auto result = probe(mutating, with_set, make_optional(proof_basename), *mutation);
            if (result.markers == 0)
                fail("mutation mode: no set-based push was justified, so the proof is empty");
            println(cerr, "wrote a deliberately corrupted proof to {}.pbp", proof_basename);
            return EXIT_SUCCESS;
        }
    }

    // --search: generated instances, a proof verified per instance, and a
    // solution count against the rule off. The lane that matters --- hand-built
    // fixtures are symmetric and generous and verify straight through
    // certificate bugs.
    if (argc > 1 && string{argv[1]} == "--search") {
        auto seed = argc > 2 ? static_cast<unsigned>(std::stoul(argv[2])) : 0u;
        mt19937 rnd{seed};
        auto fired = 0, checked = 0;
        for (auto attempt = 0; attempt < 60; ++attempt) {
            auto inst = generate(rnd, 4 + static_cast<int>(attempt % 3));
            auto name = "disjunctive_set_precedences_gen_" + to_string(attempt);
            auto on = probe(inst, with_set, proofs ? make_optional(name) : nullopt, disjunctive_proof_mutation::None{}, true);
            auto off = probe(inst, without_set, nullopt, disjunctive_proof_mutation::None{}, true);
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
        println(cerr, "checked {} generated instances, {} fired the rule", checked, fired);
        return EXIT_SUCCESS;
    }

    // The lb push, and the control that says nothing else makes it.
    {
        auto on = probe(sharp, with_set, proofs ? make_optional("disjunctive_set_precedences_sharp") : nullopt);
        if (on.root_bounds.at(2).first != 7)
            fail("sharp: expected task 2's lower bound at 7, got " + to_string(on.root_bounds.at(2).first));
        auto off = probe(sharp, without_set, nullopt);
        if (off.root_bounds.at(2).first == 7)
            fail("sharp: the pairwise rules already made the push, so the fixture measures nothing");
        if (proofs && ! gcs::test_innards::run_veripb("disjunctive_set_precedences_sharp.opb", "disjunctive_set_precedences_sharp.pbp"))
            fail("sharp: veripb rejected the certificate");
    }

    // The ub push, and its control. Measuring one half of a symmetric rule
    // tells you almost nothing, which is why both are here.
    {
        auto on = probe(mirror, with_set, proofs ? make_optional("disjunctive_set_precedences_mirror") : nullopt);
        if (on.root_bounds.at(3).second != 2)
            fail("mirror: expected task 3's upper bound at 2, got " + to_string(on.root_bounds.at(3).second));
        auto off = probe(mirror, without_set, nullopt);
        if (off.root_bounds.at(3).second == 2)
            fail("mirror: the pairwise rules already made the push, so the fixture measures nothing");
        if (proofs && ! gcs::test_innards::run_veripb("disjunctive_set_precedences_mirror.opb", "disjunctive_set_precedences_mirror.pbp"))
            fail("mirror: veripb rejected the certificate");
    }

    // The margin of one: a unit more room and the set rule reaches no further
    // than the pairwise one.
    {
        auto result = probe(loose, with_set, proofs ? make_optional("disjunctive_set_precedences_loose") : nullopt);
        if (proofs && result.markers != 0)
            fail("loose: a set-based push was claimed where the pairwise rule already reaches");
        if (proofs && ! gcs::test_innards::run_veripb("disjunctive_set_precedences_loose.opb", "disjunctive_set_precedences_loose.pbp"))
            fail("loose: veripb rejected the proof");
    }

    // Both vocabulary placements certify the same push: they differ only in
    // whether the flags and the guarded rows outlive the firing that made them.
    if (proofs)
        for (auto at : {ProofLevel::Top, ProofLevel::Temporary}) {
            DisjunctiveRules rules{.detectable_precedences_set = true};
            rules.overload_vocabulary_at = at;
            auto name = string{"disjunctive_set_precedences_"} + (at == ProofLevel::Top ? "top" : "temporary");
            auto result = probe(sharp, rules, make_optional(name));
            if (result.root_bounds.at(2).first != 7)
                fail(name + ": the push did not land");
            if (! gcs::test_innards::run_veripb(name + ".opb", name + ".pbp"))
                fail(name + ": veripb rejected the certificate");
        }

    // Alongside every other rule, which share the whole vocabulary with it and
    // reach the guarded rows at different guards over different windows.
    // Running all of them is what would catch a cache keyed on too little.
    if (proofs) {
        DisjunctiveRules rules{.detectable_precedences_set = true};
        rules.edge_finding = true;
        rules.not_first_not_last = true;
        rules.overload = true;
        auto result = probe(sharp, rules, make_optional("disjunctive_set_precedences_with_everything"));
        if (result.root_bounds.at(2).first < 7)
            fail("with_everything: the push did not land");
        if (! gcs::test_innards::run_veripb("disjunctive_set_precedences_with_everything.opb", "disjunctive_set_precedences_with_everything.pbp"))
            fail("with_everything: veripb rejected the certificate");
    }

    return EXIT_SUCCESS;
}
