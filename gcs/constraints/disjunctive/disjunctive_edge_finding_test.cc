/* Edge-finding for Disjunctive, and its certificate.
 *
 * The rule prunes rather than fails, and that changes what can serve as a test.
 * The overload check's destination is a contradiction, so every route to it is
 * valid and corrupting the route is what bites; here the reason context
 * extended with the negated conclusion goes contradictory as soon as the
 * argument lands, so a corruption that merely *shortens* the derivation is
 * still sound and VeriPB is right to accept it. **The `+1` on the conclusion is
 * the signature test**, and the fixtures are built so that one unit is exactly
 * the difference between a valid push and a false one.
 *
 * Both fixtures put a window `[a, b)` around a set `Theta` that fits in it, and
 * one further task with a single end inside. `sharp` has that end at the left,
 * so the push raises a lower bound; `mirror` has it at the right, so the push
 * lowers an upper bound. Both are here because measuring one direction of a
 * symmetric rule tells you almost nothing --- on the cumulative side the two
 * halves came out at 2.2% and 51%.
 *
 * Every fixture comes with a control: the same instance with the rule off. If
 * the control already makes the push then the fixture is measuring
 * time-tabling or detectable precedences, not this. Neither fires on either
 * fixture by construction --- no task has a mandatory part, and no pair's
 * ordering is forced by bounds alone --- and the controls are what keep that
 * true as the rest of the propagator changes.
 *
 * `--search` generates random unary instances, verifies a proof per instance,
 * and checks the rule removes no solutions. Hand-built fixtures are symmetric
 * and generous, and verify straight through certificate bugs; generated ones
 * are what actually found them on the cumulative side.
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
        println(cerr, "disjunctive_edge_finding_test: {}", message);
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

    /// What root propagation alone came to. Unlike the overload check this rule
    /// moves a bound, so what a control has to compare is the *bound*: an
    /// instance it prunes is usually still satisfiable, and comparing
    /// satisfiability would compare nothing.
    struct Probe
    {
        vector<pair<int, int>> root_bounds;
        int markers = 0;
        int solutions = 0;
        bool refuted_at_root = false;
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
        DisjunctiveProofMutation mutation = disjunctive_proof_mutation::None{}, bool enumerate = false) -> Probe
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
        result.refuted_at_root = ! reached_a_node && 0 == result.solutions;
        if (proof_name)
            result.markers = count_markers(*proof_name, "disjunctive edge-finding w=");
        return result;
    }

    const DisjunctiveRules with_ef{.edge_finding = true};
    const DisjunctiveRules without_ef{};

    /// Random unary instances with enough slack to be satisfiable and enough
    /// pressure for the rule to have something to say. Durations are small and
    /// windows overlap, which is where a set argument beats a pairwise one.
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

    // Window [2, 8), six wide. Theta = two tasks of two and three, so five
    // units, which fits. Task 2 starts inside the window and ends past it: if
    // it started before 7 it would have to spend at least two of the window's
    // time points there, and five plus two does not fit in six. So its start
    // rises to 7 = ect(Theta), and 7 is reachable --- 2 at [2,5), 0 at [5,7),
    // 2 at [7,9) --- so one further would be false.
    //
    // No task has a mandatory part (every latest start is past its earliest
    // end), and no pair's ordering is forced by bounds alone, so time-tabling
    // and detectable precedences are both silent.
    const Instance sharp{{{2, 6}, {2, 5}, {2, 20}}, {2, 3, 2}};

    // The mirror, about the window [4, 10): task 2 now starts before the window
    // and ends inside it, so the push lowers its upper bound to
    // b - p_j - p(Theta) = 3. At 4 it would spend two of the window's points
    // inside; at 3 only one, and six units fit in six.
    const Instance mirror{{{4, 8}, {4, 7}, {0, 8}}, {2, 3, 2}};

    // Mutation mode: emit one deliberately corrupted proof and stop, for
    // run_test_and_expect_verify_failure.bash to hand to veripb.
    {
        optional<DisjunctiveProofMutation> mutation;
        string proof_basename = "disjunctive_edge_finding_mutation";
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
            auto result = probe(sharp, with_ef, make_optional(proof_basename), *mutation);
            if (result.markers == 0)
                fail("mutation mode: no edge-finding push was justified, so the proof is empty");
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
            auto name = "disjunctive_edge_finding_gen_" + to_string(attempt);
            auto on = probe(inst, with_ef, proofs ? make_optional(name) : nullopt, disjunctive_proof_mutation::None{}, true);
            auto off = probe(inst, without_ef, nullopt, disjunctive_proof_mutation::None{}, true);
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
        println(cerr, "checked {} generated proofs, {} of them carrying an edge-finding push", checked, fired);
        if (proofs && fired == 0)
            fail("--search: no generated instance fired the rule, so nothing was tested");
        return EXIT_SUCCESS;
    }

    // The lb push, and --- the half that makes the fixture worth having ---
    // that nothing else makes it.
    {
        auto on = probe(sharp, with_ef, proofs ? make_optional("disjunctive_edge_finding_sharp") : nullopt);
        if (on.root_bounds.at(2).first != 7)
            fail("sharp: expected the pushed task's lower bound at 7, got " + to_string(on.root_bounds.at(2).first));
        if (proofs && on.markers != 1)
            fail("sharp: expected exactly one edge-finding marker, got " + to_string(on.markers));
        if (proofs && ! gcs::test_innards::run_veripb("disjunctive_edge_finding_sharp.opb", "disjunctive_edge_finding_sharp.pbp"))
            fail("sharp: veripb rejected the certificate");

        auto off = probe(sharp, without_ef, nullopt);
        if (off.root_bounds.at(2).first >= 7)
            fail("sharp: the bound moved with the rule off, so the fixture says nothing about the rule");
    }

    // The ub push, which is the same certificate with the guards the other way
    // round --- and the one a test that measured only the lb push would miss.
    {
        auto on = probe(mirror, with_ef, proofs ? make_optional("disjunctive_edge_finding_mirror") : nullopt);
        if (on.root_bounds.at(2).second != 3)
            fail("mirror: expected the pushed task's upper bound at 3, got " + to_string(on.root_bounds.at(2).second));
        if (proofs && on.markers != 1)
            fail("mirror: expected exactly one edge-finding marker, got " + to_string(on.markers));
        if (proofs && ! gcs::test_innards::run_veripb("disjunctive_edge_finding_mirror.opb", "disjunctive_edge_finding_mirror.pbp"))
            fail("mirror: veripb rejected the certificate");

        auto off = probe(mirror, without_ef, nullopt);
        if (off.root_bounds.at(2).second <= 3)
            fail("mirror: the bound moved with the rule off, so the fixture says nothing about the rule");
    }

    // The margin of one: widen the window by a single unit and the rule has
    // nothing to say, so neither fixture above is firing on a technicality.
    {
        const Instance loose{{{2, 7}, {2, 6}, {2, 20}}, {2, 3, 2}};
        auto result = probe(loose, with_ef, proofs ? make_optional("disjunctive_edge_finding_loose") : nullopt);
        if (proofs && result.markers != 0)
            fail("loose: a push was claimed where the work fits");
        if (proofs && ! gcs::test_innards::run_veripb("disjunctive_edge_finding_loose.opb", "disjunctive_edge_finding_loose.pbp"))
            fail("loose: veripb rejected the proof");
    }

    // Both vocabulary placements certify the same push. They differ only in
    // whether the flags and the guarded rows outlive the firing that made
    // them, so a difference here is a bug in one of them.
    if (proofs)
        for (auto at : {ProofLevel::Top, ProofLevel::Temporary}) {
            DisjunctiveRules rules{.edge_finding = true};
            rules.overload_vocabulary_at = at;
            auto name = string{"disjunctive_edge_finding_"} + (at == ProofLevel::Top ? "top" : "temporary");
            auto result = probe(sharp, rules, make_optional(name));
            if (result.root_bounds.at(2).first != 7)
                fail(name + ": the push did not land");
            if (! gcs::test_innards::run_veripb(name + ".opb", name + ".pbp"))
                fail(name + ": veripb rejected the certificate");
        }

    // Alongside the overload check, which shares every piece of the
    // vocabulary with it. Running both is what would catch a cache keyed on
    // too little.
    if (proofs) {
        DisjunctiveRules rules{.edge_finding = true};
        rules.overload = true;
        auto result = probe(sharp, rules, make_optional("disjunctive_edge_finding_with_overload"));
        if (result.root_bounds.at(2).first != 7)
            fail("with_overload: the push did not land");
        if (! gcs::test_innards::run_veripb("disjunctive_edge_finding_with_overload.opb", "disjunctive_edge_finding_with_overload.pbp"))
            fail("with_overload: veripb rejected the certificate");
    }

    return EXIT_SUCCESS;
}
