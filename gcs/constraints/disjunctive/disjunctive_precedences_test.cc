#include <gcs/constraints/disjunctive.hh>
#include <gcs/constraints/innards/constraints_test_utils.hh>
#include <gcs/problem.hh>
#include <gcs/solve.hh>

#include <cstdlib>
#include <fstream>
#include <iostream>
#include <optional>
#include <random>
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
using std::ifstream;
using std::make_optional;
using std::max;
using std::min;
using std::nullopt;
using std::optional;
using std::pair;
using std::set;
using std::string;
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
using namespace gcs::innards;
using namespace gcs::test_innards;

namespace
{
    // A fixture: a start range and a duration spec {lo, hi} per task, where
    // lo == hi is a constant duration and lo < hi a variable one.
    struct Instance
    {
        vector<pair<int, int>> start_ranges;
        vector<pair<int, int>> length_specs;
        bool strict = true;
    };

    auto is_variable_length(const Instance & inst, size_t i) -> bool
    {
        return inst.length_specs[i].first != inst.length_specs[i].second;
    }

    // The lengths a solution vector carries: starts first, then one entry per
    // variable duration, in task order (what post() enumerates).
    auto lengths_of(const Instance & inst, const vector<int> & vals) -> vector<int>
    {
        auto n = inst.start_ranges.size();
        vector<int> lengths(n);
        auto next = n;
        for (size_t i = 0; i < n; ++i)
            lengths[i] = is_variable_length(inst, i) ? vals.at(next++) : inst.length_specs[i].first;
        return lengths;
    }

    auto is_satisfying(const Instance & inst, const vector<int> & vals) -> bool
    {
        auto n = inst.start_ranges.size();
        auto lengths = lengths_of(inst, vals);
        for (size_t i = 0; i < n; ++i)
            for (size_t j = i + 1; j < n; ++j) {
                // Non-strict: a pair involving a zero-length task floats.
                if (! inst.strict && (lengths[i] == 0 || lengths[j] == 0))
                    continue;
                if (! (vals[i] + lengths[i] <= vals[j]) && ! (vals[j] + lengths[j] <= vals[i]))
                    return false;
            }
        return true;
    }

    // Posts the instance, and hands back the starts (which every probe reads
    // bounds from) and the full enumerated variable list (starts, then the
    // variable durations).
    struct Posted
    {
        vector<IntegerVariableID> starts;
        vector<IntegerVariableID> all_vars;
    };

    auto post(Problem & p, const Instance & inst, DisjunctiveRules rules, DisjunctiveProofMutation mutation = disjunctive_proof_mutation::None{})
        -> Posted
    {
        Posted posted;
        vector<IntegerVariableID> lengths;
        for (auto & [lo, hi] : inst.start_ranges) {
            auto v = p.create_integer_variable(Integer{lo}, Integer{hi});
            posted.starts.push_back(v);
            posted.all_vars.push_back(v);
        }
        for (size_t i = 0; i < inst.start_ranges.size(); ++i)
            if (is_variable_length(inst, i)) {
                auto lv = p.create_integer_variable(Integer{inst.length_specs[i].first}, Integer{inst.length_specs[i].second});
                lengths.push_back(lv);
                posted.all_vars.push_back(lv);
            }
            else
                lengths.push_back(constant_variable(Integer{inst.length_specs[i].first}));

        p.post(Disjunctive{posted.starts, lengths}.with_strict(inst.strict).with_rules(rules).with_proof_mutation(mutation));
        return posted;
    }

    // How many times each detectable-precedence push left its marker in a
    // proof file. The propagator writes one comment per push it justifies, so
    // a test can tell "the rule fired" from "the rule was compiled in and
    // never triggered" --- and, on a negative twin, insist that it did not
    // fire at all.
    struct MarkerCounts
    {
        size_t lb = 0, ub = 0;

        [[nodiscard]] auto total() const -> size_t
        {
            return lb + ub;
        }
    };

    auto count_markers(const string & proof_name) -> MarkerCounts
    {
        MarkerCounts counts;
        ifstream proof{proof_name + ".pbp"};
        if (! proof) {
            println(cerr, "could not read {}.pbp to count precedence markers", proof_name);
            std::exit(EXIT_FAILURE);
        }
        string line;
        while (getline(proof, line)) {
            if (line.find("disjunctive detectable precedence") == string::npos)
                continue;
            if (line.find("push=lb") != string::npos)
                ++counts.lb;
            else if (line.find("push=ub") != string::npos)
                ++counts.ub;
        }
        return counts;
    }

    // What one propagation at the root did: whether it refuted the instance,
    // the start bounds it left behind, and which pushes fired getting there.
    // Stopping at the first search node keeps all of that attributable to root
    // reasoning --- a satisfiable instance would otherwise accumulate markers
    // from deep in the search, which says nothing about the fixture.
    struct RootProbe
    {
        bool refuted = false;
        vector<pair<int, int>> start_bounds;
        MarkerCounts markers;
    };

    auto solve_root_only(const Instance & inst, DisjunctiveRules rules, DisjunctiveProofMutation mutation, const optional<string> & proof_name)
        -> RootProbe
    {
        Problem p;
        auto posted = post(p, inst, rules, mutation);

        RootProbe probe;
        // Refuted means root propagation reached a contradiction: neither a
        // search node nor a solution. The solution check is not redundant ---
        // an instance whose variables are all fixed by propagation is answered
        // without ever branching, so no node is ever traced.
        bool reached_a_node = false, found_a_solution = false;
        auto record = [&](const CurrentState & s) -> bool {
            if (probe.start_bounds.empty())
                for (const auto & v : posted.starts)
                    probe.start_bounds.emplace_back(static_cast<int>(s.lower_bound(v).raw_value), static_cast<int>(s.upper_bound(v).raw_value));
            return false;
        };
        solve_with(p,
            SolveCallbacks{.solution = [&](const CurrentState & s) -> bool {
                               found_a_solution = true;
                               return record(s);
                           },
                .trace = [&](const CurrentState & s) -> bool {
                    reached_a_node = true;
                    return record(s);
                }},
            proof_name ? make_optional<ProofOptions>(ProofFileNames{*proof_name}) : nullopt);

        probe.refuted = ! reached_a_node && ! found_a_solution;
        return probe;
    }

    auto probe_root(const Instance & inst, DisjunctiveRules rules, const optional<string> & proof_name) -> RootProbe
    {
        auto probe = solve_root_only(inst, rules, disjunctive_proof_mutation::None{}, proof_name);
        if (proof_name) {
            probe.markers = count_markers(*proof_name);
            verify_proof_and_clean_up(*proof_name);
        }
        return probe;
    }

    // The rule written out from its definition, iterated to a fixpoint, over a
    // plain double loop sharing no code with the propagator. Bounds only: the
    // rule never touches a duration, so the durations stay at their root lower
    // bounds throughout. Returns nullopt when a push empties a domain, or when
    // the always-on mandatory-overlap check finds a conflict.
    //
    // A fixpoint is well defined whatever order the pairs are visited in:
    // raising a lower bound or lowering an upper bound can only make more
    // precedences detectable, never fewer, so the rule is monotone and the
    // propagator's own visiting order cannot matter.
    //
    // A task whose start is already fixed is never the one pushed, matching the
    // propagator. Nothing is lost by that: a detected precedence between a
    // fixed task and an unfixed one pushes the unfixed one just as far (that is
    // the same precedence read the other way round), and a pair of fixed tasks
    // that collide both have mandatory parts, which the always-on
    // mandatory-overlap check below catches.
    auto oracle_precedence_fixpoint(const Instance & inst) -> optional<vector<pair<int, int>>>
    {
        auto n = inst.start_ranges.size();
        auto bounds = inst.start_ranges;
        vector<int> min_len;
        for (auto & [lo, hi] : inst.length_specs)
            min_len.push_back(lo);

        for (bool changed = true; changed;) {
            changed = false;
            // The mandatory-overlap contradiction, which runs whatever rules are
            // selected (it is what makes the propagator a checker), and which
            // the propagator scans for before it pushes anything.
            for (size_t i = 0; i < n; ++i)
                for (size_t j = i + 1; j < n; ++j) {
                    if (min_len[i] == 0 || min_len[j] == 0)
                        continue;
                    auto lst_i = bounds[i].second, eet_i = bounds[i].first + min_len[i];
                    auto lst_j = bounds[j].second, eet_j = bounds[j].first + min_len[j];
                    if (lst_i < eet_i && lst_j < eet_j && lst_i < eet_j && lst_j < eet_i)
                        return nullopt;
                }
            for (size_t j = 0; j < n; ++j) {
                if (min_len[j] == 0 || bounds[j].first == bounds[j].second)
                    continue;
                for (size_t k = 0; k < n; ++k) {
                    if (k == j || min_len[k] == 0)
                        continue;
                    // k << j detectable: j cannot finish before k starts.
                    if (bounds[j].first + min_len[j] > bounds[k].second) {
                        auto target = min(bounds[k].first + min_len[k], bounds[j].second + 1);
                        if (target > bounds[j].first) {
                            bounds[j].first = target;
                            changed = true;
                        }
                    }
                    // j << k detectable: k cannot finish before j starts.
                    if (bounds[k].first + min_len[k] > bounds[j].second) {
                        auto target = max(bounds[k].second - min_len[j], bounds[j].first - 1);
                        if (target < bounds[j].second) {
                            bounds[j].second = target;
                            changed = true;
                        }
                    }
                }
                if (bounds[j].first > bounds[j].second)
                    return nullopt;
            }
        }
        return bounds;
    }

    auto fail(const string & message) -> void
    {
        println(cerr, "disjunctive precedences test failure: {}", message);
        std::exit(EXIT_FAILURE);
    }

    // A full enumeration against brute force, with the proof verified. This is
    // the soundness net: a bug in the rule removes solutions.
    auto check_enumeration(const string & what, const Instance & inst, DisjunctiveRules rules, const optional<string> & proof_name) -> void
    {
        print(cerr, "disjunctive precedences {}{} starts={} lens={}{}", what, inst.strict ? " strict" : " nonstrict", inst.start_ranges,
            inst.length_specs, proof_name ? " with proofs:" : ":");
        cerr << flush;

        vector<pair<int, int>> all_ranges = inst.start_ranges;
        for (size_t i = 0; i < inst.start_ranges.size(); ++i)
            if (is_variable_length(inst, i))
                all_ranges.push_back(inst.length_specs[i]);

        set<vector<int>> expected, actual;
        build_expected(expected, [&](const vector<int> & vals) { return is_satisfying(inst, vals); }, all_ranges);
        println(cerr, " expecting {} solutions", expected.size());

        Problem p;
        auto posted = post(p, inst, rules);
        solve_for_tests(p, proof_name, actual, tuple{posted.all_vars});
        check_results(proof_name, expected, actual);
    }

    auto read_file(const string & name) -> string
    {
        ifstream in{name, std::ios::binary};
        if (! in)
            fail("could not read " + name);
        return string{std::istreambuf_iterator<char>{in}, std::istreambuf_iterator<char>{}};
    }

    // The OPB is the statement being verified, and nothing detectable
    // precedences do may reach it: every fact the rule establishes is a
    // derivation inside the proof. So the model must come out byte-identical
    // however the rule is configured --- including under a mutation, which is
    // proof-only too.
    //
    // VeriPB will happily verify a correct proof of the wrong model, so this is
    // not a tidiness check: an inference that quietly became a model axiom
    // would leave every proof in this file verifying and prove nothing about
    // the solver.
    auto check_opb_unaffected(const string & what, const Instance & inst) -> void
    {
        const string on = "disjunctive_precedences_opb_on", off = "disjunctive_precedences_opb_off", mutated = "disjunctive_precedences_opb_mutated";

        solve_root_only(inst, DisjunctiveRules{}, disjunctive_proof_mutation::None{}, on);
        solve_root_only(inst, DisjunctiveRules{.time_table = true, .detectable_precedences = false}, disjunctive_proof_mutation::None{}, off);
        solve_root_only(inst, DisjunctiveRules{}, disjunctive_proof_mutation::SkipRefutation{}, mutated);

        auto with_rule = read_file(on + ".opb");
        if (with_rule != read_file(off + ".opb"))
            fail("OPB differs with and without detectable precedences, on " + what);
        if (with_rule != read_file(mutated + ".opb"))
            fail("OPB differs under a proof mutation, on " + what);

        for (const auto & name : {on, off, mutated})
            dispose_of_proof_files(name);
    }
}

auto main(int argc, char * argv[]) -> int
{
    establish_and_announce_seed(argc, argv);

    const DisjunctiveRules all_rules{};
    const DisjunctiveRules no_precedences{.time_table = true, .detectable_precedences = false};
    // Isolate the precedence reasoning: with time-tabling off, any bound the
    // propagator moves was moved by a detected precedence.
    const DisjunctiveRules only_precedences{.time_table = false, .detectable_precedences = true};

    auto proofs = can_run_veripb();

    // The sharp-margin fixture. Task 0 runs for 3 units somewhere in [0, 3],
    // task 1 for 3 units somewhere in [1, 10]. Neither has a mandatory part ---
    // task 0's [3, 3) and task 1's [10, 4) are both empty --- so time-tabling
    // has nothing to say at all.
    //
    // But task 1 cannot finish before task 0 starts: it cannot end before
    // 1 + 3 = 4, and task 0 must start by 3. So 0 << 1, and task 1 starts no
    // earlier than task 0's earliest end, 0 + 3 = 3.
    //
    // The margin is exactly one on both counts: detection has 4 against 3 + 1,
    // and s_1 = 3 is still feasible, so a push to 4 would be false.
    const Instance sharp{{{0, 3}, {1, 10}}, {{3, 3}, {3, 3}}};

    // A fixture whose pushes all happen during search: no precedence is
    // detectable at the root here (task 1 cannot end before 4, and task 0 need
    // not start until 4), but once search raises lb(s_1) to 2, task 1 cannot end
    // before 5 while task 0 must start by 4, so 0 << 1 and task 0 must finish by
    // task 1's latest start. Every bound the pushes cite is then a search bound.
    const Instance deep{{{-3, 4}, {1, 4}}, {{1, 1}, {3, 3}}};

    // The fixture the mutation lanes corrupt, which is deliberately *not*
    // `sharp`, and the reason is worth recording: on `sharp`, dropping either
    // one of the two pols still verifies. Whether the closing RUP needs them
    // both is a property of the particular arithmetic --- unit propagation over
    // the operands' bit encodings sometimes closes the gap on its own --- and
    // the propagator cannot cheaply tell which case it is in, so it always emits
    // both, exactly as time-tabling's push chains do. A mutation lane needs a
    // fixture where that is visible.
    //
    // Task 0 runs for 5 units in [7, 8], task 1 for 3 units in [6, 18]. Task 1
    // cannot end before 6 + 3 = 9 while task 0 must start by 8, so 0 << 1, and
    // task 1 starts no earlier than task 0's earliest end, 7 + 5 = 12. The
    // margin is one on both counts: detection has 9 against 8 + 1, and s_1 = 12
    // is feasible (task 0 at 7), so a push to 13 would be false. Every mutation
    // below is rejected here, the one that weakens a cited bound by one
    // included.
    const Instance tight{{{7, 8}, {6, 18}}, {{5, 5}, {3, 3}}};

    // Mutation mode: emit one deliberately corrupted proof of `tight` and stop,
    // for run_test_and_expect_verify_failure.bash to hand to veripb.
    // Time-tabling is off so every justification in the proof is a precedence
    // push's, and the solve enumerates, so the proof is a complete enumeration
    // however the derivation was corrupted. Branching here is the default, not
    // the seeded random one, so the lanes are reproducible.
    {
        optional<DisjunctiveProofMutation> mutation;
        string proof_basename = "disjunctive_precedences_mutation";
        for (int a = 1; a < argc; ++a) {
            string arg = argv[a];
            if (arg == "--mutate=emit_nothing")
                mutation = disjunctive_proof_mutation::EmitNothing{};
            else if (arg == "--mutate=skip_refutation")
                mutation = disjunctive_proof_mutation::SkipRefutation{};
            else if (arg == "--mutate=skip_fold")
                mutation = disjunctive_proof_mutation::SkipTargetFold{};
            else if (arg == "--mutate=loose_bound")
                mutation = disjunctive_proof_mutation::LooseDetectionBound{};
            else if (arg == "--mutate=one_too_far")
                mutation = disjunctive_proof_mutation::PushOneTooFar{};
            else if (arg == "--proof-files-basename" && a + 1 < argc)
                proof_basename = argv[++a];
        }

        if (mutation) {
            Problem p;
            post(p, tight, only_precedences, *mutation);
            solve_with(p, SolveCallbacks{.solution = [&](const CurrentState &) -> bool { return true; }},
                make_optional<ProofOptions>(ProofFileNames{proof_basename}));
            if (count_markers(proof_basename).total() == 0)
                fail("mutation mode: no precedence push was justified, so the proof is empty");
            println(cerr, "wrote a deliberately corrupted proof to {}.pbp", proof_basename);
            return EXIT_SUCCESS;
        }
    }

    // The sharp fixture, and the claim that time-tabling cannot reach its
    // conclusion. This is the whole point of the rule: it prunes where
    // time-tabling is silent.
    {
        auto with_rule = probe_root(sharp, all_rules, proofs ? make_optional("disjunctive_precedences_sharp") : nullopt);
        if (with_rule.refuted)
            fail("sharp: refuted at the root, but it is satisfiable");
        if (with_rule.start_bounds.at(1).first != 3)
            fail("sharp: expected lb(s_1) = 3 at the root, got " + std::to_string(with_rule.start_bounds.at(1).first));
        if (proofs && with_rule.markers.lb != 1)
            fail("sharp: expected exactly one lb push marker, got " + std::to_string(with_rule.markers.lb));
        if (proofs && with_rule.markers.ub != 0)
            fail("sharp: an upper bound was pushed where nothing forces one");

        auto without_rule = probe_root(sharp, no_precedences, nullopt);
        if (without_rule.start_bounds != sharp.start_ranges)
            fail("sharp: time-tabling alone moved a bound, so the fixture proves nothing");
    }

    // The mirror image, on an upper bound. Task 1 runs for 3 units somewhere
    // in [4, 7], so it cannot end before 7; task 0 must start by 6, so task 1
    // cannot finish before task 0 starts and 0 << 1. Task 0 must therefore
    // finish by task 1's latest start, putting s_0 at 7 - 3 = 4 at the latest.
    // Both mandatory parts are again empty, so time-tabling says nothing.
    const Instance sharp_ub{{{0, 6}, {4, 7}}, {{3, 3}, {3, 3}}};

    {
        auto with_rule = probe_root(sharp_ub, all_rules, proofs ? make_optional("disjunctive_precedences_sharp_ub") : nullopt);
        if (with_rule.refuted)
            fail("sharp_ub: refuted at the root, but it is satisfiable");
        if (with_rule.start_bounds.at(0).second != 4)
            fail("sharp_ub: expected ub(s_0) = 4 at the root, got " + std::to_string(with_rule.start_bounds.at(0).second));
        if (proofs && with_rule.markers.ub != 1)
            fail("sharp_ub: expected exactly one ub push marker, got " + std::to_string(with_rule.markers.ub));

        auto without_rule = probe_root(sharp_ub, no_precedences, nullopt);
        if (without_rule.start_bounds != sharp_ub.start_ranges)
            fail("sharp_ub: time-tabling alone moved a bound, so the fixture proves nothing");
    }

    // A negative twin: the same two tasks, short enough that neither ordering
    // is forced. Nothing may be pushed and no marker may appear.
    const Instance twin{{{0, 3}, {1, 10}}, {{1, 1}, {1, 1}}};

    {
        auto probe = probe_root(twin, all_rules, proofs ? make_optional("disjunctive_precedences_twin") : nullopt);
        if (probe.start_bounds != twin.start_ranges)
            fail("twin: a bound moved where no precedence is detectable");
        if (proofs && probe.markers.total() != 0)
            fail("twin: a push was justified where no precedence is detectable");
    }

    // A chain of three, where the pushes compose: 0 << 1 pushes task 1 up to
    // 3, which is what makes 1 << 2 (detectable from the start) worth
    // anything, pushing task 2 up to 6. No mandatory part appears at any
    // point, so time-tabling stays silent throughout and every bound that
    // moves was moved by this rule.
    const Instance chain{{{0, 3}, {1, 6}, {4, 12}}, {{3, 3}, {3, 3}, {3, 3}}};

    {
        auto with_rule = probe_root(chain, all_rules, proofs ? make_optional("disjunctive_precedences_chain") : nullopt);
        if (with_rule.refuted)
            fail("chain: refuted at the root, but it is satisfiable");
        auto oracle = oracle_precedence_fixpoint(chain);
        if (! oracle || with_rule.start_bounds != *oracle)
            fail("chain: the root bounds are not the rule's fixpoint");
        if (with_rule.start_bounds.at(1).first != 3 || with_rule.start_bounds.at(2).first != 6)
            fail("chain: expected lb(s_1) = 3 and lb(s_2) = 6 at the root");
        if (proofs && with_rule.markers.total() != 2)
            fail("chain: expected exactly two pushes, got " + std::to_string(with_rule.markers.total()));

        auto without_rule = probe_root(chain, no_precedences, nullopt);
        if (without_rule.start_bounds != chain.start_ranges)
            fail("chain: time-tabling alone moved a bound, so the fixture proves nothing");
    }

    // A contradiction reached by the rule alone: task 1 has nowhere left to go
    // once 0 << 1 pushes it past its own upper bound.
    const Instance refuted{{{0, 3}, {1, 2}}, {{3, 3}, {3, 3}}};

    {
        auto with_rule = probe_root(refuted, only_precedences, proofs ? make_optional("disjunctive_precedences_refuted") : nullopt);
        if (! with_rule.refuted)
            fail("refuted: the rule did not refute at the root");
        if (proofs && with_rule.markers.total() != 1)
            fail("refuted: expected exactly one push marker, got " + std::to_string(with_rule.markers.total()));
    }

    // Pushes made against search bounds rather than root ones: nothing is
    // detectable at the root here, so every push in the proof cites a bound
    // search established, and the whole thing verifies as a complete
    // enumeration.
    {
        auto root = probe_root(deep, only_precedences, nullopt);
        if (root.start_bounds != deep.start_ranges)
            fail("deep: a bound moved at the root, so the fixture is not testing search-state bounds");

        auto name = "disjunctive_precedences_deep";
        Problem p;
        post(p, deep, only_precedences);
        size_t solutions = 0;
        solve_with(p, SolveCallbacks{.solution = [&](const CurrentState &) -> bool {
            ++solutions;
            return true;
        }},
            proofs ? make_optional<ProofOptions>(ProofFileNames{name}) : nullopt);
        if (solutions == 0)
            fail("deep: no solutions, but the fixture is satisfiable");
        if (proofs) {
            if (count_markers(name).total() == 0)
                fail("deep: no precedence push anywhere in the search, so the fixture tests nothing");
            verify_proof_and_clean_up(name);
        }
    }

    // The mutation fixture, honestly derived: one push at the root, by a margin
    // of one, and the proof the lanes below corrupt verifies before they do.
    {
        auto with_rule = probe_root(tight, only_precedences, proofs ? make_optional("disjunctive_precedences_tight") : nullopt);
        if (with_rule.refuted)
            fail("tight: refuted at the root, but it is satisfiable");
        if (with_rule.start_bounds.at(1).first != 12)
            fail("tight: expected lb(s_1) = 12 at the root, got " + std::to_string(with_rule.start_bounds.at(1).first));
        if (proofs && with_rule.markers.lb != 1)
            fail("tight: expected exactly one lb push marker, got " + std::to_string(with_rule.markers.lb));
    }

    // Variable durations, strict and non-strict. The pols cite lb(l) for a
    // variable duration, and in non-strict mode every variable-duration task
    // carries a zero-length escape flag that the justification has to pin
    // false before the separation clause is usable.
    for (auto strict : {true, false}) {
        Instance var{{{0, 3}, {1, 10}}, {{3, 4}, {3, 4}}, strict};
        auto label = strict ? "var_strict" : "var_nonstrict";
        auto with_rule = probe_root(var, all_rules, proofs ? make_optional("disjunctive_precedences_" + string{label}) : nullopt);
        if (with_rule.refuted)
            fail(string{label} + ": refuted at the root, but it is satisfiable");
        if (with_rule.start_bounds.at(1).first != 3)
            fail(string{label} + ": expected lb(s_1) = 3 at the root");
        if (proofs && with_rule.markers.lb != 1)
            fail(string{label} + ": expected exactly one lb push marker");
    }

    // Oracle cross-check. Over a random corpus, with time-tabling off so that
    // every bound the propagator moves was moved by this rule, the root bounds
    // must be exactly the rule's own fixpoint --- which catches both
    // under- and over-firing. Durations are all positive, so the strict-mode
    // zero-length check cannot fire and confuse the comparison.
    {
        std::mt19937 rand(*get_seed());
        // Start domains reach below zero: a push then lands on the order
        // literals of a signed bit encoding (issue #553's shape).
        std::uniform_int_distribution<> n_dist(2, 4), lo_dist(-4, 6), span_dist(0, 6), len_dist(1, 4);

        size_t fired = 0, verified = 0;
        for (int k = 0; k < 250; ++k) {
            Instance inst;
            auto n = n_dist(rand);
            for (int i = 0; i < n; ++i) {
                auto lo = lo_dist(rand), span = span_dist(rand);
                inst.start_ranges.emplace_back(lo, lo + span);
                auto len = len_dist(rand);
                inst.length_specs.emplace_back(len, len);
            }

            auto oracle = oracle_precedence_fixpoint(inst);
            // A bound moved without the instance being refuted, which is the
            // case a marker must be attributable to: a refutation may equally
            // have come from the always-on mandatory-overlap scan, which is not
            // this rule and leaves no marker.
            auto pushed = oracle && *oracle != inst.start_ranges;
            // Verify a proof for the first few interesting instances rather than
            // all of them: the cross-check is about which bounds move, and the
            // fixtures above are where the derivation itself is scrutinised.
            auto name =
                ((pushed || ! oracle) && verified < 12) ? make_optional("disjunctive_precedences_oracle_" + std::to_string(verified)) : nullopt;
            auto probe = probe_root(inst, only_precedences, proofs ? name : nullopt);

            if (probe.refuted != ! oracle.has_value()) {
                println(cerr, "oracle disagreement on starts={} lens={}: oracle refutes {}, propagator refutes {}", inst.start_ranges,
                    inst.length_specs, ! oracle.has_value(), probe.refuted);
                fail("oracle cross-check (refutation)");
            }
            if (oracle && probe.start_bounds != *oracle) {
                println(cerr, "oracle disagreement on starts={} lens={}: oracle says {}, propagator says {}", inst.start_ranges, inst.length_specs,
                    *oracle, probe.start_bounds);
                fail("oracle cross-check (bounds)");
            }
            if (name)
                ++verified;
            if (pushed) {
                ++fired;
                if (proofs && name && probe.markers.total() == 0)
                    fail("oracle cross-check: a push left no marker");
            }

            // The rule must not cost solutions, whatever the oracle says.
            check_enumeration("random_" + std::to_string(k), inst, all_rules, nullopt);
        }

        if (fired == 0)
            fail("oracle cross-check: nothing in the corpus had a detectable precedence, so nothing was compared");
        println(cerr, "oracle cross-check: {} of 250 instances had a bound pushed at the root", fired);
    }

    // Two tasks sharing one start variable, which is UNSAT for positive
    // durations: each pair is still encoded, so the rule can detect a
    // precedence between a variable and itself and must not fall over.
    {
        Problem p;
        auto shared = p.create_integer_variable(0_i, 3_i);
        auto other = p.create_integer_variable(1_i, 10_i);
        vector<IntegerVariableID> starts{shared, shared, other};
        p.post(Disjunctive{starts, vector<Integer>{3_i, 3_i, 3_i}}.with_rules(only_precedences));

        auto name = "disjunctive_precedences_dup";
        bool reached_a_node = false, found_a_solution = false;
        solve_with(p,
            SolveCallbacks{.solution = [&](const CurrentState &) -> bool {
                               found_a_solution = true;
                               return false;
                           },
                .trace = [&](const CurrentState &) -> bool {
                    reached_a_node = true;
                    return false;
                }},
            proofs ? make_optional<ProofOptions>(ProofFileNames{name}) : nullopt);
        if (found_a_solution)
            fail("dup: two length-three tasks sharing a start cannot both be scheduled");
        if (proofs) {
            (void)reached_a_node;
            verify_proof_and_clean_up(name);
        }
    }

    // Nothing this rule does may reach the model.
    {
        check_opb_unaffected("sharp", sharp);
        check_opb_unaffected("sharp_ub", sharp_ub);
        check_opb_unaffected("chain", chain);
        check_opb_unaffected("deep", deep);
        check_opb_unaffected("tight", tight);

        std::mt19937 rand(*get_seed());
        std::uniform_int_distribution<> n_dist(2, 4), lo_dist(-2, 4), span_dist(0, 4), len_dist(0, 3);
        for (int k = 0; k < 20; ++k) {
            Instance inst;
            auto n = n_dist(rand);
            for (int i = 0; i < n; ++i) {
                auto lo = lo_dist(rand), span = span_dist(rand);
                inst.start_ranges.emplace_back(lo, lo + span);
                auto len = len_dist(rand);
                inst.length_specs.emplace_back(len, len);
            }
            check_opb_unaffected("random_" + std::to_string(k), inst);
        }
    }

    // The solutions must survive the new rule, with the proof verified.
    check_enumeration("sharp", sharp, all_rules, proofs ? make_optional("disjunctive_precedences_enum_sharp") : nullopt);
    check_enumeration("sharp_ub", sharp_ub, all_rules, proofs ? make_optional("disjunctive_precedences_enum_sharp_ub") : nullopt);
    check_enumeration("twin", twin, all_rules, proofs ? make_optional("disjunctive_precedences_enum_twin") : nullopt);
    check_enumeration("chain", chain, all_rules, proofs ? make_optional("disjunctive_precedences_enum_chain") : nullopt);
    check_enumeration("refuted", refuted, all_rules, proofs ? make_optional("disjunctive_precedences_enum_refuted") : nullopt);
    check_enumeration("deep", deep, all_rules, proofs ? make_optional("disjunctive_precedences_enum_deep") : nullopt);
    check_enumeration("tight", tight, all_rules, proofs ? make_optional("disjunctive_precedences_enum_tight") : nullopt);
    // The mutation lanes' own configuration, enumerated honestly. This is also
    // where a rule selection that stopped the propagator checking its own
    // solutions would be caught: with time-tabling's pushes off, the
    // mandatory-overlap scan is the only thing rejecting an overlapping leaf,
    // and if it were gated too this enumeration would report solutions that are
    // not.
    check_enumeration("tight_precedences_only", tight, only_precedences, proofs ? make_optional("disjunctive_precedences_enum_tight_only") : nullopt);
    for (auto strict : {true, false}) {
        Instance var{{{0, 3}, {1, 6}}, {{3, 4}, {0, 3}}, strict};
        check_enumeration(strict ? "var_strict" : "var_nonstrict", var, all_rules,
            proofs ? make_optional("disjunctive_precedences_enum_var_" + string{strict ? "strict" : "nonstrict"}) : nullopt);
    }

    return EXIT_SUCCESS;
}
