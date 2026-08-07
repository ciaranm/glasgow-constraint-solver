#include <gcs/constraints/comparison.hh>
#include <gcs/constraints/cumulative.hh>
#include <gcs/constraints/equals.hh>
#include <gcs/constraints/innards/constraints_test_utils.hh>
#include <gcs/constraints/linear.hh>
#include <gcs/exception.hh>
#include <gcs/problem.hh>
#include <gcs/solve.hh>

#include <climits>
#include <cstdlib>
#include <fstream>
#include <iostream>
#include <optional>
#include <random>
#include <set>
#include <sstream>
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
using std::mt19937;
using std::nullopt;
using std::optional;
using std::pair;
using std::set;
using std::string;
using std::stringstream;
using std::tuple;
using std::uniform_int_distribution;
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
    // The comment the presence-falsification justification writes. Tests count
    // it: a rule that never fires makes every other assertion about it vacuous,
    // and a twin instance that must not fire is only checked by counting to
    // zero. See issue #541's shared validation vocabulary.
    const string falsification_marker = "cumulative optional: task";

    // One task of an optional-Cumulative instance. A presence spec of {0, 1} is
    // a genuine decision variable; {1, 1} and {0, 0} are the constants, which
    // exercise the two ways prepare() resolves a presence away.
    struct TaskSpec
    {
        pair<int, int> start_range;
        int length;
        int height;
        pair<int, int> presence;
    };

    [[nodiscard]] auto presence_is_var(const TaskSpec & t) -> bool
    {
        return t.presence.first != t.presence.second;
    }

    // Solutions are (every start, then every *variable* presence in task
    // order). A task is active at t iff it is present and its window covers t.
    [[nodiscard]] auto make_is_satisfying(const vector<TaskSpec> & tasks, int capacity)
    {
        return [&tasks, capacity](const vector<int> & vals) {
            auto n = tasks.size();
            vector<int> present(n);
            size_t k = n;
            for (size_t i = 0; i < n; ++i)
                present[i] = presence_is_var(tasks[i]) ? vals.at(k++) : tasks[i].presence.first;

            int t_lo = INT_MAX, t_hi = INT_MIN;
            for (size_t i = 0; i < n; ++i) {
                if (! present[i] || tasks[i].length == 0 || tasks[i].height == 0)
                    continue;
                t_lo = min(t_lo, vals[i]);
                t_hi = max(t_hi, vals[i] + tasks[i].length - 1);
            }
            for (int t = t_lo; t <= t_hi; ++t) {
                int load = 0;
                for (size_t i = 0; i < n; ++i)
                    if (present[i] && vals[i] <= t && t < vals[i] + tasks[i].length)
                        load += tasks[i].height;
                if (load > capacity)
                    return false;
            }
            return true;
        };
    }

    [[nodiscard]] auto enumerated_ranges(const vector<TaskSpec> & tasks) -> vector<pair<int, int>>
    {
        vector<pair<int, int>> ranges;
        for (const auto & t : tasks)
            ranges.push_back(t.start_range);
        for (const auto & t : tasks)
            if (presence_is_var(t))
                ranges.push_back(t.presence);
        return ranges;
    }

    // Post the instance, returning the variables in enumeration order.
    auto post_optional_cumulative(Problem & p, const vector<TaskSpec> & tasks, int capacity, CumulativePresenceMutation mutation)
        -> vector<IntegerVariableID>
    {
        vector<IntegerVariableID> starts, presences, all_vars;
        for (const auto & t : tasks) {
            auto v = p.create_integer_variable(Integer{t.start_range.first}, Integer{t.start_range.second});
            starts.push_back(v);
            all_vars.push_back(v);
        }
        for (const auto & t : tasks) {
            if (presence_is_var(t)) {
                auto v = p.create_integer_variable(Integer{t.presence.first}, Integer{t.presence.second});
                presences.push_back(v);
                all_vars.push_back(v);
            }
            else
                presences.push_back(constant_variable(Integer{t.presence.first}));
        }
        vector<IntegerVariableID> lengths, heights;
        for (const auto & t : tasks) {
            lengths.push_back(constant_variable(Integer{t.length}));
            heights.push_back(constant_variable(Integer{t.height}));
        }
        p.post(Cumulative{starts, lengths, heights, presences, constant_variable(Integer{capacity})}.with_presence_mutation(mutation));
        return all_vars;
    }

    auto run_optional_test(bool proofs, const string & tag, const vector<TaskSpec> & tasks, int capacity) -> void
    {
        print(cerr, "cumulative optional {} n={} c={}{}", tag, tasks.size(), capacity, proofs ? " with proofs:" : ":");
        cerr << flush;

        set<vector<int>> expected, actual;
        build_expected(expected, make_is_satisfying(tasks, capacity), enumerated_ranges(tasks));
        println(cerr, " expecting {} solutions", expected.size());

        Problem p;
        auto all_vars = post_optional_cumulative(p, tasks, capacity, cumulative_presence_mutation::None{});

        auto proof_name = proofs ? make_optional("cumulative_optional_test_" + tag) : nullopt;
        solve_for_tests(p, proof_name, actual, tuple{all_vars});
        check_results(proof_name, expected, actual);
    }
}

namespace
{
    // How many times `needle` appears in the proof file. The falsification
    // marker is the only thing tests read the .pbp for; everything else about
    // the proof is VeriPB's business.
    [[nodiscard]] auto count_in_proof(const string & proof_name, const string & needle) -> int
    {
        ifstream f{proof_name + ".pbp"};
        if (! f) {
            println(cerr, "could not open {}.pbp to count markers", proof_name);
            return -1;
        }
        int count = 0;
        for (string line; getline(f, line);)
            if (line.find(needle) != string::npos)
                ++count;
        return count;
    }

    /// What the falsification marker count must be. Note the asymmetry: "must
    /// fire" is a claim about the root, where the fixture is arranged so the
    /// rule triggers before any branching, and it holds whatever the search
    /// does afterwards. "Must never fire" is a claim about every node, so it is
    /// only assertable on a fixture where the task fits under *every* partial
    /// assignment --- otherwise the harness's seed-derived random branching
    /// decides whether the rule fires below the root, and the test is flaky.
    enum class MarkerCount
    {
        AtLeastOne,   ///< the rule must fire
        Never,        ///< the rule must not fire at any node
        Unconstrained ///< firing below the root is legitimate here; see above
    };

    struct FalsificationExpectation
    {
        MarkerCount markers;
        int present_ones;              ///< how many solutions have this task present
        size_t falsified_task;         ///< index of the task under test
        size_t falsified_var_position; ///< its position among the enumerated variables
    };

    // A falsification fixture and its twin, checked as a pair: the same
    // enumeration check as everywhere else, plus the marker count, plus what
    // the task's presence is allowed to be in a solution.
    auto run_falsification_test(const string & tag, const vector<TaskSpec> & tasks, int capacity, const FalsificationExpectation & expect) -> bool
    {
        println(cerr, "cumulative optional falsification {} c={}", tag, capacity);

        set<vector<int>> expected, actual;
        build_expected(expected, make_is_satisfying(tasks, capacity), enumerated_ranges(tasks));

        Problem p;
        auto all_vars = post_optional_cumulative(p, tasks, capacity, cumulative_presence_mutation::None{});

        auto proof_name = "cumulative_optional_falsify_" + tag;
        solve_for_tests(p, proof_name, actual, tuple{all_vars});

        auto markers = count_in_proof(proof_name, falsification_marker);
        bool ok = true;
        switch (expect.markers) {
            using enum MarkerCount;
        case AtLeastOne:
            if (markers <= 0) {
                println(cerr, "{}: falsification marker count is {}, expected at least one", tag, markers);
                ok = false;
            }
            break;
        case Never:
            if (markers != 0) {
                println(cerr, "{}: falsification marker count is {}, expected zero", tag, markers);
                ok = false;
            }
            break;
        case Unconstrained: break;
        }

        // How many solutions leave the task present, according to brute force.
        // On a "must fire at the root" fixture, this being zero is the semantic
        // half of the marker assertion; on a twin, its being positive is what
        // says the rule did *not* fire at the root, whatever it did below.
        int present_count = 0;
        for (const auto & sol : expected)
            if (sol.at(expect.falsified_var_position) == 1)
                ++present_count;
        if (present_count != expect.present_ones) {
            println(cerr, "{}: brute force says task {} is present in {} solutions, fixture claims {}", tag, expect.falsified_task, present_count,
                expect.present_ones);
            ok = false;
        }

        check_results(make_optional(proof_name), expected, actual);
        return ok;
    }

    // Write a deliberately corrupted proof of the given instance, under
    // `proof_basename`, and leave the checking to
    // run_test_and_expect_verify_failure.bash --- which passes only if VeriPB
    // rejects it. A mutation that still verifies means the honest derivation
    // had slack, which is a finding about the derivation.
    auto write_mutated_proof(const vector<TaskSpec> & tasks, int capacity, CumulativePresenceMutation mutation, const string & proof_basename) -> void
    {
        set<vector<int>> actual;
        Problem p;
        auto all_vars = post_optional_cumulative(p, tasks, capacity, mutation);
        // Deliberately not check_results: ClaimOneTooFar draws a wrong
        // conclusion, so the solution set is wrong too, and that is the point.
        solve_for_tests(p, make_optional(proof_basename), actual, tuple{all_vars});
        println(cerr, "wrote a deliberately corrupted proof to {}.pbp", proof_basename);
    }
}

namespace
{
    // The OPB's constraints, so two models can be compared line for line. The
    // s-expression goes to the .scp, so what is left here is exactly the
    // pseudo-Boolean model --- minus the `*` comment lines, which include the
    // per-constraint block header naming the constraint type. That header is
    // *meant* to differ between the two forms (they are different constraint
    // types, and cake_pb_cp dispatches on the name), and it is the one thing
    // here that is not part of the model.
    [[nodiscard]] auto read_opb_constraints(const string & proof_name) -> optional<vector<string>>
    {
        ifstream f{proof_name + ".opb"};
        if (! f)
            return nullopt;
        vector<string> lines;
        for (string line; getline(f, line);)
            if (! line.starts_with("*"))
                lines.push_back(line);
        return lines;
    }

    [[nodiscard]] auto opb_names_constraint_type(const string & proof_name, const string & type) -> bool
    {
        ifstream f{proof_name + ".opb"};
        for (string line; getline(f, line);)
            if (line.starts_with("* constraint " + type + " "))
                return true;
        return false;
    }

    // The optional form must degenerate structurally, not by emitting a
    // constant-true conjunct: posting every presence as the constant 1 has to
    // produce the same OPB as not passing presences at all. That is what keeps
    // the non-optional constructors' encoding --- and every proof already
    // written against it --- untouched by this feature.
    auto check_constant_presence_encoding_is_unchanged() -> bool
    {
        vector<pair<int, int>> start_ranges{{0, 3}, {0, 3}, {0, 4}};
        vector<int> lengths{2, 2, 3}, heights{1, 2, 1};
        Integer capacity{3_i};

        auto build = [&](bool optional_form, const string & proof_name) -> optional<vector<string>> {
            Problem p;
            vector<IntegerVariableID> starts, lengths_v, heights_v, presences;
            for (auto & [lo, hi] : start_ranges)
                starts.push_back(p.create_integer_variable(Integer{lo}, Integer{hi}));
            for (auto l : lengths)
                lengths_v.push_back(constant_variable(Integer{l}));
            for (auto h : heights)
                heights_v.push_back(constant_variable(Integer{h}));
            for (size_t i = 0; i < starts.size(); ++i)
                presences.push_back(constant_variable(1_i));

            if (optional_form)
                p.post(Cumulative{starts, lengths_v, heights_v, presences, constant_variable(capacity)});
            else
                p.post(Cumulative{starts, lengths_v, heights_v, constant_variable(capacity)});

            set<vector<int>> results;
            solve_for_tests(p, make_optional(proof_name), results, tuple{starts});
            auto opb = read_opb_constraints(proof_name);
            bool named_right = opb_names_constraint_type(proof_name, optional_form ? "cumulative_optional" : "cumulative");
            dispose_of_proof_files(proof_name);
            if (! named_right) {
                println(cerr, "constant-presence encoding check: the {} form's OPB does not name its constraint type",
                    optional_form ? "optional" : "plain");
                return nullopt;
            }
            return opb;
        };

        // Solution-set equivalence too, over a random corpus: the OPB check
        // above says the two models are the same pseudo-Boolean formula, and
        // this says the two constraints propagate to the same solutions, which
        // is the property a user of the new constructor actually relies on.
        mt19937 rand(*get_seed());
        for (int k = 0; k < 15; ++k) {
            uniform_int_distribution<> n_dist(2, 3), lo_dist(0, 3), span_dist(0, 3), len_dist(0, 3), ht_dist(0, 2), cap_dist(0, 3);
            auto n = static_cast<size_t>(n_dist(rand));
            vector<TaskSpec> tasks;
            for (size_t i = 0; i < n; ++i) {
                auto lo = lo_dist(rand);
                tasks.push_back(TaskSpec{{lo, min(lo + span_dist(rand), 3)}, len_dist(rand), ht_dist(rand), {1, 1}});
            }
            auto capacity = cap_dist(rand);

            set<vector<int>> with_presences, without;
            {
                Problem p;
                auto all_vars = post_optional_cumulative(p, tasks, capacity, cumulative_presence_mutation::None{});
                solve_for_tests(p, nullopt, with_presences, tuple{all_vars});
            }
            {
                Problem p;
                vector<IntegerVariableID> starts, lengths_v, heights_v;
                for (const auto & t : tasks)
                    starts.push_back(p.create_integer_variable(Integer{t.start_range.first}, Integer{t.start_range.second}));
                for (const auto & t : tasks) {
                    lengths_v.push_back(constant_variable(Integer{t.length}));
                    heights_v.push_back(constant_variable(Integer{t.height}));
                }
                p.post(Cumulative{starts, lengths_v, heights_v, constant_variable(Integer{capacity})});
                solve_for_tests(p, nullopt, without, tuple{starts});
            }
            if (with_presences != without) {
                println(cerr, "constant-presence equivalence {}: optional form has {} solutions, plain form has {}", k, with_presences.size(),
                    without.size());
                return false;
            }
        }

        auto plain = build(false, "cumulative_optional_encoding_plain");
        auto optional_form = build(true, "cumulative_optional_encoding_opt");
        if (! plain || ! optional_form) {
            println(cerr, "constant-presence encoding check: could not read an OPB back");
            return false;
        }
        if (*plain != *optional_form) {
            println(cerr, "constant-presence encoding check: the optional form's OPB differs from the plain form's");
            for (size_t i = 0; i < max(plain->size(), optional_form->size()); ++i) {
                auto a = i < plain->size() ? (*plain)[i] : "<end>";
                auto b = i < optional_form->size() ? (*optional_form)[i] : "<end>";
                if (a != b)
                    println(cerr, "  line {}: plain {:?} vs optional {:?}", i + 1, a, b);
            }
            return false;
        }
        return true;
    }
}

namespace
{
    // Semantic drift detector. Model the same instance two ways --- presence
    // Booleans, and heights channelled to {0, h} --- and require the same
    // solution count under the bijection present_i = 1 <-> h_i = h. This pins
    // "absent consumes nothing" against a formulation that shares none of the
    // optional-task code path, including at the zero-length and zero-height
    // edges where "absent" and "present but weightless" look the same.
    auto check_bijection(const string & tag, const vector<TaskSpec> & tasks, int capacity) -> bool
    {
        set<vector<int>> via_presence, via_height;

        {
            Problem p;
            vector<IntegerVariableID> starts, lengths_v, heights_v, presences, all_vars;
            for (const auto & t : tasks)
                starts.push_back(p.create_integer_variable(Integer{t.start_range.first}, Integer{t.start_range.second}));
            for (const auto & t : tasks) {
                lengths_v.push_back(constant_variable(Integer{t.length}));
                heights_v.push_back(constant_variable(Integer{t.height}));
                presences.push_back(p.create_integer_variable(0_i, 1_i));
            }
            p.post(Cumulative{starts, lengths_v, heights_v, presences, constant_variable(Integer{capacity})});
            all_vars = starts;
            all_vars.insert(all_vars.end(), presences.begin(), presences.end());
            solve_for_tests(p, nullopt, via_presence, tuple{all_vars});
        }

        {
            Problem p;
            vector<IntegerVariableID> starts, lengths_v, heights_v, presences, all_vars;
            for (const auto & t : tasks)
                starts.push_back(p.create_integer_variable(Integer{t.start_range.first}, Integer{t.start_range.second}));
            for (const auto & t : tasks) {
                lengths_v.push_back(constant_variable(Integer{t.length}));
                // h_i in {0, h}, channelled to the presence Boolean. A height of
                // 0 makes both branches the same variable, which is the honest
                // encoding of "this task consumes nothing either way".
                auto h = p.create_integer_variable(0_i, Integer{t.height});
                auto present = p.create_integer_variable(0_i, 1_i);
                p.post(LinearEquality{WeightedSum{} + 1_i * h + -Integer{t.height} * present, 0_i});
                heights_v.push_back(h);
                presences.push_back(present);
            }
            p.post(Cumulative{starts, lengths_v, heights_v, constant_variable(Integer{capacity})});
            all_vars = starts;
            all_vars.insert(all_vars.end(), presences.begin(), presences.end());
            solve_for_tests(p, nullopt, via_height, tuple{all_vars});
        }

        if (via_presence != via_height) {
            println(cerr, "bijection {}: presence model has {} solutions, variable-height model has {}", tag, via_presence.size(), via_height.size());
            for (const auto & sol : via_presence)
                if (! via_height.contains(sol))
                    println(cerr, "  only in the presence model: {}", sol);
            for (const auto & sol : via_height)
                if (! via_presence.contains(sol))
                    println(cerr, "  only in the variable-height model: {}", sol);
            return false;
        }
        println(cerr, "bijection {}: {} solutions agree", tag, via_presence.size());
        return true;
    }
}

namespace
{
    // The motivating use case: maximise the number of scheduled tasks, with the
    // optimum proved. This is also the only test that puts a presence variable
    // in the objective, so it is what exercises presence literals on the
    // objective's proof path.
    auto check_objective(const string & tag, const vector<TaskSpec> & tasks, int capacity, int expected_optimum) -> bool
    {
        Problem p;
        vector<IntegerVariableID> starts, lengths_v, heights_v, presences;
        for (const auto & t : tasks)
            starts.push_back(p.create_integer_variable(Integer{t.start_range.first}, Integer{t.start_range.second}));
        for (const auto & t : tasks) {
            lengths_v.push_back(constant_variable(Integer{t.length}));
            heights_v.push_back(constant_variable(Integer{t.height}));
            presences.push_back(p.create_integer_variable(0_i, 1_i));
        }
        p.post(Cumulative{starts, lengths_v, heights_v, presences, constant_variable(Integer{capacity})});

        auto scheduled = p.create_integer_variable(0_i, Integer(static_cast<long long>(tasks.size())), "scheduled");
        WeightedSum count;
        for (const auto & v : presences)
            count += 1_i * v;
        p.post(LinearEquality{count + -1_i * scheduled, 0_i});
        p.maximise(scheduled);

        auto proof_name = "cumulative_optional_objective_" + tag;
        optional<int> best;
        solve_for_tests_with_callbacks(
            p, make_optional(proof_name),
            [&](const CurrentState & s) -> bool {
                best = static_cast<int>(s(scheduled).raw_value);
                return true;
            },
            [](const CurrentState &) -> bool { return true; });

        bool ok = true;
        if (best != make_optional(expected_optimum)) {
            println(cerr, "objective {}: optimum is {}, expected {}", tag, best ? std::to_string(*best) : "none", expected_optimum);
            ok = false;
        }
        if (! verify_proof_and_dispose(proof_name)) {
            println(cerr, "objective {}: proof did not verify", tag);
            ok = false;
        }
        else
            println(cerr, "objective {}: optimum {} verified", tag, expected_optimum);
        return ok;
    }
}

namespace
{
    auto expect_bad_presence_throws(const char * label, pair<int, int> presence_domain) -> bool
    {
        Problem p;
        auto s = p.create_integer_variable(0_i, 3_i, "s");
        auto present = p.create_integer_variable(Integer{presence_domain.first}, Integer{presence_domain.second}, "present");
        p.post(Cumulative{vector<IntegerVariableID>{s}, vector<IntegerVariableID>{constant_variable(2_i)},
            vector<IntegerVariableID>{constant_variable(1_i)}, vector<IntegerVariableID>{present}, constant_variable(1_i)});
        try {
            solve(p, [](const CurrentState &) { return true; });
        }
        catch (const InvalidProblemDefinitionException &) {
            return true;
        }
        println(cerr, "{}: expected InvalidProblemDefinitionException", label);
        return false;
    }

    auto expect_mismatched_sizes_throws() -> bool
    {
        Problem p;
        auto s = p.create_integer_variable(0_i, 3_i, "s");
        try {
            p.post(Cumulative{vector<IntegerVariableID>{s}, vector<IntegerVariableID>{constant_variable(2_i)},
                vector<IntegerVariableID>{constant_variable(1_i)}, vector<IntegerVariableID>{}, constant_variable(1_i)});
        }
        catch (const InvalidProblemDefinitionException &) {
            return true;
        }
        println(cerr, "mismatched presence array size: expected InvalidProblemDefinitionException");
        return false;
    }
}

namespace
{
    // The sharp-margin falsification family. Three blockers with pairwise
    // coprime heights saturate the horizon to exactly one unit below what the
    // optional task needs, so every coefficient in the emitted derivation is
    // load-bearing: drop any one blocker and the task fits. Task 0 is the
    // optional one under test; the rest are present and start-fixed.
    //
    // The horizon is chosen so the chain runs four steps (blocked times 1, 3, 5
    // and 7, one length apart), which is what gives the omit-a-step mutation
    // something to omit.
    [[nodiscard]] auto sharp_margin_tasks(int blocker_length) -> vector<TaskSpec>
    {
        return {
            TaskSpec{{0, 7}, 2, 7, {0, 1}}, // the optional task under test
            TaskSpec{{0, 0}, blocker_length, 5, {1, 1}},
            TaskSpec{{0, 0}, blocker_length, 8, {1, 1}},
            TaskSpec{{0, 0}, blocker_length, 11, {1, 1}},
        };
    }
    constexpr int sharp_margin_capacity = 30; // 5 + 8 + 11 = 24, and 24 + 7 = 31 > 30 by exactly one
}

auto main(int argc, char * argv[]) -> int
{
    establish_and_announce_seed(argc, argv);

    // Mutation lanes come in through run_test_and_expect_verify_failure.bash,
    // which prepends its own flags, so the mutation is selected by scanning
    // argv rather than from the positional mode. The harness runs veripb and
    // passes only if it rejects what we write here; all this binary has to do
    // is write the corrupted proof and exit successfully.
    optional<CumulativePresenceMutation> mutation;
    vector<TaskSpec> mutation_tasks;
    string proof_basename = "cumulative_optional_mutation";
    for (int a = 1; a < argc; ++a) {
        string arg = argv[a];
        // The chain argues about a different optional task than the one being
        // falsified, so the pinned activity is not implied by anything. Needs a
        // second optional task to point at.
        if (arg == "--mutate=wrong_task") {
            mutation = cumulative_presence_mutation::WrongTask{};
            mutation_tasks = sharp_margin_tasks(9);
            mutation_tasks.push_back(TaskSpec{{0, 7}, 2, 7, {0, 1}});
        }
        // The control: no chain at all. The order atoms the wrapping RUP would
        // need are created *by* the chain, so a proof without it does not close.
        // If this lane ever starts verifying, the chain has become decoration
        // and the other mutations are checking nothing.
        else if (arg == "--mutate=emit_nothing") {
            mutation = cumulative_presence_mutation::EmitNothing{};
            mutation_tasks = sharp_margin_tasks(9);
        }
        // Sharp margin: on the twin where exactly one placement still fits,
        // falsifying anyway is a wrong inference, and the chain runs out of
        // blocked times before it can pretend otherwise.
        else if (arg == "--mutate=one_too_far") {
            mutation = cumulative_presence_mutation::ClaimOneTooFar{};
            mutation_tasks = sharp_margin_tasks(7);
        }
        else if (arg == "--proof-files-basename" && a + 1 < argc)
            proof_basename = argv[++a];
    }

    if (mutation) {
        write_mutated_proof(mutation_tasks, sharp_margin_capacity, *mutation, proof_basename);
        return EXIT_SUCCESS;
    }

    string mode = argc >= 2 ? argv[1] : "enumerate";
    bool ok = true;

    if (mode == "enumerate") {
        // Rejections first: a presence outside {0, 1} and a mismatched array
        // are modelling errors, not silently-reinterpreted input.
        ok &= expect_bad_presence_throws("presence 0..2", {0, 2});
        ok &= expect_bad_presence_throws("presence -1..1", {-1, 1});
        ok &= expect_mismatched_sizes_throws();
        if (! ok)
            return EXIT_FAILURE;

        ok &= check_constant_presence_encoding_is_unchanged();
        if (! ok)
            return EXIT_FAILURE;

        vector<pair<string, pair<vector<TaskSpec>, int>>> data{
            // Two optional unit-height tasks, capacity 1: they may not overlap,
            // but either or both may simply be absent, so the all-absent
            // solution and both singletons are all in.
            {"pair_cap1", {{{{0, 3}, 2, 1, {0, 1}}, {{0, 3}, 2, 1, {0, 1}}}, 1}},
            // The same, capacity 2: presence never matters.
            {"pair_cap2", {{{{0, 3}, 2, 1, {0, 1}}, {{0, 3}, 2, 1, {0, 1}}}, 2}},
            // One mandatory task and one optional one it can block.
            {"one_mandatory", {{{{0, 2}, 3, 2, {1, 1}}, {{0, 2}, 2, 2, {0, 1}}}, 3}},
            // A constantly-absent task: it must drop out entirely, so its start
            // is free and it consumes nothing even where it would not fit.
            {"const_absent", {{{{0, 2}, 3, 5, {0, 0}}, {{0, 2}, 3, 1, {1, 1}}}, 1}},
            // A task whose height is 0: present or absent, it is weightless.
            {"zero_height", {{{{0, 2}, 2, 0, {0, 1}}, {{0, 2}, 2, 1, {1, 1}}}, 1}},
            // A task whose length is 0: present or absent, it occupies nothing.
            {"zero_length", {{{{0, 2}, 0, 3, {0, 1}}, {{0, 2}, 2, 1, {1, 1}}}, 1}},
            // Every task optional and capacity 0: nothing with a positive height
            // may be present at all, so the only solution set is the absent one
            // crossed with every start.
            {"cap_zero", {{{{0, 2}, 1, 1, {0, 1}}, {{0, 2}, 1, 1, {0, 1}}}, 0}},
            // A task that cannot fit even alone: its presence is false at the
            // root, with no search needed.
            {"never_fits", {{{{0, 2}, 2, 5, {0, 1}}, {{0, 2}, 2, 1, {1, 1}}}, 3}},
            // Three optional tasks over a tight horizon.
            {"three_tight", {{{{0, 2}, 2, 1, {0, 1}}, {{0, 2}, 1, 1, {0, 1}}, {{0, 2}, 1, 1, {0, 1}}}, 2}},
            // Negative starts, so the per-task windows and the flags span t < 0.
            {"neg_start", {{{{-2, 1}, 2, 1, {0, 1}}, {{-2, 1}, 2, 1, {0, 1}}}, 1}},
            // A fixed start on an optional task: nothing to push, but its
            // presence can still be decided.
            {"fixed_start", {{{{1, 1}, 2, 2, {0, 1}}, {{0, 2}, 2, 2, {1, 1}}}, 3}},
            // The only instance here that reaches the (TTOC) strengthening
            // with an undecided task among the outside-the-window ones. Task 0
            // saturates the horizon without overflowing it, and is excluded
            // from the energy set by its {0, 1} start, so it contributes only
            // profile; task 1 has no mandatory part but cannot be placed
            // anywhere, which the check catches only by adding that profile
            // from outside the window; task 2 is undecided with a mandatory
            // part overlapping it. Coverage of the path, not a tripwire: by the
            // time the pins are emitted the reason context is contradictory, so
            // pinning the undecided task too would verify anyway.
            {"ttoc_undecided_outside", {{{{0, 1}, 10, 10, {1, 1}}, {{2, 6}, 4, 1, {1, 1}}, {{2, 2}, 4, 1, {0, 1}}}, 10}},
            // Mixed constants: one always present, one always absent, one free.
            {"mixed_consts", {{{{0, 2}, 2, 2, {1, 1}}, {{0, 2}, 2, 2, {0, 0}}, {{0, 2}, 2, 1, {0, 1}}}, 3}},
        };

        mt19937 rand(*get_seed());
        // Random instances for breadth, all tasks optional so the presence
        // cross-product is exercised everywhere. Kept small: enumeration is over
        // starts times presences, so the space grows fast.
        for (int k = 0; k < 20; ++k) {
            uniform_int_distribution<> n_dist(2, 3), lo_dist(0, 3), span_dist(0, 3), len_dist(0, 3), ht_dist(0, 2), cap_dist(0, 3), pres_dist(0, 3);
            vector<TaskSpec> tasks;
            auto n = n_dist(rand);
            for (int i = 0; i < n; ++i) {
                auto lo = lo_dist(rand);
                auto p = pres_dist(rand);
                tasks.push_back(TaskSpec{
                    {lo, min(lo + span_dist(rand), 3)}, len_dist(rand), ht_dist(rand), p == 0 ? pair{1, 1} : (p == 1 ? pair{0, 0} : pair{0, 1})});
            }
            data.emplace_back("random" + std::to_string(k), pair{tasks, cap_dist(rand)});
        }

        for (bool proofs : {false, true}) {
            if (proofs && ! can_run_veripb())
                continue;
            for (const auto & [tag, instance] : data)
                run_optional_test(proofs, tag, instance.first, instance.second);
        }
    }
    else if (mode == "falsify") {
        if (! can_run_veripb()) {
            println(cerr, "veripb not available, skipping falsification tests");
            return EXIT_SUCCESS;
        }

        // Sharp margin: the blockers saturate the whole horizon to one unit
        // below what the optional task needs, so it can go nowhere, the rule
        // fires at the root, and its presence is false in every solution.
        ok &= run_falsification_test("sharp", sharp_margin_tasks(9), sharp_margin_capacity,
            FalsificationExpectation{.markers = MarkerCount::AtLeastOne, .present_ones = 0, .falsified_task = 0, .falsified_var_position = 4});

        // Twin, one unit the other side of the threshold: capacity 31 leaves
        // exactly enough room. Nothing is ever blocked, at the root or below it,
        // so this is the twin that can carry the marker-count-zero assertion,
        // and all 8 starts stay available with the task present.
        ok &= run_falsification_test("twin_capacity", sharp_margin_tasks(9), sharp_margin_capacity + 1,
            FalsificationExpectation{.markers = MarkerCount::Never, .present_ones = 8, .falsified_task = 0, .falsified_var_position = 4});

        // Twin, the other way: the blockers stop two time points earlier, so the
        // tail of the horizon has room for exactly one placement --- start 7.
        // That one surviving solution is what says the rule did not fire at the
        // root. It legitimately *does* fire below the root, once branching has
        // ruled that start out, so the marker count here is a function of the
        // search seed and is not asserted on.
        ok &= run_falsification_test("twin_window", sharp_margin_tasks(7), sharp_margin_capacity,
            FalsificationExpectation{.markers = MarkerCount::Unconstrained, .present_ones = 1, .falsified_task = 0, .falsified_var_position = 4});

        // A second optional task, so the wrong-task mutation has somewhere
        // wrong to point. Both are falsified.
        auto two_optional = sharp_margin_tasks(9);
        two_optional.push_back(TaskSpec{{0, 7}, 2, 7, {0, 1}});
        ok &= run_falsification_test("two_optional", two_optional, sharp_margin_capacity,
            FalsificationExpectation{.markers = MarkerCount::AtLeastOne, .present_ones = 0, .falsified_task = 0, .falsified_var_position = 5});

        if (! ok)
            return EXIT_FAILURE;
    }
    else if (mode == "bijection") {
        ok &= check_bijection("pair_cap1", {{{0, 3}, 2, 1, {0, 1}}, {{0, 3}, 2, 1, {0, 1}}}, 1);
        ok &= check_bijection("three", {{{0, 2}, 2, 2, {0, 1}}, {{0, 2}, 1, 1, {0, 1}}, {{0, 2}, 2, 1, {0, 1}}}, 2);
        ok &= check_bijection("zero_edges", {{{0, 2}, 0, 2, {0, 1}}, {{0, 2}, 2, 0, {0, 1}}, {{0, 2}, 2, 2, {0, 1}}}, 2);
        ok &= check_bijection("cap_zero", {{{0, 2}, 1, 1, {0, 1}}, {{0, 2}, 1, 1, {0, 1}}}, 0);
        ok &= check_bijection("neg_start", {{{-2, 1}, 2, 1, {0, 1}}, {{-2, 1}, 2, 2, {0, 1}}}, 2);
        if (! ok)
            return EXIT_FAILURE;
    }
    else if (mode == "objective") {
        if (! can_run_veripb()) {
            println(cerr, "veripb not available, skipping objective tests");
            return EXIT_SUCCESS;
        }
        // Three unit-height tasks of length 2 over t in 0..3, capacity 1: at
        // most two fit end to end, so the optimum is 2.
        ok &= check_objective("pack_two", {{{0, 2}, 2, 1, {0, 1}}, {{0, 2}, 2, 1, {0, 1}}, {{0, 2}, 2, 1, {0, 1}}}, 1, 2);
        // One task cannot fit at all, so the optimum is one short of the count.
        ok &= check_objective("one_too_big", {{{0, 2}, 2, 5, {0, 1}}, {{0, 2}, 2, 1, {0, 1}}, {{0, 2}, 2, 1, {0, 1}}}, 2, 2);
        if (! ok)
            return EXIT_FAILURE;
    }
    else {
        println(cerr, "unknown mode {}", mode);
        return EXIT_FAILURE;
    }

    return ok ? EXIT_SUCCESS : EXIT_FAILURE;
}
