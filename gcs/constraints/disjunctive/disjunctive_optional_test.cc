#include <gcs/constraints/cumulative.hh>
#include <gcs/constraints/disjunctive.hh>
#include <gcs/constraints/innards/constraints_test_utils.hh>
#include <gcs/constraints/linear.hh>
#include <gcs/exception.hh>
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
using std::mt19937;
using std::nullopt;
using std::optional;
using std::pair;
using std::set;
using std::string;
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
    // zero.
    const string falsification_marker = "disjunctive optional: task";

    // One task of an optional-Disjunctive instance. A presence spec of {0, 1} is
    // a genuine decision variable; {1, 1} and {0, 0} are the constants, which
    // exercise the two ways prepare() resolves a presence away. A length spec of
    // {a, b} with a != b is a variable duration.
    struct TaskSpec
    {
        pair<int, int> start_range;
        pair<int, int> length;
        pair<int, int> presence;
    };

    [[nodiscard]] auto is_var(pair<int, int> spec) -> bool
    {
        return spec.first != spec.second;
    }

    // Solutions are (every start, then every *variable* length, then every
    // *variable* presence, each in task order).
    [[nodiscard]] auto make_is_satisfying(const vector<TaskSpec> & tasks, bool strict)
    {
        return [&tasks, strict](const vector<int> & vals) {
            auto n = tasks.size();
            vector<int> length(n), present(n);
            size_t k = n;
            for (size_t i = 0; i < n; ++i)
                length[i] = is_var(tasks[i].length) ? vals.at(k++) : tasks[i].length.first;
            for (size_t i = 0; i < n; ++i)
                present[i] = is_var(tasks[i].presence) ? vals.at(k++) : tasks[i].presence.first;

            for (size_t i = 0; i < n; ++i)
                for (size_t j = i + 1; j < n; ++j) {
                    // An absent task occupies no time, so it constrains nobody
                    // and nobody constrains it.
                    if (! present[i] || ! present[j])
                        continue;
                    // Non-strict: pairs involving a zero-length task float freely.
                    if (! strict && (length[i] == 0 || length[j] == 0))
                        continue;
                    if (vals[i] + length[i] > vals[j] && vals[j] + length[j] > vals[i])
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
            if (is_var(t.length))
                ranges.push_back(t.length);
        for (const auto & t : tasks)
            if (is_var(t.presence))
                ranges.push_back(t.presence);
        return ranges;
    }

    // Post the instance, returning the variables in enumeration order.
    auto post_optional_disjunctive(Problem & p, const vector<TaskSpec> & tasks, bool strict, DisjunctivePresenceMutation mutation)
        -> vector<IntegerVariableID>
    {
        vector<IntegerVariableID> starts, lengths, presences, all_vars;
        for (const auto & t : tasks) {
            auto v = p.create_integer_variable(Integer{t.start_range.first}, Integer{t.start_range.second});
            starts.push_back(v);
            all_vars.push_back(v);
        }
        for (const auto & t : tasks) {
            if (is_var(t.length)) {
                auto v = p.create_integer_variable(Integer{t.length.first}, Integer{t.length.second});
                lengths.push_back(v);
                all_vars.push_back(v);
            }
            else
                lengths.push_back(constant_variable(Integer{t.length.first}));
        }
        for (const auto & t : tasks) {
            if (is_var(t.presence)) {
                auto v = p.create_integer_variable(Integer{t.presence.first}, Integer{t.presence.second});
                presences.push_back(v);
                all_vars.push_back(v);
            }
            else
                presences.push_back(constant_variable(Integer{t.presence.first}));
        }
        p.post(Disjunctive{starts, lengths, presences}.with_strict(strict).with_presence_mutation(mutation));
        return all_vars;
    }

    auto run_optional_test(bool proofs, const string & tag, const vector<TaskSpec> & tasks, bool strict) -> void
    {
        print(cerr, "disjunctive{} optional {} n={}{}", strict ? "_strict" : "", tag, tasks.size(), proofs ? " with proofs:" : ":");
        cerr << flush;

        set<vector<int>> expected, actual;
        build_expected(expected, make_is_satisfying(tasks, strict), enumerated_ranges(tasks));
        println(cerr, " expecting {} solutions", expected.size());

        Problem p;
        auto all_vars = post_optional_disjunctive(p, tasks, strict, disjunctive_presence_mutation::None{});

        auto proof_name = proofs ? make_optional("disjunctive_optional_test_" + tag) : nullopt;
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
        int present_ones;      ///< how many solutions have this task present
        size_t falsified_task; ///< index of the task under test
    };

    // Where the task's presence sits in an enumerated solution: after every
    // start and every variable length, then in task order among the variable
    // presences. Derived rather than written down per fixture, because getting
    // it wrong reads a *start* instead and the assertion then passes or fails
    // for reasons that have nothing to do with the rule.
    [[nodiscard]] auto presence_position(const vector<TaskSpec> & tasks, size_t task) -> size_t
    {
        auto at = tasks.size();
        for (const auto & t : tasks)
            if (is_var(t.length))
                ++at;
        for (size_t i = 0; i < task; ++i)
            if (is_var(tasks[i].presence))
                ++at;
        return at;
    }

    // A falsification fixture and its twin, checked as a pair: the same
    // enumeration check as everywhere else, plus the marker count, plus what
    // the task's presence is allowed to be in a solution.
    auto run_falsification_test(const string & tag, const vector<TaskSpec> & tasks, const FalsificationExpectation & expect) -> bool
    {
        println(cerr, "disjunctive optional falsification {}", tag);

        set<vector<int>> expected, actual;
        build_expected(expected, make_is_satisfying(tasks, true), enumerated_ranges(tasks));

        Problem p;
        auto all_vars = post_optional_disjunctive(p, tasks, true, disjunctive_presence_mutation::None{});

        auto proof_name = "disjunctive_optional_falsify_" + tag;
        solve_for_tests(p, make_optional(proof_name), actual, tuple{all_vars});

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
        auto position = presence_position(tasks, expect.falsified_task);
        for (const auto & sol : expected)
            if (sol.at(position) == 1)
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
    auto write_mutated_proof(const vector<TaskSpec> & tasks, DisjunctivePresenceMutation mutation, const string & proof_basename) -> void
    {
        set<vector<int>> actual;
        Problem p;
        auto all_vars = post_optional_disjunctive(p, tasks, true, mutation);
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

    auto report_opb_difference(const string & what, const vector<string> & plain, const vector<string> & optional_form) -> void
    {
        println(cerr, "{}: the optional form's OPB differs from the plain form's", what);
        for (size_t i = 0; i < max(plain.size(), optional_form.size()); ++i) {
            auto a = i < plain.size() ? plain[i] : "<end>";
            auto b = i < optional_form.size() ? optional_form[i] : "<end>";
            if (a != b)
                println(cerr, "  line {}: plain {:?} vs optional {:?}", i + 1, a, b);
        }
    }

    // The optional form must degenerate structurally, not by emitting a
    // constant-true disjunct: posting every presence as the constant 1 has to
    // produce the same OPB as not passing presences at all. That is what keeps
    // the non-optional constructors' encoding --- and every proof already
    // written against it --- untouched by this feature.
    auto check_constant_presence_encoding_is_unchanged(bool strict) -> bool
    {
        vector<pair<int, int>> start_ranges{{0, 3}, {0, 3}, {0, 4}};
        vector<int> lengths{2, 2, 3};

        auto build = [&](bool optional_form, const string & proof_name) -> optional<vector<string>> {
            Problem p;
            vector<IntegerVariableID> starts, lengths_v, presences;
            for (auto & [lo, hi] : start_ranges)
                starts.push_back(p.create_integer_variable(Integer{lo}, Integer{hi}));
            for (auto l : lengths)
                lengths_v.push_back(constant_variable(Integer{l}));
            for (size_t i = 0; i < starts.size(); ++i)
                presences.push_back(constant_variable(1_i));

            if (optional_form)
                p.post(Disjunctive{starts, lengths_v, presences}.with_strict(strict));
            else
                p.post(Disjunctive{starts, lengths_v}.with_strict(strict));

            set<vector<int>> results;
            solve_for_tests(p, make_optional(proof_name), results, tuple{starts});
            auto opb = read_opb_constraints(proof_name);
            auto expected_type = string{strict ? "disjunctive_strict" : "disjunctive"} + (optional_form ? "_optional" : "");
            bool named_right = opb_names_constraint_type(proof_name, expected_type);
            dispose_of_proof_files(proof_name);
            if (! named_right) {
                println(cerr, "constant-presence encoding check: the {} form's OPB does not name itself {}", optional_form ? "optional" : "plain",
                    expected_type);
                return nullopt;
            }
            return opb;
        };

        auto suffix = strict ? "_strict" : "";
        auto plain = build(false, string{"disjunctive_optional_encoding_plain"} + suffix);
        auto optional_form = build(true, string{"disjunctive_optional_encoding_opt"} + suffix);
        if (! plain || ! optional_form) {
            println(cerr, "constant-presence encoding check: could not read an OPB back");
            return false;
        }
        if (*plain != *optional_form) {
            report_opb_difference("constant-presence encoding check", *plain, *optional_form);
            return false;
        }

        // Solution-set equivalence too, over a random corpus: the OPB check
        // above says the two models are the same pseudo-Boolean formula, and
        // this says the two constraints propagate to the same solutions, which
        // is the property a user of the new constructor actually relies on.
        mt19937 rand(*get_seed());
        for (int k = 0; k < 15; ++k) {
            uniform_int_distribution<> n_dist(2, 3), lo_dist(0, 3), span_dist(0, 3), len_dist(0, 3);
            auto n = static_cast<size_t>(n_dist(rand));
            vector<TaskSpec> tasks;
            for (size_t i = 0; i < n; ++i) {
                auto lo = lo_dist(rand);
                auto len = len_dist(rand);
                tasks.push_back(TaskSpec{{lo, min(lo + span_dist(rand), 3)}, {len, len}, {1, 1}});
            }

            set<vector<int>> with_presences, without;
            {
                Problem p;
                auto all_vars = post_optional_disjunctive(p, tasks, strict, disjunctive_presence_mutation::None{});
                solve_for_tests(p, nullopt, with_presences, tuple{all_vars});
            }
            {
                Problem p;
                vector<IntegerVariableID> starts, lengths_v;
                for (const auto & t : tasks)
                    starts.push_back(p.create_integer_variable(Integer{t.start_range.first}, Integer{t.start_range.second}));
                for (const auto & t : tasks)
                    lengths_v.push_back(constant_variable(Integer{t.length.first}));
                p.post(Disjunctive{starts, lengths_v}.with_strict(strict));
                solve_for_tests(p, nullopt, without, tuple{starts});
            }
            if (with_presences != without) {
                println(cerr, "constant-presence equivalence {}: optional form has {} solutions, plain form has {}", k, with_presences.size(),
                    without.size());
                return false;
            }
        }
        return true;
    }

    // What optional tasks are allowed to cost the encoding, stated as a diff.
    // Build the same instance twice --- once with genuine {0, 1} presence
    // variables, once with the same variables created and left out of the
    // constraint --- so the two problems declare identical variables and the
    // OPBs are comparable line for line. Every line must then match, except the
    // separation clauses, each of which must be the plain form's clause with
    // exactly the two presence literals appended.
    //
    // This is the design commitment #735 is built on: presence rides on the
    // clause the pair already had, so no proof step gets a new row to cite and
    // the pols are the ones that were there before.
    auto check_optional_costs_only_the_clause_literals(bool strict) -> bool
    {
        vector<pair<int, int>> start_ranges{{0, 3}, {0, 3}, {0, 4}};
        vector<int> lengths{2, 2, 3};

        auto build = [&](bool optional_form, const string & proof_name) -> optional<vector<string>> {
            Problem p;
            vector<IntegerVariableID> starts, lengths_v, presences;
            for (auto & [lo, hi] : start_ranges)
                starts.push_back(p.create_integer_variable(Integer{lo}, Integer{hi}));
            for (auto l : lengths)
                lengths_v.push_back(constant_variable(Integer{l}));
            // Created either way, so the variable declarations match; only the
            // optional form hands them to the constraint.
            for (size_t i = 0; i < starts.size(); ++i)
                presences.push_back(p.create_integer_variable(0_i, 1_i));

            if (optional_form)
                p.post(Disjunctive{starts, lengths_v, presences}.with_strict(strict));
            else
                p.post(Disjunctive{starts, lengths_v}.with_strict(strict));

            set<vector<int>> results;
            solve_for_tests(p, make_optional(proof_name), results, tuple{starts});
            auto opb = read_opb_constraints(proof_name);
            dispose_of_proof_files(proof_name);
            return opb;
        };

        auto suffix = strict ? "_strict" : "";
        auto plain = build(false, string{"disjunctive_optional_diff_plain"} + suffix);
        auto optional_form = build(true, string{"disjunctive_optional_diff_opt"} + suffix);
        if (! plain || ! optional_form) {
            println(cerr, "optional-encoding diff: could not read an OPB back");
            return false;
        }
        if (plain->size() != optional_form->size()) {
            report_opb_difference("optional-encoding diff (line count)", *plain, *optional_form);
            return false;
        }

        int clauses_grown = 0;
        for (size_t i = 0; i < plain->size(); ++i) {
            const auto &a = (*plain)[i], &b = (*optional_form)[i];
            if (a == b)
                continue;
            // The only permitted difference: the plain clause, with presence
            // literals inserted before its `>= 1 ;` tail. Anything else --- a
            // changed coefficient, a changed degree, a new row --- is the
            // encoding drifting rather than being extended.
            auto tail = a.find(">=");
            if (tail == string::npos || ! b.starts_with(a.substr(0, tail)) || ! b.ends_with(a.substr(tail))) {
                report_opb_difference("optional-encoding diff", *plain, *optional_form);
                return false;
            }
            // Two tasks per clause, so two added terms, each a negated presence
            // atom at coefficient 1: "1 ~i[_4][b0] 1 ~i[_5][b0]". Nothing may be
            // scaled, and nothing positive may appear --- a presence entering
            // any other way would be a different encoding.
            auto added = b.substr(tail, b.size() - a.size());
            vector<string> tokens;
            for (size_t at = added.find_first_not_of(' '); at != string::npos; at = added.find_first_not_of(' ', at)) {
                auto end = added.find(' ', at);
                tokens.push_back(added.substr(at, end == string::npos ? string::npos : end - at));
                at = end;
            }
            bool literals_ok = tokens.size() == 4;
            for (size_t t = 0; literals_ok && t + 1 < tokens.size(); t += 2)
                literals_ok = tokens[t] == "1" && tokens[t + 1].starts_with("~");
            if (! literals_ok) {
                println(cerr, "optional-encoding diff: line {} gained {:?}, which is not a pair of unit negated presence literals", i + 1, added);
                return false;
            }
            ++clauses_grown;
        }

        // Three tasks, so three pairs, so three separation clauses --- and if
        // the diff were empty the check above would pass vacuously.
        if (clauses_grown != 3) {
            println(cerr, "optional-encoding diff: {} clauses grew, expected 3", clauses_grown);
            return false;
        }
        println(cerr, "optional-encoding diff{}: {} separation clauses grew, everything else is identical", suffix, clauses_grown);
        return true;
    }
}

namespace
{
    // Semantic drift detector. Model the same instance two ways --- presence
    // Booleans, and durations channelled to {0, d} under the non-strict
    // reading, where a zero-duration task places no constraint on anything ---
    // and require the same solution set under the bijection
    // present_i = 1 <-> d_i = d. This pins "absent occupies no time" against a
    // formulation that shares none of the optional-task code path.
    auto check_bijection(const string & tag, const vector<TaskSpec> & tasks) -> bool
    {
        set<vector<int>> via_presence, via_duration;

        {
            Problem p;
            vector<IntegerVariableID> starts, lengths_v, presences, all_vars;
            for (const auto & t : tasks)
                starts.push_back(p.create_integer_variable(Integer{t.start_range.first}, Integer{t.start_range.second}));
            for (const auto & t : tasks) {
                lengths_v.push_back(constant_variable(Integer{t.length.first}));
                presences.push_back(p.create_integer_variable(0_i, 1_i));
            }
            p.post(Disjunctive{starts, lengths_v, presences}.with_strict(false));
            all_vars = starts;
            all_vars.insert(all_vars.end(), presences.begin(), presences.end());
            solve_for_tests(p, nullopt, via_presence, tuple{all_vars});
        }

        {
            Problem p;
            vector<IntegerVariableID> starts, lengths_v, presences, all_vars;
            for (const auto & t : tasks)
                starts.push_back(p.create_integer_variable(Integer{t.start_range.first}, Integer{t.start_range.second}));
            for (const auto & t : tasks) {
                // d_i in {0, d}, channelled to the presence Boolean. A duration
                // of 0 makes both branches the same variable, which is the
                // honest encoding of "this task occupies nothing either way".
                auto d = p.create_integer_variable(0_i, Integer{t.length.first});
                auto present = p.create_integer_variable(0_i, 1_i);
                p.post(LinearEquality{WeightedSum{} + 1_i * d + -Integer{t.length.first} * present, 0_i});
                lengths_v.push_back(d);
                presences.push_back(present);
            }
            p.post(Disjunctive{starts, lengths_v}.with_strict(false));
            all_vars = starts;
            all_vars.insert(all_vars.end(), presences.begin(), presences.end());
            solve_for_tests(p, nullopt, via_duration, tuple{all_vars});
        }

        if (via_presence != via_duration) {
            println(
                cerr, "bijection {}: presence model has {} solutions, variable-duration model has {}", tag, via_presence.size(), via_duration.size());
            for (const auto & sol : via_presence)
                if (! via_duration.contains(sol))
                    println(cerr, "  only in the presence model: {}", sol);
            for (const auto & sol : via_duration)
                if (! via_presence.contains(sol))
                    println(cerr, "  only in the variable-duration model: {}", sol);
            return false;
        }
        println(cerr, "bijection {}: {} solutions agree", tag, via_presence.size());
        return true;
    }

    // The routing this constraint replaces. `fzn_disjunctive_opt` used to
    // decompose to `fzn_cumulative_opt` at unit demands and capacity one, so the
    // non-strict optional Disjunctive must agree with that Cumulative exactly.
    // Not a redundant cross-check: it is the evidence that switching the mznlib
    // redefinition over changes nothing but the encoding and the proof.
    auto check_matches_optional_cumulative(const string & tag, const vector<TaskSpec> & tasks) -> bool
    {
        set<vector<int>> via_disjunctive, via_cumulative;

        auto build = [&](bool as_cumulative, set<vector<int>> & into) {
            Problem p;
            vector<IntegerVariableID> starts, lengths_v, presences, all_vars;
            for (const auto & t : tasks)
                starts.push_back(p.create_integer_variable(Integer{t.start_range.first}, Integer{t.start_range.second}));
            for (const auto & t : tasks) {
                lengths_v.push_back(constant_variable(Integer{t.length.first}));
                presences.push_back(p.create_integer_variable(Integer{t.presence.first}, Integer{t.presence.second}));
            }
            if (as_cumulative) {
                vector<IntegerVariableID> heights(tasks.size(), constant_variable(1_i));
                p.post(Cumulative{starts, lengths_v, heights, presences, constant_variable(1_i)});
            }
            else
                p.post(Disjunctive{starts, lengths_v, presences}.with_strict(false));
            all_vars = starts;
            all_vars.insert(all_vars.end(), presences.begin(), presences.end());
            solve_for_tests(p, nullopt, into, tuple{all_vars});
        };

        build(false, via_disjunctive);
        build(true, via_cumulative);

        if (via_disjunctive != via_cumulative) {
            println(cerr, "vs cumulative {}: disjunctive has {} solutions, cumulative has {}", tag, via_disjunctive.size(), via_cumulative.size());
            for (const auto & sol : via_disjunctive)
                if (! via_cumulative.contains(sol))
                    println(cerr, "  only in the disjunctive model: {}", sol);
            for (const auto & sol : via_cumulative)
                if (! via_disjunctive.contains(sol))
                    println(cerr, "  only in the cumulative model: {}", sol);
            return false;
        }
        println(cerr, "vs cumulative {}: {} solutions agree", tag, via_disjunctive.size());
        return true;
    }
}

namespace
{
    // The motivating use case: maximise the number of scheduled tasks, with the
    // optimum proved. This is also the only test that puts a presence variable
    // in the objective, so it is what exercises presence literals on the
    // objective's proof path.
    auto check_objective(const string & tag, const vector<TaskSpec> & tasks, int expected_optimum) -> bool
    {
        Problem p;
        vector<IntegerVariableID> starts, lengths_v, presences;
        for (const auto & t : tasks)
            starts.push_back(p.create_integer_variable(Integer{t.start_range.first}, Integer{t.start_range.second}));
        for (const auto & t : tasks) {
            lengths_v.push_back(constant_variable(Integer{t.length.first}));
            presences.push_back(p.create_integer_variable(0_i, 1_i));
        }
        p.post(Disjunctive{starts, lengths_v, presences});

        auto scheduled = p.create_integer_variable(0_i, Integer(static_cast<long long>(tasks.size())), "scheduled");
        WeightedSum count;
        for (const auto & v : presences)
            count += 1_i * v;
        p.post(LinearEquality{count + -1_i * scheduled, 0_i});
        p.maximise(scheduled);

        auto proof_name = "disjunctive_optional_objective_" + tag;
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
        auto s2 = p.create_integer_variable(0_i, 3_i, "s2");
        auto present = p.create_integer_variable(Integer{presence_domain.first}, Integer{presence_domain.second}, "present");
        p.post(Disjunctive{vector<IntegerVariableID>{s, s2}, vector<IntegerVariableID>{constant_variable(2_i), constant_variable(2_i)},
            vector<IntegerVariableID>{present, constant_variable(1_i)}});
        try {
            solve(p, [](const CurrentState &) { return true; });
        }
        catch (const InvalidProblemDefinitionException &) {
            return true;
        }
        println(cerr, "{}: expected InvalidProblemDefinitionException", label);
        return false;
    }

    auto expect_constant_presence_out_of_range_throws() -> bool
    {
        Problem p;
        auto s = p.create_integer_variable(0_i, 3_i, "s");
        auto s2 = p.create_integer_variable(0_i, 3_i, "s2");
        try {
            p.post(Disjunctive{vector<IntegerVariableID>{s, s2}, vector<IntegerVariableID>{constant_variable(2_i), constant_variable(2_i)},
                vector<IntegerVariableID>{constant_variable(2_i), constant_variable(1_i)}});
        }
        catch (const InvalidProblemDefinitionException &) {
            return true;
        }
        println(cerr, "constant presence 2: expected InvalidProblemDefinitionException");
        return false;
    }

    auto expect_mismatched_sizes_throws() -> bool
    {
        Problem p;
        auto s = p.create_integer_variable(0_i, 3_i, "s");
        try {
            p.post(Disjunctive{vector<IntegerVariableID>{s}, vector<IntegerVariableID>{constant_variable(2_i)}, vector<IntegerVariableID>{}});
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
    // The sharp-margin falsification family. Unit-length blockers at fixed
    // starts, one time point apart, leave no two consecutive free times
    // anywhere in the optional task's reach --- so it can go nowhere, while
    // dropping any single blocker opens a gap it fits in. Task 0 is the
    // optional one under test; the rest are present and start-fixed. Capacity
    // is one here, so the blockers have to be pairwise disjoint themselves,
    // which is what makes "saturated" mean "alternating" rather than "stacked".
    //
    // `last_blocker` is where the wall stops: at 7 the whole domain is covered
    // and the chain runs four steps (blocked times 1, 3, 5 and 7); at 5 the tail
    // has room for exactly one placement, start 6, which is the twin the
    // one-too-far mutation needs.
    [[nodiscard]] auto sharp_margin_tasks(int last_blocker) -> vector<TaskSpec>
    {
        vector<TaskSpec> tasks{TaskSpec{{0, 6}, {2, 2}, {0, 1}}}; // the optional task under test
        for (int t = 1; t <= last_blocker; t += 2)
            tasks.push_back(TaskSpec{{t, t}, {1, 1}, {1, 1}});
        return tasks;
    }
}

auto main(int argc, char * argv[]) -> int
{
    establish_and_announce_seed(argc, argv);

    // Mutation lanes come in through run_test_and_expect_verify_failure.bash,
    // which prepends its own flags, so the mutation is selected by scanning
    // argv rather than from the positional mode. The harness runs veripb and
    // passes only if it rejects what we write here; all this binary has to do
    // is write the corrupted proof and exit successfully.
    optional<DisjunctivePresenceMutation> mutation;
    vector<TaskSpec> mutation_tasks;
    string proof_basename = "disjunctive_optional_mutation";
    for (int a = 1; a < argc; ++a) {
        string arg = argv[a];
        // The deposits argue about a different optional task than the one being
        // falsified, so nothing the chain establishes is about the conclusion.
        // Needs a second optional task to point at.
        if (arg == "--mutate=wrong_task") {
            mutation = disjunctive_presence_mutation::WrongTask{};
            mutation_tasks = sharp_margin_tasks(7);
            mutation_tasks.push_back(TaskSpec{{0, 6}, {2, 2}, {0, 1}});
        }
        // The control: no chain at all. If this lane ever starts verifying, the
        // chain is decoration and the other mutations are checking nothing.
        else if (arg == "--mutate=emit_nothing") {
            mutation = disjunctive_presence_mutation::EmitNothing{};
            mutation_tasks = sharp_margin_tasks(7);
        }
        // Sharp margin: on the twin where exactly one placement still fits,
        // falsifying anyway is a wrong inference, and the chain runs out of
        // blockers before it can pretend otherwise.
        else if (arg == "--mutate=one_too_far") {
            mutation = disjunctive_presence_mutation::ClaimOneTooFar{};
            mutation_tasks = sharp_margin_tasks(5);
        }
        else if (arg == "--proof-files-basename" && a + 1 < argc)
            proof_basename = argv[++a];
    }

    if (mutation) {
        write_mutated_proof(mutation_tasks, *mutation, proof_basename);
        return EXIT_SUCCESS;
    }

    string mode = argc >= 2 ? argv[1] : "enumerate";
    bool ok = true;

    if (mode == "enumerate") {
        // Rejections first: a presence outside {0, 1} and a mismatched array
        // are modelling errors, not silently-reinterpreted input.
        ok &= expect_bad_presence_throws("presence 0..2", {0, 2});
        ok &= expect_bad_presence_throws("presence -1..1", {-1, 1});
        ok &= expect_constant_presence_out_of_range_throws();
        ok &= expect_mismatched_sizes_throws();
        if (! ok)
            return EXIT_FAILURE;

        for (bool strict : {true, false}) {
            ok &= check_constant_presence_encoding_is_unchanged(strict);
            ok &= check_optional_costs_only_the_clause_literals(strict);
        }
        if (! ok)
            return EXIT_FAILURE;

        vector<pair<string, vector<TaskSpec>>> data{
            // Two optional tasks that cannot both be scheduled where they are,
            // but either or both may simply be absent.
            {"pair", {{{0, 3}, {2, 2}, {0, 1}}, {{0, 3}, {2, 2}, {0, 1}}}},
            // Room for both, so presence never matters.
            {"roomy", {{{0, 7}, {2, 2}, {0, 1}}, {{0, 7}, {2, 2}, {0, 1}}}},
            // One mandatory task and one optional one it can block.
            {"one_mandatory", {{{0, 2}, {3, 3}, {1, 1}}, {{0, 2}, {2, 2}, {0, 1}}}},
            // A constantly-absent task: it must drop out entirely, so its start
            // is free and it overlaps whatever it likes.
            {"const_absent", {{{0, 2}, {3, 3}, {0, 0}}, {{0, 2}, {3, 3}, {1, 1}}}},
            // A zero-length task: under the strict reading it may not sit inside
            // another, unless it is absent, which is the case Cumulative cannot
            // express and this constraint exists to certify.
            {"zero_length", {{{0, 3}, {0, 0}, {0, 1}}, {{0, 3}, {2, 2}, {1, 1}}}},
            // Two zero-length optional tasks and one real one.
            {"two_zero", {{{0, 2}, {0, 0}, {0, 1}}, {{0, 2}, {0, 0}, {0, 1}}, {{0, 2}, {2, 2}, {1, 1}}}},
            // A variable duration on an optional task: the zero-length escape
            // and the presence disjunct are on the same clause.
            {"var_length", {{{0, 3}, {0, 2}, {0, 1}}, {{0, 3}, {2, 2}, {1, 1}}}},
            // Both variable-duration and both optional.
            {"var_both", {{{0, 3}, {1, 2}, {0, 1}}, {{0, 3}, {0, 2}, {0, 1}}}},
            // A task that cannot fit even alone once the fixed one is placed:
            // its presence is false at the root, with no search needed.
            {"never_fits", {{{1, 1}, {2, 2}, {0, 1}}, {{1, 1}, {2, 2}, {1, 1}}}},
            // Three optional tasks over a tight horizon.
            {"three_tight", {{{0, 2}, {2, 2}, {0, 1}}, {{0, 2}, {1, 1}, {0, 1}}, {{0, 2}, {1, 1}, {0, 1}}}},
            // Negative starts.
            {"neg_start", {{{-2, 1}, {2, 2}, {0, 1}}, {{-2, 1}, {2, 2}, {0, 1}}}},
            // A fixed start on an optional task: nothing to push, but its
            // presence can still be decided.
            {"fixed_start", {{{1, 1}, {2, 2}, {0, 1}}, {{0, 2}, {2, 2}, {1, 1}}}},
            // Mixed constants: one always present, one always absent, one free.
            {"mixed_consts", {{{0, 2}, {2, 2}, {1, 1}}, {{0, 2}, {2, 2}, {0, 0}}, {{0, 2}, {2, 2}, {0, 1}}}},
        };

        mt19937 rand(*get_seed());
        // Random instances for breadth, all tasks optional so the presence
        // cross-product is exercised everywhere. Kept small: enumeration is over
        // starts times durations times presences, so the space grows fast.
        for (int k = 0; k < 20; ++k) {
            uniform_int_distribution<> n_dist(2, 3), lo_dist(0, 3), span_dist(0, 3), len_dist(0, 3), pres_dist(0, 3), var_len_dist(0, 3);
            vector<TaskSpec> tasks;
            auto n = n_dist(rand);
            for (int i = 0; i < n; ++i) {
                auto lo = lo_dist(rand);
                auto len = len_dist(rand);
                auto p = pres_dist(rand);
                // One in four durations is a variable, spanning down to zero.
                auto length = var_len_dist(rand) == 0 ? pair{0, len} : pair{len, len};
                tasks.push_back(TaskSpec{{lo, min(lo + span_dist(rand), 3)}, length, p == 0 ? pair{1, 1} : (p == 1 ? pair{0, 0} : pair{0, 1})});
            }
            data.emplace_back("random" + std::to_string(k), tasks);
        }

        for (bool proofs : {false, true}) {
            if (proofs && ! can_run_veripb())
                continue;
            for (bool strict : {true, false})
                for (const auto & [tag, tasks] : data)
                    run_optional_test(proofs, tag + (strict ? "_strict" : "_nonstrict"), tasks, strict);
        }
    }
    else if (mode == "falsify") {
        if (! can_run_veripb()) {
            println(cerr, "veripb not available, skipping falsification tests");
            return EXIT_SUCCESS;
        }

        // Sharp margin: the blockers leave no two consecutive free times in the
        // optional task's reach, so it can go nowhere, the rule fires at the
        // root, and its presence is false in every solution.
        ok &= run_falsification_test(
            "sharp", sharp_margin_tasks(7), FalsificationExpectation{.markers = MarkerCount::AtLeastOne, .present_ones = 0, .falsified_task = 0});

        // Twin, one blocker short: the tail of the horizon has room for exactly
        // one placement, start 6. That one surviving solution is what says the
        // rule did not fire at the root. It legitimately *does* fire below the
        // root, once branching has ruled that start out, so the marker count
        // here is a function of the search seed and is not asserted on.
        ok &= run_falsification_test("twin_window", sharp_margin_tasks(5),
            FalsificationExpectation{.markers = MarkerCount::Unconstrained, .present_ones = 1, .falsified_task = 0});

        // The twin that carries the marker-count-zero assertion: the optional
        // task's whole domain sits in free space, so nothing blocks it at the
        // root or below it, whatever the search does.
        ok &= run_falsification_test("twin_free", {{{0, 1}, {2, 2}, {0, 1}}, {{4, 4}, {1, 1}, {1, 1}}, {{6, 6}, {1, 1}, {1, 1}}},
            FalsificationExpectation{.markers = MarkerCount::Never, .present_ones = 2, .falsified_task = 0});

        // A second optional task, so the wrong-task mutation has somewhere
        // wrong to point. Both are falsified.
        auto two_optional = sharp_margin_tasks(7);
        two_optional.push_back(TaskSpec{{0, 6}, {2, 2}, {0, 1}});
        ok &= run_falsification_test(
            "two_optional", two_optional, FalsificationExpectation{.markers = MarkerCount::AtLeastOne, .present_ones = 0, .falsified_task = 0});

        if (! ok)
            return EXIT_FAILURE;
    }
    else if (mode == "bijection") {
        ok &= check_bijection("pair", {{{0, 3}, {2, 2}, {0, 1}}, {{0, 3}, {2, 2}, {0, 1}}});
        ok &= check_bijection("three", {{{0, 3}, {2, 2}, {0, 1}}, {{0, 3}, {1, 1}, {0, 1}}, {{0, 3}, {2, 2}, {0, 1}}});
        ok &= check_bijection("zero_edge", {{{0, 2}, {0, 0}, {0, 1}}, {{0, 2}, {2, 2}, {0, 1}}});
        ok &= check_bijection("neg_start", {{{-2, 1}, {2, 2}, {0, 1}}, {{-2, 1}, {2, 2}, {0, 1}}});
        if (! ok)
            return EXIT_FAILURE;
    }
    else if (mode == "cumulative") {
        ok &= check_matches_optional_cumulative("pair", {{{0, 3}, {2, 2}, {0, 1}}, {{0, 3}, {2, 2}, {0, 1}}});
        ok &= check_matches_optional_cumulative("three", {{{0, 3}, {2, 2}, {0, 1}}, {{0, 3}, {1, 1}, {0, 1}}, {{0, 3}, {2, 2}, {0, 1}}});
        ok &= check_matches_optional_cumulative("zero_edge", {{{0, 2}, {0, 0}, {0, 1}}, {{0, 2}, {2, 2}, {0, 1}}});
        ok &= check_matches_optional_cumulative("neg_start", {{{-2, 1}, {2, 2}, {0, 1}}, {{-2, 1}, {2, 2}, {0, 1}}});

        mt19937 rand(*get_seed());
        for (int k = 0; k < 25; ++k) {
            uniform_int_distribution<> n_dist(2, 3), lo_dist(-1, 3), span_dist(0, 3), len_dist(0, 3), pres_dist(0, 2);
            vector<TaskSpec> tasks;
            auto n = n_dist(rand);
            for (int i = 0; i < n; ++i) {
                auto lo = lo_dist(rand);
                auto len = len_dist(rand);
                auto pv = pres_dist(rand);
                tasks.push_back(TaskSpec{{lo, min(lo + span_dist(rand), 3)}, {len, len}, pv == 0 ? pair{1, 1} : (pv == 1 ? pair{0, 0} : pair{0, 1})});
            }
            ok &= check_matches_optional_cumulative("random" + std::to_string(k), tasks);
        }
        if (! ok)
            return EXIT_FAILURE;
    }
    else if (mode == "objective") {
        if (! can_run_veripb()) {
            println(cerr, "veripb not available, skipping objective tests");
            return EXIT_SUCCESS;
        }
        // Three tasks of length 2 over t in 0..3: at most two fit end to end,
        // so the optimum is 2.
        ok &= check_objective("pack_two", {{{0, 2}, {2, 2}, {0, 1}}, {{0, 2}, {2, 2}, {0, 1}}, {{0, 2}, {2, 2}, {0, 1}}}, 2);
        // One task is longer than the whole horizon left to it, so the optimum
        // is one short of the count.
        ok &= check_objective("one_too_big", {{{0, 0}, {5, 5}, {0, 1}}, {{0, 2}, {2, 2}, {0, 1}}, {{2, 4}, {2, 2}, {0, 1}}}, 2);
        if (! ok)
            return EXIT_FAILURE;
    }
    else {
        println(cerr, "unknown mode {}", mode);
        return EXIT_FAILURE;
    }

    return ok ? EXIT_SUCCESS : EXIT_FAILURE;
}
