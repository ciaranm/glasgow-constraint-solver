#include <gcs/constraints/comparison.hh>
#include <gcs/constraints/equals.hh>
#include <gcs/constraints/innards/constraints_test_utils.hh>
#include <gcs/constraints/innards/equals_mutations.hh>
#include <gcs/current_state.hh>
#include <gcs/exception.hh>
#include <gcs/problem.hh>
#include <gcs/solve.hh>
#include <gcs/stats.hh>

#include <algorithm>
#include <cstdlib>
#include <fstream>
#include <functional>
#include <iostream>
#include <random>
#include <set>
#include <string>
#include <tuple>
#include <type_traits>
#include <utility>
#include <vector>

using std::cerr;
using std::flush;
using std::function;
using std::is_same_v;
using std::make_optional;
using std::mt19937;
using std::nullopt;
using std::pair;
using std::set;
using std::string;
using std::tuple;
using std::variant;
using std::vector;
using std::ranges::includes;

#if defined(__cpp_lib_print) && defined(__cpp_lib_format)
using std::print;
using std::println;
#else
using fmt::print;
using fmt::println;
#endif

using namespace gcs;
using namespace gcs::test_innards;

template <typename Constraint_>
auto run_equals_test(const string & which, bool proofs, const ViewWrapConfig & view_cfg, variant<int, pair<int, int>> v1_range,
    variant<int, pair<int, int>> v2_range, const function<auto(int, int, int)->bool> & is_satisfying) -> void
{
    auto wraps = wraps_for_positions(view_cfg, 2);
    visit([&](auto v1,
              auto v2) { print(cerr, "equals {} [{}] {} {} {}", which, view_wrap_config_label(view_cfg), v1, v2, proofs ? " with proofs:" : ":"); },
        v1_range, v2_range);
    cerr << flush;

    pair<int, int> v3_range{0, 1};
    set<tuple<int, int, int>> expected, actual;
    build_expected(expected, is_satisfying, v1_range, v2_range, v3_range);
    println(cerr, " expecting {} solutions", expected.size());

    Problem p;
    auto v1 = visit([&](auto b) { return create_integer_variable_or_constant_with_view(p, b, wraps.at(0)); }, v1_range);
    auto v2 = visit([&](auto b) { return create_integer_variable_or_constant_with_view(p, b, wraps.at(1)); }, v2_range);
    auto v3 = p.create_integer_variable(0_i, 1_i);
    if constexpr (is_same_v<Constraint_, Equals>) {
        p.post(Constraint_{v1, v2});
    }
    else if constexpr (is_same_v<Constraint_, NotEquals>) {
        p.post(Constraint_{v1, v2});
    }
    else {
        p.post(Constraint_{v1, v2, v3 == 1_i});
    }

    auto proof_name = proofs ? make_optional("equals_test_" + view_wrap_config_label(view_cfg)) : nullopt;
    solve_for_tests_checking_gac(p, proof_name, expected, actual, tuple{v1, v2, v3});

    check_results(proof_name, expected, actual);
}

// Dup-variable test: post a constraint with the same handle in both
// variable slots. Consistency is intentionally not checked: a GAC
// algorithm for distinct variables doesn't generally yield GAC under
// aliasing, and fixing it varies in difficulty per constraint. We
// verify the solution set and the proof only.
template <typename Constraint_>
auto run_dup_equals_test(const string & filename_tag, bool proofs, pair<int, int> x_range, const function<auto(int, int)->bool> & is_satisfying)
    -> void
{
    print(cerr, "equals dup {} {} {}", filename_tag, x_range, proofs ? " with proofs:" : ":");
    cerr << flush;

    pair<int, int> c_range{0, 1};
    set<tuple<int, int>> expected, actual;
    build_expected(expected, is_satisfying, x_range, c_range);
    println(cerr, " expecting {} solutions", expected.size());

    Problem p;
    auto x = p.create_integer_variable(Integer(x_range.first), Integer(x_range.second));
    auto c = p.create_integer_variable(0_i, 1_i);
    if constexpr (is_same_v<Constraint_, Equals> || is_same_v<Constraint_, NotEquals>) {
        p.post(Constraint_{x, x});
    }
    else {
        p.post(Constraint_{x, x, c == 1_i});
    }

    auto proof_name = proofs ? make_optional("equals_test_dup_" + filename_tag) : nullopt;
    solve_for_tests(p, proof_name, actual, tuple{x, c});

    check_results(proof_name, expected, actual);
}

auto run_no_overlap_equals_test(bool proofs) -> void
{
    print(cerr, "no overlap equals {}", proofs ? " with proofs:" : ":");
    cerr << flush;

    pair<int, int> x_range{1, 10};
    pair<int, int> y_range{1, 10};
    pair<int, int> z_range{0, 1};
    pair<int, int> c_range{0, 1};
    set<tuple<int, int, int, int>> expected, actual;
    build_expected(
        expected,
        [](int x, int y, int z, int c) -> bool {
            if (x == 4 && c != 0)
                return false;
            if (x == 5 && c != 0)
                return false;
            if (x == 6 && c != 0)
                return false;
            if (x == 9 && c != 0)
                return false;
            if (x == 10 && c != 0)
                return false;

            if (y == 1 && c != 0)
                return false;
            if (y == 2 && c != 0)
                return false;
            if (y == 3 && c != 0)
                return false;
            if (y == 6 && c != 0)
                return false;
            if (y == 7 && c != 0)
                return false;
            if (y == 8 && c != 0)
                return false;

            if (z == 1) {
                if (x != y)
                    return false;
            }
            return true;
        },
        x_range, y_range, z_range, c_range);
    println(cerr, " expecting {} solutions", expected.size());

    Problem p;
    auto x = p.create_integer_variable(1_i, 10_i);
    auto y = p.create_integer_variable(1_i, 10_i);
    auto z = p.create_integer_variable(0_i, 1_i);
    auto c = p.create_integer_variable(0_i, 1_i);
    p.post(EqualsIf{x, y, z == 1_i});

    p.post(EqualsIf{c, 0_c, x == 4_i});
    p.post(EqualsIf{c, 0_c, x == 5_i});
    p.post(EqualsIf{c, 0_c, x == 6_i});
    p.post(EqualsIf{c, 0_c, x == 9_i});
    p.post(EqualsIf{c, 0_c, x == 10_i});

    p.post(EqualsIf{c, 0_c, y == 1_i});
    p.post(EqualsIf{c, 0_c, y == 2_i});
    p.post(EqualsIf{c, 0_c, y == 3_i});
    p.post(EqualsIf{c, 0_c, y == 6_i});
    p.post(EqualsIf{c, 0_c, y == 7_i});
    p.post(EqualsIf{c, 0_c, y == 8_i});

    auto proof_name = proofs ? make_optional("equals_test") : nullopt;
    // x, y, z are each GAC (a single EqualsIf is GAC, and c=1 does propagate
    // x != 4 etc. via the contrapositive). But c is only network-GAC: c=1 is
    // unsupported at z=1 because x==y combined with *all* the c -> x not in {...}
    // / c -> y not in {...} implications leaves no common value -- a deduction
    // across all 13 posted constraints that no individual EqualsIf propagator
    // can make (GAC of a conjunction != conjunction of GAC). So c is None.
    solve_for_tests_checking_consistency(p, proof_name, expected, actual,
        tuple{pair{x, CheckConsistency::GAC}, pair{y, CheckConsistency::GAC}, pair{z, CheckConsistency::GAC}, pair{c, CheckConsistency::None}});

    check_results(proof_name, expected, actual);
}

// A reified equals whose operands are disjoint but *interleaved*: each one's
// values sit in the other's holes, so no bound separates them and the witness
// has to account for every run. This is the shape the interval certificate of
// #867 exists for, and the only one in this file that reaches the two moves
// that carry a range literal -- "v1 has nothing in [lo, hi]", which needs no
// lemma, and "v2 has nothing in [lo, hi]", which needs two.
//
// Both orders are run, because the walk is not symmetric: it climbs v1's domain,
// so which operand is first decides whether it starts at v1's lower bound or at
// v2's, and whether it ends by running off the top of v1 or of v2. Between them
// the two orders reach all six moves.
//
// Proofs on, and it is the proof that is the point: the reason is stated over
// intervals, and the conclusion is only RUP if the lemmas emitted alongside it
// let unit propagation see those interval literals through. Verified, so a
// missing lemma is a red lane rather than a silently weaker proof.
auto run_holey_no_overlap_equals_test(bool proofs, bool swapped) -> void
{
    print(cerr, "holey no overlap equals {}{}", swapped ? "swapped" : "plain", proofs ? " with proofs:" : ":");
    cerr << flush;

    // Two blocks each, interleaved: {0..3, 8..11} against {4..7, 12..15}.
    vector<Integer> lower_first, upper_first;
    for (Integer v = 0_i; v <= 15_i; ++v)
        ((v / 4_i) % 2_i == 0_i ? lower_first : upper_first).push_back(v);

    set<tuple<int, int, int>> expected, actual;
    for (const auto & xv : swapped ? upper_first : lower_first)
        for (const auto & yv : swapped ? lower_first : upper_first)
            expected.emplace(static_cast<int>(xv.raw_value), static_cast<int>(yv.raw_value), 0);
    println(cerr, " expecting {} solutions", expected.size());

    Problem p;
    auto x = p.create_integer_variable(swapped ? upper_first : lower_first);
    auto y = p.create_integer_variable(swapped ? lower_first : upper_first);
    auto b = p.create_integer_variable(0_i, 1_i);
    p.post(EqualsIff{x, y, b == 1_i});

    auto proof_name = proofs ? make_optional("equals_test_holey_" + string{swapped ? "swapped" : "plain"}) : nullopt;
    solve_for_tests(p, proof_name, actual, tuple{x, y, b});

    check_results(proof_name, expected, actual);
}

// The same interleaved shape with a *view* as the second operand, which is the
// one instance here whose witness is not spelled entirely in intervals.
//
// A view has no range literal (#882), so a run of values it cannot take is
// spelled out value by value in the reason -- and the second operand is the one
// whose runs cost lemmas. The witness has to recognise those single-value
// literals as one run again, or it pays two lemmas per value instead of two per
// run; the proof still verifies either way, which is why this is checked by
// diffing proof bytes against the interval spelling rather than by a lane going
// red. Measured on this instance: putting the run back together saves nine
// proof lines -- 759 against 768 at --seed=1, 755 against 764 at 424242, 742
// against 751 at 999. The absolute size moves with the seed, since this test
// enumerates under a randomised branching order; the nine lines do not.
//
// It matters more than a handful of lines because it is the only coverage of the
// witness reading a run out of literals it did not write as a range: everything
// else in this file hands it interval literals.
auto run_holey_no_overlap_view_equals_test(bool proofs) -> void
{
    print(cerr, "holey no overlap equals with a view operand{}", proofs ? " with proofs:" : ":");
    cerr << flush;

    // {4..7, 12..15} against a view of {0..3, 8..11}: interleaved, disjoint, and
    // the walk climbs the bare operand, so every run it steps over belongs to
    // the view.
    vector<Integer> lower_first, upper_first;
    for (Integer v = 0_i; v <= 15_i; ++v)
        ((v / 4_i) % 2_i == 0_i ? lower_first : upper_first).push_back(v);

    set<tuple<int, int, int>> expected, actual;
    for (const auto & xv : upper_first)
        for (const auto & yv : lower_first)
            expected.emplace(static_cast<int>(xv.raw_value), static_cast<int>(yv.raw_value), 0);
    println(cerr, " expecting {} solutions", expected.size());

    Problem p;
    auto x = p.create_integer_variable(upper_first);

    // A non-zero offset, deliberately: `v + 0` deviews onto the underlying
    // variable in the proof and gets that variable's range literals, so it would
    // not exercise the per-value spelling at all.
    vector<Integer> shifted;
    for (const auto & v : lower_first)
        shifted.push_back(v - 1_i);
    auto y = p.create_integer_variable(shifted) + 1_i;
    auto b = p.create_integer_variable(0_i, 1_i);
    p.post(EqualsIff{x, y, b == 1_i});

    auto proof_name = proofs ? make_optional("equals_test_holey_view") : nullopt;
    solve_for_tests(p, proof_name, actual, tuple{x, y, b});

    check_results(proof_name, expected, actual);
}

// A reified equals whose operands are wide and do not overlap. Nothing else in
// this file goes anywhere near this shape: every other domain here lives inside
// [-10, 10], and range_infer_test works inside [0, 40], so the no-overlap rule
// had never been asked a question whose answer depends on the width at all.
//
// What this pins is the *answer*: root propagation alone must decide the
// condition, at a width where deciding it by looking at values cannot work.
// Note what it does not pin. It would have passed before #864 was fixed too --
// the unguarded reason walk gave the same answer, having spent 78 GB and 160 s
// to do it, with proofs off. Cost is not checkable from here; the ReifiedEquals
// row of the large-domain audit lane is what holds that down, and it has the
// guard instrumentation to fail rather than merely take a long time.
//
// Proofs off only, and deliberately: at this width the *reason* is the thing
// under test and it is only built when reasons are wanted. The proof side has
// its own test below, at a width whose regression is slow rather than fatal.
//
// Solutions are not enumerated: there are ~2.5e17 of them. Search stops at the
// first node, which is reached only once root propagation has finished.
auto run_wide_no_overlap_equals_test() -> void
{
    const auto width = 1000000000_i;
    println(cerr, "wide no overlap equals: expecting the condition to be false after root propagation");

    Problem p;
    auto x = p.create_integer_variable(0_i, width / 2_i);
    auto y = p.create_integer_variable(width / 2_i + 1_i, width);
    auto b = p.create_integer_variable(0_i, 1_i);
    p.post(EqualsIff{x, y, b == 1_i});

    bool reached_a_node = false, condition_is_false = false;
    auto check = [&](const CurrentState & s) {
        reached_a_node = true;
        condition_is_false = s.has_single_value(b) && s(b) == 0_i;
        return false;
    };

    solve_with(p, SolveCallbacks{.solution = check, .trace = check, .stats_report = silent_stats_report()});

    if (! reached_a_node)
        throw UnexpectedException{"wide no overlap equals test never reached a node"};
    if (! condition_is_false)
        throw UnexpectedException{"wide no overlap equals did not force its condition false at the root"};
}

// The same shape, proved, and this one pins the *cost*: it fails if the witness
// goes back to being one line per value.
//
// Before #867 the rule's justification emitted one RUP line per value in the
// first operand's bounds range, so a proving run at this width wrote a hundred
// megabytes of proof for a fact that two bounds settle -- which is why the test
// above could only be run with proofs off. The interval witness states it in a
// fixed handful of lines at any width, so the assertion is on the proof's line
// count, checked before the proof is handed to veripb.
//
// The bound is loose, and deliberately not a pinned figure. Most of what a proof
// this small contains is fixed overhead -- the header, the initial bound axioms,
// the order-encoding definitions the conclusion's literals pull in -- and that
// part is free to move as unrelated proof scaffolding changes, whereas the thing
// under test is whether the witness is a constant or a million lines. Any
// threshold between the two separates them; pinning the exact figure would only
// buy a lane that goes red for reasons that have nothing to do with this rule.
//
// The width is 10^6 rather than the 10^9 above: a regression must fail, not
// wedge, and at 10^9 a per-value witness would fill the disk before anything
// could notice.
auto run_wide_proved_no_overlap_equals_test() -> void
{
    const auto width = 1000000_i;
    const auto line_budget = 1000;
    println(cerr, "wide no overlap equals with proofs: expecting a proof of well under {} lines", line_budget);

    Problem p;
    auto x = p.create_integer_variable(0_i, width / 2_i);
    auto y = p.create_integer_variable(width / 2_i + 1_i, width);
    auto b = p.create_integer_variable(0_i, 1_i);
    p.post(EqualsIff{x, y, b == 1_i});

    // Solutions are not enumerated: there are ~2.5e11 of them. Stopping at the
    // first node still completes a checkable proof, exactly as
    // check_initialisation_only_for_tests does.
    const string proof_name = "equals_test_wide_proved";
    solve_with(
        p, SolveCallbacks{.trace = [](const CurrentState &) -> bool { return false; }}, make_optional<ProofOptions>(ProofFileNames{proof_name}));

    auto lines = 0;
    {
        std::ifstream proof{proof_name + ".pbp"};
        if (! proof)
            throw UnexpectedException{"wide proved no overlap equals wrote no proof"};
        for (string line; getline(proof, line);)
            ++lines;
    }
    println(cerr, "wide no overlap equals proof is {} lines", lines);
    if (lines > line_budget)
        throw UnexpectedException{"wide proved no overlap equals wrote " + std::to_string(lines) +
            " proof lines, which is not a witness whose size is independent of the domain width"};

    verify_proof_and_clean_up(proof_name);
}

// The family's assertion-hint inventory, read off a real proof.
//
// At AssertionLevel::Inferences the solver emits `a` lines and hints and
// nothing else: the lemmas an explicit derivation writes are absent, and an
// external justifier is expected to rebuild each derivation from the
// annotation, the asserted literal and the reason. So the annotation has to say
// which derivation it was. Until issue #866 the interval bridge -- a conclusion
// that is only RUP once two bound lemmas have carried its endpoints across the
// equality -- arrived under the same `equals:((constraint_id _N))` as the
// family's one-line RUP prunings, and the only way to tell a three-line
// derivation from a one-line one was to notice that the asserted literal was
// spelled as a range. That is keying off literal spelling, which is what the
// hint vocabulary exists to avoid.
//
// Two instances, because no one instance fires all three shapes: a holey
// Equals reaches the bridge and, once search fixes an operand, the
// fixed-operand RUP; a bounds-disjoint reified one reaches the no-overlap walk.
//
// An unrecognised subhint fails as well. The inventory is a closed list that
// the family document quotes rule by rule, so a fourth shape should have to
// come here and be named rather than appearing on the wire unannounced.
namespace
{
    struct EqualsHintsSeen
    {
        bool bare = false;
        set<string> subhints;
        int annotations = 0;
    };

    auto equals_hints_in_proof(const string & proof_name) -> EqualsHintsSeen
    {
        const string annotation = "::equals:(", field = "(subhint ";

        EqualsHintsSeen seen;
        std::ifstream proof{proof_name + ".pbp"};
        if (! proof)
            throw UnexpectedException{"equals hint inventory test wrote no proof for " + proof_name};
        for (string line; getline(proof, line);) {
            auto at = line.find(annotation);
            if (at == string::npos)
                continue;
            ++seen.annotations;
            auto subhint = line.find(field, at);
            if (subhint == string::npos)
                seen.bare = true;
            else {
                auto from = subhint + field.size();
                auto to = line.find(')', from);
                if (to == string::npos)
                    throw UnexpectedException{"unterminated (subhint ...) in " + proof_name + ".pbp: " + line};
                seen.subhints.insert(line.substr(from, to - from));
            }
        }
        return seen;
    }

    auto prove_at_inference_assertion_level(Problem & p, const string & proof_name) -> EqualsHintsSeen
    {
        auto options = ProofOptions{ProofFileNames{proof_name}};
        options.set_assertion_level(AssertionLevel::Inferences);
        solve_with(p, SolveCallbacks{.stats_report = silent_stats_report()}, make_optional(options));

        auto seen = equals_hints_in_proof(proof_name);
        if (0 == seen.annotations)
            throw UnexpectedException{
                "equals hint inventory test found no equals annotations at all in " + proof_name + ".pbp, so it is not testing what it thinks it is"};
        dispose_of_proof_files(proof_name);
        return seen;
    }
}

auto run_hint_inventory_equals_test() -> void
{
    const set<string> inventory{"no_overlap", "not_in_range"};

    // {0..5} against {0,1,4,5}: the symmetric difference is the single run
    // {2,3}, which is a range-literal conclusion and so takes the bridge, and
    // once search fixes the surviving operand the other is forced by a plain
    // RUP. Both operands are bare handles, or the bridge degrades to per-value
    // prunings that really are one-line RUPs (#882).
    println(cerr, "equals hint inventory, interval bridge: expecting a not_in_range subhint and a bare hint");
    {
        Problem p;
        auto x = p.create_integer_variable(0_i, 5_i);
        auto y = p.create_integer_variable(vector<Integer>{0_i, 1_i, 4_i, 5_i});
        p.post(Equals{x, y});

        auto seen = prove_at_inference_assertion_level(p, "equals_test_hints_bridge");
        if (! seen.subhints.contains("not_in_range"))
            throw UnexpectedException{"the equals interval bridge did not annotate its conclusion with the not_in_range subhint, so a justifier "
                                      "cannot tell a three-line derivation from a one-line RUP"};
        if (! seen.bare)
            throw UnexpectedException{"the equals hint inventory instance produced no bare-hint assertion, so it is not showing that the two wire "
                                      "forms are distinguishable"};
        if (! includes(inventory, seen.subhints))
            throw UnexpectedException{"the equals interval bridge instance carried a subhint outside the family's inventory: add it here and to "
                                      "dev_docs/constraints/equals.md"};
    }

    // Bounds-disjoint operands under an iff: the undecided pass forces the
    // condition false, which is the walk.
    println(cerr, "equals hint inventory, no-overlap walk: expecting a no_overlap subhint");
    {
        Problem p;
        auto x = p.create_integer_variable(0_i, 3_i);
        auto y = p.create_integer_variable(5_i, 8_i);
        auto b = p.create_integer_variable(0_i, 1_i);
        p.post(EqualsIff{x, y, b == 1_i});

        auto seen = prove_at_inference_assertion_level(p, "equals_test_hints_no_overlap");
        if (! seen.subhints.contains("no_overlap"))
            throw UnexpectedException{"the equals no-overlap walk did not annotate its verdict with the no_overlap subhint"};
        if (! includes(inventory, seen.subhints))
            throw UnexpectedException{"the equals no-overlap instance carried a subhint outside the family's inventory: add it here and to "
                                      "dev_docs/constraints/equals.md"};
    }
}

// What the constraint *says* it is, and whether it means what it says.
//
// The equals family writes six descriptions, and one of them used to be a
// description of a different constraint: a NotEqualsIff came out as an
// `equals_iff` over a negated condition, because ReifiedEquals::clone() dropped
// the flag that picks the keyword and Problem::post clones (issue #865). That is
// the same constraint said backwards, so it cost nothing -- until half of it
// were repaired, at which point the two negations stop cancelling and the .scp
// says the opposite of what was posted.
//
// So both halves are pinned here, because either alone passes on the bug. The
// keyword and its condition are read out of the .scp, which is what catches a
// flag that stops reaching s_expr(); and the description is read back with
// read_scp and re-solved, which is what catches a keyword and a condition that
// no longer agree with each other. Every other proving test in this file
// exercises the writer, and none of them can see either failure:
// check_scp_writer_reader_symmetry asks only that the reader has a case.
//
// Named variables and bare handles, deliberately: an instance has to be one
// read_scp can rebuild for the semantic half to run at all.
template <typename Constraint_>
auto run_scp_description_equals_test(const string & which, const string & description, const function<auto(int, int, int)->bool> & is_satisfying)
    -> void
{
    println(cerr, "equals scp description {}: expecting ({})", which, description);

    Problem p;
    auto x = p.create_integer_variable(0_i, 3_i, "x");
    auto y = p.create_integer_variable(0_i, 3_i, "y");
    auto b = p.create_integer_variable(0_i, 1_i, "b");
    if constexpr (is_same_v<Constraint_, Equals> || is_same_v<Constraint_, NotEquals>)
        p.post(Constraint_{x, y});
    else
        p.post(Constraint_{x, y, b == 1_i});

    set<vector<int>> expected;
    for (int xv = 0; xv <= 3; ++xv)
        for (int yv = 0; yv <= 3; ++yv)
            for (int bv = 0; bv <= 1; ++bv)
                if (is_satisfying(xv, yv, bv))
                    expected.insert(vector{xv, yv, bv});

    const string proof_name = "equals_test_scp_" + which;
    set<vector<int>> actual;
    solve_for_tests_with_callbacks(
        p, make_optional(proof_name),
        [&](const CurrentState & s) -> bool {
            actual.insert(vector{extract_from_state(s, x), extract_from_state(s, y), extract_from_state(s, b)});
            return true;
        },
        [](const CurrentState &) -> bool { return true; });

    if (actual != expected)
        throw UnexpectedException{"equals scp description test for " + which + " found " + std::to_string(actual.size()) + " solutions, expecting " +
            std::to_string(expected.size())};

    // The label is whatever the constraint id came out as, so match from the
    // space after it; without that leading space "equals x y)" is a substring of
    // "not_equals x y)" and the plain form's pin would pass on the negated one.
    std::ifstream scp{proof_name + ".scp"};
    if (! scp)
        throw UnexpectedException{"equals scp description test for " + which + " wrote no .scp"};
    const string scp_text{std::istreambuf_iterator<char>{scp}, std::istreambuf_iterator<char>{}};
    if (scp_text.find(" " + description + ")") == string::npos) {
        println(cerr, "the .scp for {} does not describe itself as ({}):\n{}", which, description, scp_text);
        throw UnexpectedException{"equals scp description test for " + which + " wrote a description other than (" + description + ")"};
    }

    check_scp_round_trip_solutions(proof_name, {"x", "y", "b"}, expected);
    verify_proof_and_clean_up(proof_name);
}

// Mutation lanes: one deliberately corrupted proof, which
// run_test_and_expect_verify_failure.bash passes only if veripb rejects. See
// EqualsProofMutation for what each corruption is and why it is that one.
//
// Each lane also checks that the run it corrupted made the inference at all --
// the pruning is still made, since these change only the proof -- because a
// mutation lane over a rule that never fired is checking an empty proof and
// passes for the wrong reason. What that check can be differs by rule: for the
// two whose conclusion is a root-propagation fact, it is the fact; for the
// fixed-operand rule, which fires only under a search assignment, it is that
// the enumeration completed, since every solution of x = y over {0..3} is
// reached through a node where one operand is fixed and the other is not.
auto run_mutation_equals_test(const string & which, const string & proof_name) -> void
{
    using namespace gcs::innards::equals_proof_mutation;

    auto root_only = [&](Problem & p, const function<auto(const CurrentState &)->void> & check) {
        solve_with(p,
            SolveCallbacks{
                .trace = [&](const CurrentState & s) -> bool {
                    check(s);
                    return false;
                },                                    //
                .stats_report = silent_stats_report() //
            },
            make_optional<ProofOptions>(ProofFileNames{proof_name}));
    };

    // {0..20} against {0..5} + {14..20}: the symmetric difference is the run
    // {6..13}, so the conclusion is a range literal and takes the two-lemma
    // bridge.
    //
    // The width is not arbitrary, and neither are the endpoints. Omitting the
    // lemmas from a *narrow* interval is not caught: on {0..5} against
    // {0,1,4,5} the conclusion `~[x in 2..3]` is RUP against the equality rows
    // unaided, and so is `~[x in 3..7]` of {0..11}, which is the same thing for
    // a different reason -- an endpoint on a power of two is one bit rather
    // than a sum. Measured across widths 5 to 16 with the hole at the middle
    // third: rejected at every width but 5 and 11. So the lemmas are
    // load-bearing, and a lane that says so has to be asked about an interval
    // whose endpoints are not bit boundaries.
    auto interval_bridge_instance = [&](innards::EqualsProofMutation mutation) {
        vector<Integer> yv;
        for (Integer v = 0_i; v <= 20_i; ++v)
            if (v <= 5_i || v >= 14_i)
                yv.push_back(v);

        Problem p;
        auto x = p.create_integer_variable(0_i, 20_i);
        auto y = p.create_integer_variable(yv);
        p.post(Equals{x, y}.with_proof_mutation(mutation));

        auto fired = false;
        root_only(p, [&](const CurrentState & s) { fired = ! s.in_domain(x, 6_i) && ! s.in_domain(x, 13_i); });
        if (! fired)
            throw UnexpectedException{"mutation lane " + which + ": the interval bridge did not prune, so its proof has nothing in it to corrupt"};
    };

    // Interleaved and disjoint under an iff, so the undecided pass forces the
    // condition false through the walk, over several runs rather than one.
    auto no_overlap_instance = [&](innards::EqualsProofMutation mutation) {
        vector<Integer> lower_first, upper_first;
        for (Integer v = 0_i; v <= 15_i; ++v)
            ((v / 4_i) % 2_i == 0_i ? lower_first : upper_first).push_back(v);

        Problem p;
        auto x = p.create_integer_variable(lower_first);
        auto y = p.create_integer_variable(upper_first);
        auto b = p.create_integer_variable(0_i, 1_i);
        p.post(EqualsIff{x, y, b == 1_i}.with_proof_mutation(mutation));

        auto fired = false;
        root_only(p, [&](const CurrentState & s) { fired = s.has_single_value(b) && s(b) == 0_i; });
        if (! fired)
            throw UnexpectedException{"mutation lane " + which +
                ": the no-overlap rule did not decide the condition, so its proof has nothing in it "
                "to corrupt"};
    };

    // A walk one of whose literals is not already in the proof's database, which
    // is what it takes for dropping a reason literal to be a corruption at all.
    //
    // Every literal of a root-firing walk is one of the operands' bounds or
    // holes. The bounds are OPB axioms, and a fact some other propagator derived
    // at the root is a unit clause the checker has too -- so at the root the
    // reason is a restatement of the database, dropping from it corrupts
    // nothing, and the lane goes green on an empty corruption. (Both were tried:
    // a bare {0..3, 8..11} against {4..7, 12..15}, and the same with x's upper
    // bound pushed by an unconditional LessThanEqual. VeriPB accepts the
    // mutation on each.) A search decision is the exception, because a decision
    // is not written to the database: what is written is the implication from
    // it. So the disjointness has to appear under one.
    //
    // Hence z, whose first decision pushes x's upper bound to 9 and leaves the
    // two operands disjoint but neither of them fixed, which is the shape the
    // walk fires on. Its stop is then `x <= 9`, a fact the reason has to carry
    // because nothing else states it unconditionally. Branching in a fixed order
    // rather than the tests' random one, since the lane needs that decision
    // taken first and taken at all.
    auto decided_bound_no_overlap_instance = [&](innards::EqualsProofMutation mutation) {
        Problem p;
        auto z = p.create_integer_variable(0_i, 1_i);
        auto x = p.create_integer_variable(0_i, 20_i);
        auto y = p.create_integer_variable(10_i, 15_i);
        auto b = p.create_integer_variable(0_i, 1_i);
        p.post(LessThanEqualIf{x, 9_c, z == 1_i});
        p.post(EqualsIff{x, y, b == 1_i}.with_proof_mutation(mutation));

        auto fired = false;
        solve_with(p,
            SolveCallbacks{
                .solution = [&](const CurrentState & s) -> bool { return fired = fired || (s(z) == 1_i && s(b) == 0_i), true; }, //
                .branch = branch_with(variable_order::in_order({z, x, y, b}), value_order::largest_first()),                     //
                .stats_report = silent_stats_report()                                                                            //
            },
            make_optional<ProofOptions>(ProofFileNames{proof_name}));
        if (! fired)
            throw UnexpectedException{
                "mutation lane " + which + ": no solution reached the decision the walk was to fire under, so the proof may not contain it"};
    };

    // The fixed-operand rule only fires under a search assignment, so this one
    // enumerates; every solution of x = y over {0..3} is reached through a node
    // where one operand is fixed and the other is not.
    auto fixed_operand_instance = [&](innards::EqualsProofMutation mutation) {
        Problem p;
        auto x = p.create_integer_variable(0_i, 3_i);
        auto y = p.create_integer_variable(0_i, 3_i);
        p.post(Equals{x, y}.with_proof_mutation(mutation));

        auto solutions = 0;
        solve_with(p,
            SolveCallbacks{
                .solution = [&](const CurrentState &) -> bool { return ++solutions, true; }, //
                .stats_report = silent_stats_report()                                        //
            },
            make_optional<ProofOptions>(ProofFileNames{proof_name}));
        if (4 != solutions)
            throw UnexpectedException{"mutation lane " + which + ": expected 4 solutions, got " + std::to_string(solutions)};
    };

    // The controls. A mutation lane that goes green because its instance's
    // *honest* proof does not verify either is worth nothing, and these four
    // shapes are not otherwise covered: three of them exist to give a rule a
    // margin of one, which is not what the rest of this file is arranged for.
    if (which == "control") {
        if (! can_run_veripb()) {
            println(cerr, "no veripb, so not checking the mutation lanes' honest proofs");
            return;
        }
        // Spelled out rather than looped over: the four have four different
        // closure types, and erasing them into a std::function just to iterate
        // is both gratuitous and something MSVC would not parse.
        fixed_operand_instance(None{});
        verify_proof_and_clean_up(proof_name);
        interval_bridge_instance(None{});
        verify_proof_and_clean_up(proof_name);
        no_overlap_instance(None{});
        verify_proof_and_clean_up(proof_name);
        decided_bound_no_overlap_instance(None{});
        verify_proof_and_clean_up(proof_name);
        println(cerr, "every mutation lane's instance verifies when it is not corrupted");
        return;
    }

    if (which == "fixed_operand_reason")
        fixed_operand_instance(DropFixedOperandReason{});
    else if (which == "bridge_lemmas")
        interval_bridge_instance(OmitBridgeLemmas{});
    else if (which == "no_overlap_stop")
        decided_bound_no_overlap_instance(DropNoOverlapStopLiteral{});
    else if (which == "no_overlap_lemmas")
        no_overlap_instance(OmitNoOverlapLemmas{});
    else if (which == "no_overlap_selector")
        no_overlap_instance(FlipNoOverlapSelector{});
    else
        throw UnexpectedException{"unknown equals mutation lane " + which};

    println(cerr, "wrote a deliberately corrupted proof to {}.pbp", proof_name);
}

auto main(int argc, char * argv[]) -> int
{
    establish_and_announce_seed(argc, argv);

    // A mutation lane runs one instance, writes one knowingly wrong proof, and
    // leaves the verdict to the wrapper script.
    string mutation, proof_basename = "equals_test_mutation";
    for (int a = 1; a < argc; ++a) {
        string arg = argv[a];
        if (arg.starts_with("--mutate="))
            mutation = arg.substr(arg.find('=') + 1);
        else if (arg == "--proof-files-basename" && a + 1 < argc)
            proof_basename = argv[++a];
    }
    if (! mutation.empty()) {
        run_mutation_equals_test(mutation, proof_basename);
        return EXIT_SUCCESS;
    }

    auto view_cfg = parse_view_wrap_config_from_argv(argc, argv);

    // Single-position config that names a position the constraint doesn't
    // have collapses to "all bare", which the baseline (no flags) already
    // covers. Skip with a success exit so ctest sees it as benign.
    constexpr int n_positions = 2;
    if (view_cfg.single_position && (*view_cfg.single_position < 0 || *view_cfg.single_position >= n_positions)) {
        println(cerr, "equals view sweep: position {} out of range for n_positions = {}; skipping", *view_cfg.single_position, n_positions);
        return EXIT_SUCCESS;
    }

    vector<pair<variant<int, pair<int, int>>, variant<int, pair<int, int>>>> data = {
        {pair{2, 5}, pair{1, 6}},     //
        {pair{1, 6}, pair{2, 5}},     //
        {pair{1, 3}, pair{1, 3}},     //
        {pair{1, 5}, pair{6, 8}},     //
        {pair{1, 1}, pair{2, 4}},     //
        {pair{-2, -2}, pair{-2, -1}}, //
        {pair{1, 3}, pair{5, 8}},     //
        {pair{4, 13}, pair{3, 16}},   //
        {pair{-2, 4}, pair{-8, 7}},   //
        {pair{-7, 3}, pair{-10, 5}},  //
        // issue #254: genuine all-constant operands (ConstantIntegerVariableID),
        // both directions. Each Equals/NotEquals (and reified) mode is computed
        // from build_expected: 4==4 holds, 4==5 does not.
        {4, 4},  //
        {4, 5},  //
        {-3, -3} //
    };

    mt19937 rand(*get_seed());
    for (int x = 0; x < 10; ++x)
        generate_random_data(rand, data, random_bounds(-10, 10, 5, 15), random_bounds(-10, 10, 5, 15));
    for (int x = 0; x < 10; ++x)
        generate_random_data(rand, data, random_constant(-10, 10), random_bounds(-10, 10, 5, 15));
    for (int x = 0; x < 10; ++x)
        generate_random_data(rand, data, random_bounds(-10, 10, 5, 15), random_constant(-10, 10));

    // no_overlap_equals_test fixes its own variable construction and isn't
    // currently part of the view sweep, so only run it for the baseline.
    bool run_no_overlap = view_wrap_config_is_effectively_bare(view_cfg, n_positions);

    // Bare-handle dup ranges. Skipped under the view-wrap sweep (which
    // mutates positional view-wraps in ways that aren't aliasing-aware).
    vector<pair<int, int>> dup_data = {
        {0, 0}, {0, 1}, {0, 5}, {-3, 3}, {2, 5} //
    };

    for (bool proofs : {false, true}) {
        if (proofs && ! can_run_veripb())
            continue;
        if (run_no_overlap) {
            run_no_overlap_equals_test(proofs);
            run_holey_no_overlap_equals_test(proofs, false);
            run_holey_no_overlap_equals_test(proofs, true);
            run_holey_no_overlap_view_equals_test(proofs);
            if (proofs)
                run_wide_proved_no_overlap_equals_test();
            else
                run_wide_no_overlap_equals_test();
        }
        // Reads its own proof rather than solving twice, and needs bare handles
        // for the same reason as the descriptions below.
        if (proofs && view_wrap_config_is_effectively_bare(view_cfg, n_positions))
            run_hint_inventory_equals_test();

        // Bare handles under names of our own choosing, so read_scp can rebuild
        // what the writer wrote; proofs on, because the .scp is only written
        // when a proof is.
        if (proofs && view_wrap_config_is_effectively_bare(view_cfg, n_positions)) {
            run_scp_description_equals_test<Equals>("equals", "equals x y", [](int xv, int yv, int) { return xv == yv; });
            run_scp_description_equals_test<EqualsIf>(
                "equals_if", "equals_if (b = 1) x y", [](int xv, int yv, int bv) { return (! bv) || xv == yv; });
            run_scp_description_equals_test<EqualsIff>(
                "equals_iff", "equals_iff (b = 1) x y", [](int xv, int yv, int bv) { return (xv == yv) == (bv == 1); });
            run_scp_description_equals_test<NotEquals>("not_equals", "not_equals x y", [](int xv, int yv, int) { return xv != yv; });
            run_scp_description_equals_test<NotEqualsIf>(
                "not_equals_if", "not_equals_if (b = 1) x y", [](int xv, int yv, int bv) { return (! bv) || xv != yv; });
            run_scp_description_equals_test<NotEqualsIff>(
                "not_equals_iff", "not_equals_iff (b = 1) x y", [](int xv, int yv, int bv) { return (xv != yv) == (bv == 1); });
        }
        for (auto & [r1, r2] : data) {
            run_equals_test<Equals>("equals", proofs, view_cfg, r1, r2, [](int a, int b, int) { return a == b; });
            run_equals_test<EqualsIf>("equals if", proofs, view_cfg, r1, r2, [](int a, int b, int f) { return (! f) || (a == b); });
            run_equals_test<EqualsIff>("equals iff", proofs, view_cfg, r1, r2, [](int a, int b, int f) { return (a == b) == f; });
            run_equals_test<NotEquals>("not equals", proofs, view_cfg, r1, r2, [](int a, int b, int) { return a != b; });
            run_equals_test<NotEqualsIf>("not equals if", proofs, view_cfg, r1, r2, [](int a, int b, int f) { return (! f) || (a != b); });
            run_equals_test<NotEqualsIff>("not equals iff", proofs, view_cfg, r1, r2, [](int a, int b, int f) { return (a != b) == f; });
        }
        if (view_wrap_config_is_effectively_bare(view_cfg, n_positions))
            for (auto & x_range : dup_data) {
                run_dup_equals_test<Equals>("equals", proofs, x_range, [](int, int) { return true; });
                run_dup_equals_test<EqualsIf>("equals_if", proofs, x_range, [](int, int) { return true; });
                run_dup_equals_test<EqualsIff>("equals_iff", proofs, x_range, [](int, int c) { return c == 1; });
                run_dup_equals_test<NotEqualsIff>("notequals_iff", proofs, x_range, [](int, int c) { return c == 0; });
                // NotEqualsIf(x, x, c) ≡ c → x ≠ x ≡ ¬c. Was Bucket B
                // (propagator silent on alias) — fixed by alias check in
                // ReifiedEquals' infer_cond_when_undecided.
                run_dup_equals_test<NotEqualsIf>("notequals_if", proofs, x_range, [](int, int c) { return c == 0; });
            }
    }

    {
        // NotEquals on aliased operands is trivially unsat; reject at
        // construction rather than discovering after search.
        Problem p;
        auto x = p.create_integer_variable(Integer{0}, Integer{3});
        try {
            p.post(NotEquals{x, x});
            cerr << "expected NotEquals(x,x) to throw InvalidProblemDefinitionException" << '\n';
            return EXIT_FAILURE;
        }
        catch (const InvalidProblemDefinitionException &) {
        }
    }

    return EXIT_SUCCESS;
}
