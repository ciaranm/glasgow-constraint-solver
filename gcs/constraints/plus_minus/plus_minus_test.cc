#include <gcs/constraints/equals.hh>
#include <gcs/constraints/innards/constraints_test_utils.hh>
#include <gcs/constraints/innards/plus_minus_mutations.hh>
#include <gcs/constraints/minus.hh>
#include <gcs/constraints/plus.hh>
#include <gcs/constraints/plus_minus/gac.hh>
#include <gcs/current_state.hh>
#include <gcs/exception.hh>
#include <gcs/problem.hh>
#include <gcs/search_heuristics.hh>
#include <gcs/solve.hh>

#include <cstdlib>
#include <functional>
#include <iostream>
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
using std::function;
using std::is_same_v;
using std::make_optional;
using std::mt19937;
using std::nullopt;
using std::optional;
using std::pair;
using std::set;
using std::string;
using std::tuple;
using std::variant;
using std::vector;

#if defined(__cpp_lib_print) && defined(__cpp_lib_format)
using std::print;
using std::println;
#else
using fmt::print;
using fmt::println;
#endif

using namespace gcs;
using namespace gcs::test_innards;

namespace
{
    // The fallback lane runs this binary with GCS_INTERVAL_PAIRS_THRESHOLD set,
    // beside the ordinary lane; tag the proof file names with it so the two runs
    // don't clobber each other's .opb/.pbp under parallel ctest (see #961).
    auto threshold_proof_suffix() -> string
    {
        if (const char * e = std::getenv("GCS_INTERVAL_PAIRS_THRESHOLD"))
            return string{"_p"} + e;
        return {};
    }

    template <typename Arithmetic_>
    struct NameOf;

    template <>
    struct NameOf<Plus>
    {
        static const constexpr auto name = "plus";
    };

    template <>
    struct NameOf<Minus>
    {
        static const constexpr auto name = "minus";
    };
}

// Which consistency level a run_plus_minus_test run asks for.
enum class Arm
{
    Auto,
    GAC,
    Dynamic
};

// Auto is checked for its solutions only. GAC is also checked to leave every
// value in every position with a support, at every node, and so is Dynamic,
// since no domain here has anything like the pairs of intervals it takes to
// make it fall back -- except in the lane that forces the threshold to zero,
// where it is checked for its solutions only.
template <typename Constraint_, typename V1_, typename V2_, typename V3_>
auto run_plus_minus_test(bool proofs, const ViewWrapConfig & view_cfg, Arm arm, V1_ v1_range, V2_ v2_range, V3_ v3_range,
    const function<auto(int, int, int)->bool> & is_satisfying) -> void
{
    string arm_name = arm == Arm::GAC ? "gac" : arm == Arm::Dynamic ? "dynamic" : "";
    auto wraps = wraps_for_positions(view_cfg, 3);
    visit(
        [&](const auto & v1, const auto & v2, const auto & v3) {
            print(cerr, "{} {} [{}] {} {} {} {}", NameOf<Constraint_>::name, arm_name, view_wrap_config_label(view_cfg), v1, v2, v3,
                proofs ? " with proofs:" : ":");
        },
        v1_range, v2_range, v3_range);
    cerr << flush;
    set<tuple<int, int, int>> expected, actual;

    visit([&](const auto & v1, const auto & v2, const auto & v3) { build_expected(expected, is_satisfying, v1, v2, v3); }, v1_range, v2_range,
        v3_range);
    println(cerr, " expecting {} solutions", expected.size());

    Problem p;
    auto v1 = visit([&](const auto & r) { return create_integer_variable_or_constant_with_view(p, r, wraps.at(0)); }, v1_range);
    auto v2 = visit([&](const auto & r) { return create_integer_variable_or_constant_with_view(p, r, wraps.at(1)); }, v2_range);
    auto v3 = visit([&](const auto & r) { return create_integer_variable_or_constant_with_view(p, r, wraps.at(2)); }, v3_range);
    switch (arm) {
    case Arm::Auto: p.post(Constraint_{v1, v2, v3}); break;
    case Arm::GAC: p.post(Constraint_{v1, v2, v3}.with_consistency(consistency::GAC{})); break;
    case Arm::Dynamic: p.post(Constraint_{v1, v2, v3}.with_consistency(consistency::Dynamic{})); break;
    }

    auto proof_name = proofs
        ? make_optional("plus_minus_test_" + (arm_name.empty() ? "" : arm_name + "_") + view_wrap_config_label(view_cfg) + threshold_proof_suffix())
        : nullopt;
    bool gac_expected = arm == Arm::GAC || (arm == Arm::Dynamic && innards::default_interval_pairs_threshold() >= 256);
    auto check = gac_expected ? CheckConsistency::GAC : CheckConsistency::None;
    solve_for_tests_checking_consistency(p, proof_name, expected, actual, tuple{pair{v1, check}, pair{v2, check}, pair{v3, check}});

    check_results(proof_name, expected, actual);
}

// consistency::Dynamic past its threshold: two operands whose pairs of
// intervals (40 x 30) exceed the default, so each step combines one operand
// with the other's hull. y is every hundredth value up to 3900 and z the even
// values up to 58, so x = y + z is exactly the even values in [100i, 100i + 58].
// Combining y with z's hull [0, 58] still removes the gap [100i + 59,
// 100i + 99] above each block, which bounds consistency would not; what it
// cannot see is that the odd values inside a block are missing too, which GAC
// would. The root is checked for both, then the whole thing is enumerated.
//
// Without proofs: checking one takes VeriPB about half a minute here, for
// derivations the fallback lane (plus_minus_constraint_dynamic_fallback, with
// the threshold at zero) already verifies on every other row.
auto run_dynamic_fallback_test() -> void
{
    println(cerr, "plus dynamic fallback");

    auto build = [](Problem & p) {
        vector<Integer> y_values, z_values;
        for (int v = 0; v <= 3900; v += 100)
            y_values.push_back(Integer{v});
        for (int v = 0; v <= 58; v += 2)
            z_values.push_back(Integer{v});
        auto y = p.create_integer_variable(y_values);
        auto z = p.create_integer_variable(z_values);
        auto x = p.create_integer_variable(0_i, 3958_i);
        p.post(Plus{y, z, x}.with_consistency(consistency::Dynamic{}));
        return tuple{y, z, x};
    };

    if (innards::default_interval_pairs_threshold() < 40 * 30) {
        Problem p;
        auto [y, z, x] = build(p);
        auto gap_removed = false, odd_kept = false;
        solve_with(p,
            SolveCallbacks{.trace =
                               [&](const CurrentState & s) {
                                   gap_removed = ! s.in_domain(x, 180_i) && ! s.in_domain(x, 3880_i);
                                   odd_kept = s.in_domain(x, 1_i) && s.in_domain(x, 157_i);
                                   return false;
                               },
                .stats_report = silent_stats_report()});
        if (! gap_removed || ! odd_kept)
            throw UnexpectedException{"Dynamic past its threshold should remove the gaps between blocks and keep the odd values inside them"};
    }

    set<tuple<int, int, int>> actual;
    Problem p;
    auto [y, z, x] = build(p);
    optional<string> proof_name = nullopt;
    solve_for_tests(p, proof_name, actual, tuple{y, z, x});
    set<tuple<int, int, int>> expected;
    for (int yv = 0; yv <= 3900; yv += 100)
        for (int zv = 0; zv <= 58; zv += 2)
            expected.emplace(yv, zv, yv + zv);
    check_results(proof_name, expected, actual);
}

// Dup-variable test: post Plus / Minus with the same handle in two
// (or all three) slots. Consistency is intentionally not checked: a
// GAC algorithm for distinct variables doesn't generally yield GAC
// under aliasing, and fixing it per-constraint is out of scope.
// See tmp/duplicate_var_audit.md.
namespace
{
    struct AliasV1V2
    {
    };
    struct AliasV1V3
    {
    };
    struct AliasV2V3
    {
    };
    struct AliasAll
    {
    };
}

template <typename Constraint_, typename AliasPattern_>
auto run_dup_plus_minus_test(bool proofs, AliasPattern_, const string & tag, bool gac, pair<int, int> a_range, pair<int, int> b_range,
    const function<auto(int, int, int)->bool> & is_satisfying) -> void
{
    print(cerr, "{} dup {}{} {} {} {}", NameOf<Constraint_>::name, tag, gac ? " gac" : "", a_range, b_range, proofs ? " with proofs:" : ":");
    cerr << flush;

    PlusConsistency level = consistency::Auto{};
    if (gac)
        level = consistency::GAC{};

    Problem p;
    auto proof_name =
        proofs ? make_optional(string{NameOf<Constraint_>::name} + "_test_dup_" + (gac ? "gac_" : "") + tag + threshold_proof_suffix()) : nullopt;

    if constexpr (is_same_v<AliasPattern_, AliasAll>) {
        // C{a, a, a} — only `a_range` matters; `b_range` ignored.
        set<tuple<int>> expected, actual;
        build_expected(expected, [&](int a) { return is_satisfying(a, a, a); }, a_range);
        println(cerr, " expecting {} solutions", expected.size());

        auto a = p.create_integer_variable(Integer(a_range.first), Integer(a_range.second));
        p.post(Constraint_{a, a, a}.with_consistency(level));

        solve_for_tests(p, proof_name, actual, tuple{a});
        check_results(proof_name, expected, actual);
    }
    else {
        set<tuple<int, int>> expected, actual;
        if constexpr (is_same_v<AliasPattern_, AliasV1V2>)
            build_expected(expected, [&](int a, int b) { return is_satisfying(a, a, b); }, a_range, b_range);
        else if constexpr (is_same_v<AliasPattern_, AliasV1V3>)
            build_expected(expected, [&](int a, int b) { return is_satisfying(a, b, a); }, a_range, b_range);
        else // AliasV2V3
            build_expected(expected, [&](int a, int b) { return is_satisfying(a, b, b); }, a_range, b_range);
        println(cerr, " expecting {} solutions", expected.size());

        auto a = p.create_integer_variable(Integer(a_range.first), Integer(a_range.second));
        auto b = p.create_integer_variable(Integer(b_range.first), Integer(b_range.second));
        if constexpr (is_same_v<AliasPattern_, AliasV1V2>)
            p.post(Constraint_{a, a, b}.with_consistency(level));
        else if constexpr (is_same_v<AliasPattern_, AliasV1V3>)
            p.post(Constraint_{a, b, a}.with_consistency(level));
        else
            p.post(Constraint_{a, b, b}.with_consistency(level));

        solve_for_tests(p, proof_name, actual, tuple{a, b});
        check_results(proof_name, expected, actual);
    }
}

// The consistency tag: forced Tabulated tabulates and is checked per node, as
// are forced GAC and Dynamic; forced BC never tabulates. Auto is Dynamic here,
// since these positions are distinct, and is checked per node too.
template <typename Constraint_>
auto run_tagged_test(bool proofs, const string & proof_suffix, const PlusConsistency & level, bool check_gac, pair<int, int> v1_range,
    pair<int, int> v2_range, pair<int, int> v3_range, const function<auto(int, int, int)->bool> & is_satisfying) -> void
{
    print(cerr, "{} tagged {} {} {} {} {}", NameOf<Constraint_>::name, check_gac ? "gac-checked" : "plain", v1_range, v2_range, v3_range,
        proofs ? " with proofs:" : ":");
    cerr << flush;
    set<tuple<int, int, int>> expected, actual;
    build_expected(expected, is_satisfying, v1_range, v2_range, v3_range);
    println(cerr, " expecting {} solutions", expected.size());

    Problem p;
    auto v1 = p.create_integer_variable(Integer(v1_range.first), Integer(v1_range.second));
    auto v2 = p.create_integer_variable(Integer(v2_range.first), Integer(v2_range.second));
    auto v3 = p.create_integer_variable(Integer(v3_range.first), Integer(v3_range.second));
    p.post(Constraint_{v1, v2, v3}.with_consistency(level));

    auto proof_name = proofs ? make_optional("plus_minus_test_tagged_" + proof_suffix + threshold_proof_suffix()) : nullopt;
    if (check_gac)
        solve_for_tests_checking_gac(p, proof_name, expected, actual, tuple{v1, v2, v3});
    else
        solve_for_tests(p, proof_name, actual, tuple{v1, v2, v3});
    check_results(proof_name, expected, actual);
}

// Mutation lanes for the consistency::GAC arm (issue #192): one deliberately
// corrupted proof, which run_test_and_expect_verify_failure.bash passes only
// if veripb rejects. See PlusMinusProofMutation for what each corruption is.
//
// One instance serves every lane, and it is shaped by the reason-dropping one.
// a's hole has to arise under a search decision, or the checker has it as a
// fact whatever the reason says, so a starts out whole and only takes w's hole
// through EqualsIf once the first decision sets z. The removal the hole lanes
// corrupt is then result's run [12, 39]: every sum of a in {3..5, 40..42} and
// b in {0..6} misses it, the walk is over b's single interval, and its window
// [6, 39] is exactly a's hole, so the proof takes both hole lemmas and names
// the hole in its reason. Neither endpoint is on a bit boundary, which is
// what lets unit propagation cross an equality unaided (equals_mutations.hh).
//
// The lane that omits every lemma is rejected earlier than that, at the root
// removal of result's [49, 60], whose windows lie past a's bounds and which
// has no hole in it at all. So it shows that the bounds-shaped lemmas are
// load-bearing too, and not only the ones for holes.
//
// Each lane also checks that the run made the inference it corrupts, since a
// lane over a pruning that never happened is checking an empty proof.
auto run_mutation_plus_test(const string & which, const string & proof_name) -> void
{
    using namespace gcs::innards::plus_minus_proof_mutation;

    auto instance = [&](innards::PlusMinusProofMutation mutation) {
        vector<Integer> w_values;
        for (auto v : {3, 4, 5, 40, 41, 42})
            w_values.push_back(Integer{v});

        Problem p;
        auto z = p.create_integer_variable(0_i, 1_i);
        auto w = p.create_integer_variable(w_values);
        auto a = p.create_integer_variable(3_i, 42_i);
        auto b = p.create_integer_variable(0_i, 6_i);
        auto result = p.create_integer_variable(0_i, 60_i);
        p.post(EqualsIf{a, w, z == 1_i});
        p.post(Plus{a, b, result}.with_consistency(consistency::GAC{}).with_proof_mutation(mutation));

        auto fired = false, whole_at_root = false;
        solve_with(p,
            SolveCallbacks{.solution = [&](const CurrentState &) -> bool { return true; },
                .trace = [&](const CurrentState & s) -> bool {
                    if (! s.has_single_value(z))
                        whole_at_root = whole_at_root || s.in_domain(result, 20_i);
                    else if (s(z) == 1_i && s.in_domain(result, 11_i) && ! s.in_domain(result, 20_i) && s.in_domain(result, 40_i))
                        fired = true;
                    return true;
                },
                .branch = branch_with(variable_order::in_order({z, a, b, result, w}), value_order::largest_first()),
                .stats_report = silent_stats_report()},
            make_optional<ProofOptions>(ProofFileNames{proof_name}));
        if (! whole_at_root || ! fired)
            throw UnexpectedException{
                "mutation lane " + which + ": result's run [12, 39] was not removed under the decision, so its proof has nothing to corrupt"};
    };

    // The control: a lane that goes green because its instance's honest proof
    // does not verify either is worth nothing.
    if (which == "control") {
        if (! can_run_veripb()) {
            println(cerr, "no veripb, so not checking the mutation lanes' honest proof");
            return;
        }
        instance(None{});
        verify_proof_and_clean_up(proof_name);
        println(cerr, "the mutation lanes' instance verifies when it is not corrupted");
        return;
    }

    if (which == "lemmas")
        instance(OmitLemmas{});
    else if (which == "hole_lemmas")
        instance(OmitHoleLemmas{});
    else if (which == "window_holes")
        instance(DropWindowHoles{});
    else
        throw UnexpectedException{"unknown plus mutation lane " + which};

    println(cerr, "wrote a deliberately corrupted proof to {}.pbp", proof_name);
}

auto main(int argc, char * argv[]) -> int
{
    establish_and_announce_seed(argc, argv);

    // A mutation lane runs one instance, writes one knowingly wrong proof, and
    // leaves the verdict to the wrapper script.
    string mutation, proof_basename = "plus_minus_test_mutation";
    for (int a = 1; a < argc; ++a) {
        string arg = argv[a];
        if (arg.starts_with("--mutate="))
            mutation = arg.substr(arg.find('=') + 1);
        else if (arg == "--proof-files-basename" && a + 1 < argc)
            proof_basename = argv[++a];
    }
    if (! mutation.empty()) {
        run_mutation_plus_test(mutation, proof_basename);
        return EXIT_SUCCESS;
    }

    auto view_cfg = parse_view_wrap_config_from_argv(argc, argv);

    constexpr int n_positions = 3;
    if (view_cfg.single_position && (*view_cfg.single_position < 0 || *view_cfg.single_position >= n_positions)) {
        println(cerr, "plus_minus view sweep: position {} out of range for n_positions = {}; skipping", *view_cfg.single_position, n_positions);
        return EXIT_SUCCESS;
    }

    using V12 = variant<int, pair<int, int>, vector<int>>;
    using V3 = variant<int, pair<int, int>>;
    vector<tuple<V12, V12, V3>> data = {
        {pair{2, 5}, pair{1, 6}, pair{1, 12}},                                  //
        {pair{1, 6}, pair{2, 5}, pair{5, 8}},                                   //
        {pair{1, 3}, pair{1, 3}, pair{0, 10}},                                  //
        {pair{1, 3}, pair{1, 3}, pair{1, 3}},                                   //
        {pair{1, 5}, pair{6, 8}, pair{-10, 10}},                                //
        {pair{1, 1}, pair{2, 4}, pair{-5, 5}},                                  //
        {pair{10, 15}, pair{60, 80}, pair{-100, 100}},                          //
        {pair{-10, 0}, pair{-4, 2}, pair{4, 9}},                                //
        {pair{1, 100}, pair{1, 3}, pair{1, 100}},                               //
        {pair{1, 10}, pair{1, 3}, pair{1, 10}},                                 //
        {pair{1, 10}, pair{1, 10}, pair{1, 20}},                                //
        {vector{1, 5, 10}, vector{1, 5, 10}, pair{1, 20}},                      //
        {vector{1, 2, 3, 5, 6, 10}, vector{1, 2, 3, 5, 8, 9, 10}, pair{1, 20}}, //
        // Constant-result regression: x + y == 6 over [1,5] × [1,5].
        {pair{1, 5}, pair{1, 5}, 6}, //
        // Constant-operand: x + 2 == z over [1,5] × [3,8].
        {pair{1, 5}, 2, pair{3, 8}}, //
        // issue #254: fully all-constant operands (ConstantIntegerVariableID).
        // Each row runs for both Plus and Minus; build_expected gives the
        // per-operation truth, e.g. {2,3,5}: 2+3==5 (Plus SAT) but 2-3!=5
        // (Minus UNSAT); {4,1,3}: 4+1!=3 (Plus UNSAT) but 4-1==3 (Minus SAT).
        {2, 3, 5}, //
        {4, 1, 3}, //
        {0, 0, 0}  //
    };

    // The random sweep mixes constants and bounds-pairs across all three slots
    // via random_bounds_or_constant. v1/v2's variant is wider than the helper's
    // return type (because hand-rolled cases include hole-y vector<int> domains
    // that the random sweep doesn't produce), so visit-widen at insertion.
    auto widen_v12 = [](variant<int, pair<int, int>> v) -> V12 { return visit([](auto x) -> V12 { return x; }, v); };
    mt19937 rand(*get_seed());
    for (int x = 0; x < 10; ++x) {
        auto r1 = generate_random_data_item(rand, random_bounds_or_constant(-10, 10, 5, 15));
        auto r2 = generate_random_data_item(rand, random_bounds_or_constant(-10, 10, 5, 15));
        auto r3 = generate_random_data_item(rand, random_bounds_or_constant(-10, 10, 5, 15));
        data.emplace_back(widen_v12(r1), widen_v12(r2), r3);
    }

    // Bare-handle dup ranges. Skipped under the view-wrap sweep.
    vector<pair<pair<int, int>, pair<int, int>>> dup_data = {
        {{0, 5}, {0, 10}},  //
        {{-3, 3}, {-6, 6}}, //
        {{1, 4}, {-5, 5}},  //
        {{0, 0}, {0, 5}}    //
    };

    // The consistency::GAC arm (issue #192) runs over every row above, then
    // over shapes that put holes where they matter to it: the values between
    // the bounds are its whole point, and its proof walks one operand a whole
    // interval at a time, stepping over the other's holes, so it wants holes
    // in every position, windows landing inside holes rather than past the
    // bounds, and runs of one value as well as wider ones.
    using V123 = variant<int, pair<int, int>, vector<int>>;
    auto widen_v3 = [](V3 v) -> V123 { return visit([](auto x) -> V123 { return x; }, v); };
    vector<tuple<V12, V12, V123>> gac_data;
    for (auto & [r1, r2, r3] : data)
        gac_data.emplace_back(r1, r2, widen_v3(r3));
    vector<tuple<V12, V12, V123>> holey_data = {
        // The issue's opening example: a gap in a leaves a gap in the result.
        {vector{1, 2, 3, 10, 11, 12}, pair{0, 2}, pair{0, 20}},                      //
        {vector{1, 2, 3, 4, 5, 6, 20, 21, 22, 23, 24, 25}, pair{0, 4}, pair{0, 40}}, //
        // Four runs removed from the result, each window inside a hole of a.
        {vector{0, 5, 10, 15}, vector{0, 1, 2}, pair{0, 20}}, //
        // Holes everywhere, the result's own among them.
        {vector{0, 5, 10, 15}, vector{0, 1, 2, 20, 21}, vector{3, 4, 8, 9, 13, 14, 21, 22, 40, 41}}, //
        // Both operands several intervals wide, so a walk crosses several holes.
        {vector{0, 1, 10, 11, 20, 21}, vector{0, 1, 5, 6}, pair{0, 30}}, //
        {vector{-8, -7, -2, -1}, vector{-3, 3}, pair{-12, 5}},           //
        // Pruning an operand, where the walk is over the result or the other operand.
        {pair{-10, 15}, vector{0, 1, 5, 6}, vector{0, 1, 10, 11}}, //
        {vector{0, 1, 10, 11}, pair{-10, 15}, vector{0, 1, 5, 6}}, //
        // Constants among holes.
        {vector{1, 2, 5, 6}, 3, pair{0, 12}},          //
        {3, vector{0, 4, 8}, vector{2, 3, 7, 11, 12}}, //
        {vector{1, 5}, vector{2, 6}, 7},               //
        // Zero-one variables, which have no bits encoding.
        {pair{0, 1}, pair{0, 1}, vector{0, 2}}, //
        {pair{0, 1}, vector{0, 1}, pair{0, 1}}  //
    };
    gac_data.insert(gac_data.end(), holey_data.begin(), holey_data.end());

    // Random holey domains: each value of a random span kept with probability
    // two in three, so most have several holes of varying widths.
    auto random_holey = [&](int lower_min, int lower_max, int span_min, int span_max) -> vector<int> {
        std::uniform_int_distribution<int> lower_dist(lower_min, lower_max), span_dist(span_min, span_max), keep(0, 2);
        auto lower = lower_dist(rand);
        auto span = span_dist(rand);
        vector<int> values;
        for (int v = lower; v <= lower + span; ++v)
            if (keep(rand) != 0)
                values.push_back(v);
        if (values.empty())
            values.push_back(lower);
        return values;
    };
    for (int x = 0; x < 10; ++x) {
        auto r1 = random_holey(-10, 10, 5, 15);
        auto r2 = random_holey(-10, 10, 5, 15);
        auto r3 = random_holey(-15, 15, 5, 20);
        gac_data.emplace_back(r1, r2, r3);
    }

    auto plus_sat = [](int a, int b, int c) { return a + b == c; };
    auto minus_sat = [](int a, int b, int c) { return a - b == c; };

    for (bool proofs : {false, true}) {
        if (proofs && ! can_run_veripb())
            continue;
        for (auto & [r1, r2, r3] : data) {
            run_plus_minus_test<Plus>(proofs, view_cfg, Arm::Auto, r1, r2, r3, plus_sat);
            run_plus_minus_test<Minus>(proofs, view_cfg, Arm::Auto, r1, r2, r3, minus_sat);
        }
        for (auto & [r1, r2, r3] : gac_data) {
            for (auto arm : {Arm::GAC, Arm::Dynamic}) {
                run_plus_minus_test<Plus>(proofs, view_cfg, arm, r1, r2, r3, plus_sat);
                run_plus_minus_test<Minus>(proofs, view_cfg, arm, r1, r2, r3, minus_sat);
            }
        }
        if (! proofs && view_wrap_config_is_effectively_bare(view_cfg, n_positions))
            run_dynamic_fallback_test();
        if (view_wrap_config_is_effectively_bare(view_cfg, n_positions))
            for (bool gac : {false, true})
                for (auto & [ar, br] : dup_data) {
                    run_dup_plus_minus_test<Plus>(proofs, AliasV1V2{}, "v1v2", gac, ar, br, plus_sat);
                    run_dup_plus_minus_test<Plus>(proofs, AliasV1V3{}, "v1v3", gac, ar, br, plus_sat);
                    run_dup_plus_minus_test<Plus>(proofs, AliasV2V3{}, "v2v3", gac, ar, br, plus_sat);
                    run_dup_plus_minus_test<Plus>(proofs, AliasAll{}, "all", gac, ar, br, plus_sat);
                    run_dup_plus_minus_test<Minus>(proofs, AliasV1V2{}, "v1v2", gac, ar, br, minus_sat);
                    run_dup_plus_minus_test<Minus>(proofs, AliasV1V3{}, "v1v3", gac, ar, br, minus_sat);
                    run_dup_plus_minus_test<Minus>(proofs, AliasV2V3{}, "v2v3", gac, ar, br, minus_sat);
                    run_dup_plus_minus_test<Minus>(proofs, AliasAll{}, "all", gac, ar, br, minus_sat);
                }

        // The consistency tags (issues #444 and #192): Auto (checked per node) is
        // Dynamic for distinct positions, forced Tabulated tabulates bigger
        // domains too, forced BC is checked for soundness only, and forced GAC
        // and Dynamic are checked per node without tabulating.
        auto suffix = view_wrap_config_label(view_cfg);
        // Dynamic, and so Auto, only promise GAC below the threshold, which the
        // fallback lane sets to zero.
        bool dynamic_is_gac = innards::default_interval_pairs_threshold() >= 256;
        run_tagged_test<Plus>(proofs, suffix, consistency::Auto{}, dynamic_is_gac, {1, 3}, {1, 3}, {2, 6}, plus_sat);
        run_tagged_test<Minus>(proofs, suffix, consistency::Auto{}, dynamic_is_gac, {1, 4}, {1, 3}, {-2, 3}, minus_sat);
        run_tagged_test<Plus>(proofs, suffix, consistency::Tabulated{}, true, {-4, 4}, {-4, 4}, {-8, 8}, plus_sat);
        run_tagged_test<Minus>(proofs, suffix, consistency::Tabulated{}, true, {-4, 4}, {-4, 4}, {-8, 8}, minus_sat);
        run_tagged_test<Plus>(proofs, suffix, consistency::BC{}, false, {1, 3}, {1, 3}, {2, 6}, plus_sat);
        run_tagged_test<Minus>(proofs, suffix, consistency::BC{}, false, {1, 3}, {1, 3}, {-2, 2}, minus_sat);
        run_tagged_test<Plus>(proofs, suffix, consistency::GAC{}, true, {-4, 4}, {-4, 4}, {-8, 8}, plus_sat);
        run_tagged_test<Minus>(proofs, suffix, consistency::GAC{}, true, {-4, 4}, {-4, 4}, {-8, 8}, minus_sat);
        run_tagged_test<Plus>(proofs, suffix, consistency::Dynamic{}, dynamic_is_gac, {-4, 4}, {-4, 4}, {-8, 8}, plus_sat);
        run_tagged_test<Minus>(proofs, suffix, consistency::Dynamic{}, dynamic_is_gac, {-4, 4}, {-4, 4}, {-8, 8}, minus_sat);
    }

    return EXIT_SUCCESS;
}
