#include <gcs/constraints/disjunctive_2d.hh>
#include <gcs/constraints/innards/constraints_test_utils.hh>
#include <gcs/exception.hh>
#include <gcs/problem.hh>
#include <gcs/solve.hh>

#include <algorithm>
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
using namespace gcs::test_innards;

namespace
{
    // The comment the presence-falsification justification writes. Tests count
    // it: a rule that never fires makes every other assertion about it vacuous,
    // and a twin instance that must not fire is only checked by counting to
    // zero.
    const string falsification_marker = "disjunctive2d optional: rectangle";

    // One rectangle of an optional-Disjunctive2D instance. A size or presence
    // spec of {lo, hi} with lo < hi is a decision variable; lo == hi is the
    // constant. A presence of {1, 1} is therefore the *constant* 1, which
    // resolves away and encodes as if the rectangle were not optional at all,
    // and {0, 0} is a rectangle that is never placed.
    struct RectSpec
    {
        pair<int, int> x_range;
        pair<int, int> y_range;
        pair<int, int> width;
        pair<int, int> height;
        pair<int, int> presence;
    };

    [[nodiscard]] auto is_var(const pair<int, int> & spec) -> bool
    {
        return spec.first != spec.second;
    }

    // Solutions are (every x, every y, then every *variable* width, every
    // variable height, and every variable presence, each in rectangle order).
    [[nodiscard]] auto enumerated_ranges(const vector<RectSpec> & rects) -> vector<pair<int, int>>
    {
        vector<pair<int, int>> ranges;
        for (const auto & r : rects)
            ranges.push_back(r.x_range);
        for (const auto & r : rects)
            ranges.push_back(r.y_range);
        for (const auto & r : rects)
            if (is_var(r.width))
                ranges.push_back(r.width);
        for (const auto & r : rects)
            if (is_var(r.height))
                ranges.push_back(r.height);
        for (const auto & r : rects)
            if (is_var(r.presence))
                ranges.push_back(r.presence);
        return ranges;
    }

    // Where a rectangle's presence sits in an enumerated solution. Derived
    // rather than written down per fixture, because getting it wrong reads a
    // *position* instead and the assertion then passes or fails for reasons
    // that have nothing to do with the rule.
    [[nodiscard]] auto presence_position(const vector<RectSpec> & rects, size_t rect) -> size_t
    {
        auto at = 2 * rects.size();
        for (const auto & r : rects)
            if (is_var(r.width))
                ++at;
        for (const auto & r : rects)
            if (is_var(r.height))
                ++at;
        for (size_t i = 0; i < rect; ++i)
            if (is_var(rects[i].presence))
                ++at;
        return at;
    }

    // An absent rectangle occupies no area, so it may overlap anything; a
    // zero-area one is ignored in non-strict mode, as in the plain form.
    [[nodiscard]] auto make_is_satisfying(const vector<RectSpec> & rects, bool strict)
    {
        return [&rects, strict](const vector<int> & vals) {
            auto n = rects.size();
            vector<int> w(n), h(n), present(n);
            auto k = 2 * n;
            for (size_t i = 0; i < n; ++i)
                w[i] = is_var(rects[i].width) ? vals.at(k++) : rects[i].width.first;
            for (size_t i = 0; i < n; ++i)
                h[i] = is_var(rects[i].height) ? vals.at(k++) : rects[i].height.first;
            for (size_t i = 0; i < n; ++i)
                present[i] = is_var(rects[i].presence) ? vals.at(k++) : rects[i].presence.first;

            for (size_t i = 0; i < n; ++i)
                for (size_t j = i + 1; j < n; ++j) {
                    if (! present[i] || ! present[j])
                        continue;
                    if (! strict && ((w[i] == 0 || h[i] == 0) || (w[j] == 0 || h[j] == 0)))
                        continue;
                    int xi = vals[i], yi = vals[n + i], xj = vals[j], yj = vals[n + j];
                    bool sep = (xi + w[i] <= xj) || (xj + w[j] <= xi) || (yi + h[i] <= yj) || (yj + h[j] <= yi);
                    if (! sep)
                        return false;
                }
            return true;
        };
    }

    // Post the instance, returning the variables in enumeration order.
    auto post_optional_disjunctive_2d(Problem & p, const vector<RectSpec> & rects, bool strict) -> vector<IntegerVariableID>
    {
        vector<IntegerVariableID> xs, ys, widths, heights, presences, all_vars;
        for (const auto & r : rects) {
            auto v = p.create_integer_variable(Integer{r.x_range.first}, Integer{r.x_range.second});
            xs.push_back(v);
            all_vars.push_back(v);
        }
        for (const auto & r : rects) {
            auto v = p.create_integer_variable(Integer{r.y_range.first}, Integer{r.y_range.second});
            ys.push_back(v);
            all_vars.push_back(v);
        }
        auto make = [&](const pair<int, int> & spec, vector<IntegerVariableID> & into) {
            if (! is_var(spec)) {
                into.push_back(constant_variable(Integer{spec.first}));
                return;
            }
            auto v = p.create_integer_variable(Integer{spec.first}, Integer{spec.second});
            into.push_back(v);
            all_vars.push_back(v);
        };
        for (const auto & r : rects)
            make(r.width, widths);
        for (const auto & r : rects)
            make(r.height, heights);
        for (const auto & r : rects)
            make(r.presence, presences);

        p.post(Disjunctive2D{xs, ys, widths, heights, presences}.with_strict(strict));
        return all_vars;
    }

    auto run_optional_test(bool proofs, const string & mode, bool strict, const string & tag, const vector<RectSpec> & rects) -> void
    {
        print(cerr, "disjunctive2d optional {} {} n={}{}", mode, tag, rects.size(), proofs ? " with proofs:" : ":");
        cerr << flush;

        set<vector<int>> expected, actual;
        build_expected(expected, make_is_satisfying(rects, strict), enumerated_ranges(rects));
        println(cerr, " expecting {} solutions", expected.size());

        Problem p;
        auto all_vars = post_optional_disjunctive_2d(p, rects, strict);

        auto proof_name = proofs ? make_optional("disjunctive_2d_optional_test_" + mode + "_" + tag) : nullopt;
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

    /// What the falsification marker count must be. Note the asymmetry, which
    /// is 1D's and holds here for the same reason: "must fire" is a claim about
    /// the root, where the fixture is arranged so the rule triggers before any
    /// branching, and it holds whatever the search does afterwards. "Must never
    /// fire" is a claim about every node, so it is only assertable on a fixture
    /// where the rectangle fits under *every* partial assignment --- otherwise
    /// the harness's seed-derived random branching decides whether the rule
    /// fires below the root, and the test is flaky.
    enum class MarkerCount
    {
        AtLeastOne,   ///< the rule must fire
        Never,        ///< the rule must not fire at any node
        Unconstrained ///< firing below the root is legitimate here; see above
    };

    struct FalsificationExpectation
    {
        MarkerCount markers;
        int present_ones;      ///< how many solutions have this rectangle present
        size_t falsified_rect; ///< index of the rectangle under test
    };

    // A falsification fixture and its twin, checked as a pair: the same
    // enumeration check as everywhere else, plus the marker count, plus what
    // the rectangle's presence is allowed to be in a solution.
    auto run_falsification_test(const string & tag, const vector<RectSpec> & rects, const FalsificationExpectation & expect) -> bool
    {
        println(cerr, "disjunctive2d optional falsification {}", tag);

        set<vector<int>> expected, actual;
        build_expected(expected, make_is_satisfying(rects, true), enumerated_ranges(rects));

        Problem p;
        auto all_vars = post_optional_disjunctive_2d(p, rects, true);

        auto proof_name = "disjunctive_2d_optional_falsify_" + tag;
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

        // How many solutions leave the rectangle present, according to brute
        // force. On a "must fire at the root" fixture, this being zero is the
        // semantic half of the marker assertion; on a twin, its being positive
        // is what says the rule did *not* fire at the root, whatever it did
        // below.
        int present_count = 0;
        auto position = presence_position(rects, expect.falsified_rect);
        for (const auto & sol : expected)
            if (sol.at(position) == 1)
                ++present_count;
        if (present_count != expect.present_ones) {
            println(cerr, "{}: brute force says rectangle {} is present in {} solutions, fixture claims {}", tag, expect.falsified_rect,
                present_count, expect.present_ones);
            ok = false;
        }

        check_results(make_optional(proof_name), expected, actual);
        return ok;
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
        vector<RectSpec> rects{
            {{0, 2}, {0, 2}, {2, 2}, {1, 1}, {1, 1}}, {{0, 2}, {0, 2}, {1, 1}, {2, 2}, {1, 1}}, {{0, 3}, {0, 1}, {2, 2}, {1, 1}, {1, 1}}};

        auto build = [&](bool optional_form, const string & proof_name) -> optional<vector<string>> {
            Problem p;
            vector<IntegerVariableID> xs, ys, widths, heights, presences;
            for (const auto & r : rects) {
                xs.push_back(p.create_integer_variable(Integer{r.x_range.first}, Integer{r.x_range.second}));
                ys.push_back(p.create_integer_variable(Integer{r.y_range.first}, Integer{r.y_range.second}));
                widths.push_back(constant_variable(Integer{r.width.first}));
                heights.push_back(constant_variable(Integer{r.height.first}));
                presences.push_back(constant_variable(1_i));
            }

            if (optional_form)
                p.post(Disjunctive2D{xs, ys, widths, heights, presences}.with_strict(strict));
            else
                p.post(Disjunctive2D{xs, ys, widths, heights}.with_strict(strict));

            set<vector<int>> results;
            solve_for_tests(p, make_optional(proof_name), results, tuple{xs});
            auto opb = read_opb_constraints(proof_name);
            auto expected_type = string{strict ? "disjunctive2d_strict" : "disjunctive2d"} + (optional_form ? "_optional" : "");
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
        auto plain = build(false, string{"disjunctive_2d_optional_encoding_plain"} + suffix);
        auto optional_form = build(true, string{"disjunctive_2d_optional_encoding_opt"} + suffix);
        if (! plain || ! optional_form) {
            println(cerr, "constant-presence encoding check: could not read an OPB back");
            return false;
        }
        if (*plain != *optional_form) {
            report_opb_difference("constant-presence encoding check", *plain, *optional_form);
            return false;
        }
        return true;
    }
}

auto main(int argc, char * argv[]) -> int
{
    establish_and_announce_seed(argc, argv);

    // Mode is the first non-flag positional. With no mode given (a manual run
    // rather than the ctest harness) run every mode. Keep in sync with the
    // matching foreach(mode ...) in gcs/CMakeLists.txt.
    string requested_mode;
    for (int i = 1; i < argc; ++i) {
        std::string a = argv[i];
        if (! a.starts_with("--")) {
            requested_mode = a;
            break;
        }
    }
    const vector<string> all_modes = {"strict", "nonstrict", "falsify"};
    const vector<string> modes = requested_mode.empty() ? all_modes : vector<string>{requested_mode};

    bool ok = true;

    for (const auto & mode : modes) {
        if (mode == "falsify") {
            if (! can_run_veripb()) {
                println(cerr, "veripb not available, skipping falsification tests");
                continue;
            }

            // Must fire at the root: rectangle 0 is undecided and pinned on top
            // of rectangle 1, which is constantly present, so there is nowhere
            // for it to go before any branching happens.
            ok &= run_falsification_test("sharp", {{{0, 0}, {0, 0}, {2, 2}, {2, 2}, {0, 1}}, {{0, 0}, {0, 0}, {2, 2}, {2, 2}, {1, 1}}},
                FalsificationExpectation{.markers = MarkerCount::AtLeastOne, .present_ones = 0, .falsified_rect = 0});

            // The same, with the blocker's presence a *variable* fixed to 1
            // rather than the constant: the blocker then keeps its disjunct in
            // the clause and its presence literal in the reason, which is the
            // path a solve actually takes once branching has fixed a presence.
            ok &= run_falsification_test("sharp_var_blocker",
                {{{0, 0}, {0, 0}, {2, 2}, {2, 2}, {0, 1}}, {{0, 0}, {0, 0}, {2, 2}, {2, 2}, {1, 1}}, {{9, 9}, {9, 9}, {1, 1}, {1, 1}, {0, 1}}},
                FalsificationExpectation{.markers = MarkerCount::AtLeastOne, .present_ones = 0, .falsified_rect = 0});

            // The same conclusion, but from *bounds* rather than from fixed
            // positions: each rectangle is 4x4 with two values of freedom on
            // each axis, so the mandatory boxes overlap at [3, 6) x [3, 6)
            // without anything being pinned.
            //
            // What this fixture does *not* establish, and a tripwire for
            // whoever assumes it does: that the four before-flag pols the
            // falsification emits are load-bearing. They are not, on this
            // fixture or on any of the others here --- delete them and every
            // proof in this mode still verifies, because with the pair's
            // bounds in the reason VeriPB's unit propagation refutes the four
            // flags straight off their reification rows. They are emitted
            // anyway because they are the same four refutations the
            // contradiction writes, and *those* are load-bearing: disable them
            // and this file's `mixed_consts` lane fails to verify, as does
            // `disjunctive_2d_test`'s `d1`. So the honest statement is that
            // the falsification differs from the contradiction only in which
            // literal the six-way clause is left with, and it inherits a
            // derivation that is shape-independent rather than one that holds
            // on the shapes tested.
            ok &= run_falsification_test("sharp_ranged", {{{2, 3}, {2, 3}, {4, 4}, {4, 4}, {0, 1}}, {{2, 3}, {2, 3}, {4, 4}, {4, 4}, {1, 1}}},
                FalsificationExpectation{.markers = MarkerCount::AtLeastOne, .present_ones = 0, .falsified_rect = 0});

            // Twin: the rule must never fire. Rectangle 0 fits beside the
            // blocker under every partial assignment, so no node can conclude
            // it is absent.
            ok &= run_falsification_test("twin_free", {{{0, 0}, {0, 0}, {1, 1}, {1, 1}, {0, 1}}, {{5, 5}, {5, 5}, {1, 1}, {1, 1}, {1, 1}}},
                FalsificationExpectation{.markers = MarkerCount::Never, .present_ones = 1, .falsified_rect = 0});

            // Both undecided and mutually exclusive: nothing follows at the
            // root (neither is present, so neither can be ruled out), and
            // whether the rule fires below it depends on the branching.
            ok &= run_falsification_test("both_optional", {{{0, 0}, {0, 0}, {2, 2}, {2, 2}, {0, 1}}, {{0, 0}, {0, 0}, {2, 2}, {2, 2}, {0, 1}}},
                FalsificationExpectation{.markers = MarkerCount::Unconstrained, .present_ones = 1, .falsified_rect = 0});

            continue;
        }

        bool strict;
        if (mode == "strict")
            strict = true;
        else if (mode == "nonstrict")
            strict = false;
        else
            throw UnimplementedException{};

        // Constant-1 presences must encode exactly as no presences at all.
        if (can_run_veripb())
            ok &= check_constant_presence_encoding_is_unchanged(strict);

        // { tag, rectangles }
        vector<pair<string, vector<RectSpec>>> data = {
            // Two unit squares on a small grid, both optional.
            {"units", {{{0, 2}, {0, 2}, {1, 1}, {1, 1}, {0, 1}}, {{0, 2}, {0, 2}, {1, 1}, {1, 1}, {0, 1}}}},
            // One optional rectangle among certainly-present ones.
            {"one_opt", {{{0, 2}, {0, 2}, {2, 2}, {2, 2}, {1, 1}}, {{0, 2}, {0, 2}, {2, 2}, {2, 2}, {0, 1}}}},
            // A constantly-absent rectangle: dropped entirely, and it may sit
            // anywhere including on top of the others.
            {"never", {{{0, 1}, {0, 1}, {2, 2}, {2, 2}, {1, 1}}, {{0, 1}, {0, 1}, {2, 2}, {2, 2}, {0, 0}}}},
            // Three rectangles that cannot all fit, so a presence has to give.
            {"tight", {{{0, 1}, {0, 1}, {2, 2}, {2, 2}, {0, 1}}, {{0, 1}, {0, 1}, {2, 2}, {2, 2}, {0, 1}}, {{0, 1}, {0, 1}, {2, 2}, {2, 2}, {0, 1}}}},
            // Mixed constants: one always present, one never, one free.
            {"mixed_consts",
                {{{0, 2}, {0, 2}, {2, 2}, {1, 1}, {1, 1}}, {{0, 2}, {0, 2}, {1, 1}, {1, 1}, {0, 0}}, {{0, 2}, {0, 2}, {1, 1}, {2, 2}, {0, 1}}}},
            // Negative origins, which the before-pol rides the sign bits for.
            {"negative", {{{-2, 1}, {-2, 1}, {2, 2}, {2, 2}, {0, 1}}, {{-2, 1}, {-2, 1}, {2, 2}, {2, 2}, {0, 1}}}},
            // Variable sizes alongside a variable presence: both kinds of
            // variable end up in the same reason.
            {"var_size", {{{0, 2}, {0, 2}, {1, 2}, {1, 2}, {0, 1}}, {{0, 2}, {0, 2}, {1, 2}, {1, 2}, {1, 1}}}},
            // A size that can be zero, which in non-strict mode escapes the
            // clause the same way an absent rectangle does --- the two escapes
            // have to coexist in one clause.
            {"zero_and_absent", {{{0, 2}, {0, 2}, {0, 2}, {2, 2}, {0, 1}}, {{0, 2}, {0, 2}, {2, 2}, {0, 2}, {0, 1}}}},
            // Degenerate: a single optional rectangle constrains nothing.
            {"single", {{{0, 1}, {0, 1}, {1, 1}, {1, 1}, {0, 1}}}},
        };

        mt19937 rand(*get_seed());
        // Random instances for breadth, every rectangle optional so the
        // presence cross-product is exercised everywhere. Kept small:
        // enumeration is over positions times presences, which grows fast.
        for (int k = 0; k < 12; ++k) {
            uniform_int_distribution<> n_dist(2, 3), lo_dist(0, 2), span_dist(0, 2), size_dist(0, 2), pres_dist(0, 3);
            vector<RectSpec> rects;
            auto n = n_dist(rand);
            for (int i = 0; i < n; ++i) {
                auto xlo = lo_dist(rand), ylo = lo_dist(rand);
                auto w = size_dist(rand), h = size_dist(rand);
                auto pr = pres_dist(rand);
                rects.push_back(RectSpec{{xlo, min(xlo + span_dist(rand), 2)}, {ylo, min(ylo + span_dist(rand), 2)}, {w, w}, {h, h},
                    pr == 0 ? pair{1, 1} : (pr == 1 ? pair{0, 0} : pair{0, 1})});
            }
            data.emplace_back("random" + std::to_string(k), rects);
        }

        for (bool proofs : {false, true}) {
            if (proofs && ! can_run_veripb())
                continue;
            for (const auto & [tag, rects] : data)
                run_optional_test(proofs, mode, strict, tag, rects);
        }
    }

    return ok ? EXIT_SUCCESS : EXIT_FAILURE;
}
