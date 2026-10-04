/* A Disjunctive2D as a presolver's donor (#973).
 *
 * Each axis of a Disjunctive2D projects to a Cumulative: the rectangles as
 * tasks along that axis, their extent on the other axis as heights, and the
 * other axis's window as the capacity. The projection publishes its flags and
 * rows in the proof, and itself as a donor, so the three presolvers that derive
 * Cumulatives can derive from it as they would from a posted one. Nothing here
 * posts a Cumulative, so anything a presolver installs came from a projection.
 *
 * Checked against brute force over a sweep of small instances, with the
 * projection's own propagator on and off, since the donor is there either way.
 * A mutation per presolver shows the certificates over a projection's rows
 * are what VeriPB checks, rather than something that verifies whatever.
 */

#include <gcs/constraints/disjunctive_2d.hh>
#include <gcs/constraints/innards/constraints_test_utils.hh>
#include <gcs/presolvers/cumulative_strengthening.hh>
#include <gcs/presolvers/inferred_cumulative.hh>
#include <gcs/presolvers/inferred_disjunctive.hh>
#include <gcs/problem.hh>
#include <gcs/solve.hh>

#include <cstdlib>
#include <functional>
#include <iostream>
#include <memory>
#include <optional>
#include <random>
#include <string>
#include <utility>
#include <vector>
#include <version>

#if defined(__cpp_lib_print) && defined(__cpp_lib_format)
#include <print>
#else
#include <fmt/core.h>
#include <fmt/ostream.h>
#endif

using std::cerr;
using std::function;
using std::make_optional;
using std::make_shared;
using std::nullopt;
using std::optional;
using std::pair;
using std::string;
using std::to_string;
using std::vector;

#if defined(__cpp_lib_print) && defined(__cpp_lib_format)
using std::println;
#else
using fmt::println;
#endif

using namespace gcs;
using namespace gcs::innards;
using namespace gcs::test_innards;

namespace
{
    auto fail(const string & message) -> void
    {
        println(cerr, "disjunctive2d presolver test failure: {}", message);
        std::exit(EXIT_FAILURE);
    }

    struct Rect
    {
        pair<int, int> x, y, w, h;
        bool optional = false;
    };

    struct Instance
    {
        vector<Rect> rects;
        bool strict = true;
    };

    auto describe(const Instance & inst) -> string
    {
        string result = inst.strict ? "strict" : "nonstrict";
        for (const auto & r : inst.rects)
            result += " [x" + to_string(r.x.first) + ".." + to_string(r.x.second) + " y" + to_string(r.y.first) + ".." + to_string(r.y.second) +
                " w" + to_string(r.w.first) + ".." + to_string(r.w.second) + " h" + to_string(r.h.first) + ".." + to_string(r.h.second) +
                (r.optional ? " opt" : "") + "]";
        return result;
    }

    enum class Which
    {
        Disjunctive,
        Cumulative,
        Strengthening
    };

    auto name_of(Which which) -> string
    {
        switch (which) {
        case Which::Disjunctive: return "inferred_disjunctive";
        case Which::Cumulative: return "inferred_cumulative";
        case Which::Strengthening: return "strengthening";
        }
        return "?";
    }

    struct Counts
    {
        std::size_t posted = 0, optional_instances = 0;
    };

    struct Setup
    {
        Which which;
        bool projection = false;
        optional<InferredDisjunctiveMutation> disjunctive_mutation = nullopt;
        optional<InferredCumulativeMutation> cumulative_mutation = nullopt;
        optional<CumulativeStrengtheningMutation> strengthening_mutation = nullopt;
    };

    // Every variable, in one order, so that a solution is a tuple of them.
    auto post(Problem & p, const Instance & inst, const Setup & setup) -> pair<vector<IntegerVariableID>, function<Counts()>>
    {
        vector<IntegerVariableID> xs, ys, ws, hs, ps, all;
        auto var = [&](pair<int, int> d) {
            auto v = p.create_integer_variable(Integer{d.first}, Integer{d.second});
            all.push_back(v);
            return v;
        };
        auto any_optional = false;
        for (const auto & r : inst.rects) {
            xs.push_back(var(r.x));
            ys.push_back(var(r.y));
            ws.push_back(r.w.first == r.w.second ? constant_variable(Integer{r.w.first}) : var(r.w));
            hs.push_back(r.h.first == r.h.second ? constant_variable(Integer{r.h.first}) : var(r.h));
            any_optional = any_optional || r.optional;
        }
        if (any_optional)
            for (const auto & r : inst.rects)
                ps.push_back(r.optional ? var({0, 1}) : constant_variable(1_i));

        auto rules = Disjunctive2DRules{};
        if (setup.projection)
            rules.cumulative_projection = CumulativeRules{};
        if (any_optional)
            p.post(Disjunctive2D{xs, ys, ws, hs, ps}.with_strict(inst.strict).with_rules(rules));
        else
            p.post(Disjunctive2D{xs, ys, ws, hs}.with_strict(inst.strict).with_rules(rules));

        function<Counts()> counts;
        switch (setup.which) {
        case Which::Disjunctive: {
            auto stats = make_shared<InferredDisjunctiveStats>();
            auto presolver = InferredDisjunctive{stats}.with_minimum_clique_size(2);
            if (setup.disjunctive_mutation)
                presolver.with_proof_mutation(*setup.disjunctive_mutation);
            p.add_presolver(presolver);
            counts = [stats] { return Counts{stats->cliques_posted, 0}; };
        } break;
        case Which::Cumulative: {
            auto stats = make_shared<InferredCumulativeStats>();
            auto presolver = InferredCumulative{stats};
            if (setup.cumulative_mutation)
                presolver.with_proof_mutation(*setup.cumulative_mutation);
            p.add_presolver(presolver);
            counts = [stats] { return Counts{stats->cuts_posted, 0}; };
        } break;
        case Which::Strengthening: {
            auto stats = make_shared<CumulativeStrengtheningStats>();
            auto presolver = CumulativeStrengthening{stats};
            if (setup.strengthening_mutation)
                presolver.with_proof_mutation(*setup.strengthening_mutation);
            p.add_presolver(presolver);
            counts = [stats] { return Counts{stats->derived.constraints, 0}; };
        } break;
        }
        return {all, counts};
    }

    // Brute force, in the order post() creates the variables in.
    auto brute_force(const Instance & inst) -> long long
    {
        struct Var
        {
            int lo, hi;
        };
        vector<Var> vars;
        auto any_optional = false;
        for (const auto & r : inst.rects)
            any_optional = any_optional || r.optional;
        for (const auto & r : inst.rects) {
            vars.push_back({r.x.first, r.x.second});
            vars.push_back({r.y.first, r.y.second});
            if (r.w.first != r.w.second)
                vars.push_back({r.w.first, r.w.second});
            if (r.h.first != r.h.second)
                vars.push_back({r.h.first, r.h.second});
        }
        if (any_optional)
            for (const auto & r : inst.rects)
                if (r.optional)
                    vars.push_back({0, 1});

        vector<int> vals(vars.size());
        long long count = 0;
        function<void(size_t)> go = [&](size_t k) {
            if (k == vars.size()) {
                struct Placed
                {
                    int x, y, w, h;
                    bool present;
                };
                vector<Placed> placed;
                size_t at = 0;
                for (const auto & r : inst.rects) {
                    Placed q{};
                    q.x = vals[at++];
                    q.y = vals[at++];
                    q.w = r.w.first == r.w.second ? r.w.first : vals[at++];
                    q.h = r.h.first == r.h.second ? r.h.first : vals[at++];
                    placed.push_back(q);
                }
                for (size_t i = 0; i < inst.rects.size(); ++i)
                    placed[i].present = true;
                if (any_optional)
                    for (size_t i = 0; i < inst.rects.size(); ++i)
                        if (inst.rects[i].optional)
                            placed[i].present = 1 == vals[at++];
                for (size_t i = 0; i < placed.size(); ++i)
                    for (size_t j = i + 1; j < placed.size(); ++j) {
                        const auto & a = placed[i];
                        const auto & b = placed[j];
                        if (! a.present || ! b.present)
                            continue;
                        if (! inst.strict && (a.w == 0 || a.h == 0 || b.w == 0 || b.h == 0))
                            continue;
                        auto apart = a.x + a.w <= b.x || b.x + b.w <= a.x || a.y + a.h <= b.y || b.y + b.h <= a.y;
                        if (! apart)
                            return;
                    }
                ++count;
                return;
            }
            for (int v = vars[k].lo; v <= vars[k].hi; ++v) {
                vals[k] = v;
                go(k + 1);
            }
        };
        go(0);
        return count;
    }

    // Enumerate with a proof and without, check both against brute force and
    // the proof against VeriPB, and say what the presolver posted.
    auto check(const Instance & inst, const Setup & setup, const string & name) -> Counts
    {
        auto expected = brute_force(inst);
        auto enumerate = [&](bool proofs) -> pair<long long, Counts> {
            Problem p;
            auto [vars, counts] = post(p, inst, setup);
            long long solutions = 0;
            solve_with(p, SolveCallbacks{.solution = [&](const CurrentState &) -> bool {
                ++solutions;
                return true;
            }},
                proofs ? make_optional<ProofOptions>(ProofFileNames{name}) : nullopt);
            if (solutions != expected)
                fail(name + ": " + to_string(solutions) + " solutions against brute force's " + to_string(expected) + " on " + describe(inst) +
                    " with " + name_of(setup.which) + (setup.projection ? " and the projection on" : "") + (proofs ? "" : ", proofs off"));
            return {solutions, counts()};
        };
        auto [without, unproved] = enumerate(false);
        auto [with, counts] = enumerate(true);
        if (unproved.posted != counts.posted)
            fail(name + ": " + name_of(setup.which) + " posted " + to_string(counts.posted) + " with proofs and " + to_string(unproved.posted) +
                " without on " + describe(inst));
        if (can_run_veripb())
            verify_proof_and_clean_up(name);
        else
            dispose_of_proof_files(name);
        return counts;
    }

    auto expect_rejected(const Instance & inst, const Setup & setup, const string & what) -> void
    {
        const string name = "disjunctive_2d_presolver_mutation";
        Problem p;
        auto [vars, counts] = post(p, inst, setup);
        solve_with(p, SolveCallbacks{.trace = [](const CurrentState &) -> bool { return true; }}, make_optional<ProofOptions>(ProofFileNames{name}));
        if (0 == counts().posted)
            fail(what + ": nothing was posted, so the mutation had nothing to corrupt");
        if (can_run_veripb()) {
            if (run_veripb(name + ".opb", name + ".pbp"))
                fail("veripb accepted the " + what + " mutation, so the certificate over the projection has slack in it");
            println(cerr, "veripb rejected the {} mutation, as expected", what);
        }
        dispose_of_proof_files(name);
    }
}

auto main(int argc, char * argv[]) -> int
{
    establish_and_announce_seed(argc, argv);

    // Three 2x2 squares in a strip of height three: no two can share a column,
    // since their heights sum past it, so the x projection has every pair in
    // conflict. That is a clique, a cover, and a capacity of three that nothing
    // can use all of. With x in [0, 4] they fit side by side, just.
    const Instance strip{{{{0, 4}, {0, 1}, {2, 2}, {2, 2}}, {{0, 4}, {0, 1}, {2, 2}, {2, 2}}, {{0, 4}, {0, 1}, {2, 2}, {2, 2}}}};
    // Three 1x2 bars in a strip of height five: any two fit in a column, three
    // do not, and strengthening rounds five down to four.
    const Instance bars{{{{0, 2}, {0, 3}, {1, 1}, {2, 2}}, {{0, 2}, {0, 3}, {1, 1}, {2, 2}}, {{0, 2}, {0, 3}, {1, 1}, {2, 2}}}};

    for (auto projection : {false, true}) {
        auto suffix = string{projection ? "_projection" : ""};
        if (0 == check(strip, Setup{.which = Which::Disjunctive, .projection = projection}, "disjunctive_2d_presolver_strip_d" + suffix).posted)
            fail("inferred disjunctive posted no clique over the strip's projection");
        if (0 == check(strip, Setup{.which = Which::Cumulative, .projection = projection}, "disjunctive_2d_presolver_strip_c" + suffix).posted)
            fail("inferred cumulative posted no cut over the strip's projection");
        if (0 == check(bars, Setup{.which = Which::Strengthening, .projection = projection}, "disjunctive_2d_presolver_bars_s" + suffix).posted)
            fail("strengthening strengthened nothing over the bars' projection");
    }
    println(cerr, "the fixtures: every presolver derives from a projection, and matches brute force");

    // The same over random small instances: sizes that may vary, strict or
    // not, and optional rectangles, whose presences every presolver now
    // carries into what it derives (#1136).
    std::mt19937 rng(*get_seed());
    auto pick = [&](int lo, int hi) { return std::uniform_int_distribution<int>{lo, hi}(rng); };
    // Forty rounds, and then on until every presolver has posted over
    // optional rectangles: for about one seed in 150, forty rounds draw no
    // instance on which one of them does, and the checks below would fail
    // for want of coverage rather than for anything wrong.
    Counts totals[3];
    auto covered = [&] {
        for (const auto & t : totals)
            if (0 == t.posted || 0 == t.optional_instances)
                return false;
        return true;
    };
    constexpr int min_rounds = 40, max_rounds = 400;
    for (int round = 0; round < max_rounds && (round < min_rounds || ! covered()); ++round) {
        Instance inst;
        inst.strict = pick(0, 3) != 0;
        auto n = pick(2, 3);
        auto any_optional = pick(0, 3) == 0;
        for (int i = 0; i < n; ++i) {
            Rect r;
            auto w = pick(1, 3), h = pick(1, 3);
            r.w = pick(0, 3) == 0 ? pair{w, w + 1} : pair{w, w};
            r.h = pick(0, 3) == 0 ? pair{h, h + 1} : pair{h, h};
            r.x = {0, pick(1, 3)};
            r.y = {0, pick(0, 2)};
            r.optional = any_optional && pick(0, 1) == 0;
            inst.rects.push_back(r);
        }
        for (auto which : {Which::Disjunctive, Which::Cumulative, Which::Strengthening}) {
            auto counts = check(inst, Setup{.which = which, .projection = pick(0, 1) == 0}, "disjunctive_2d_presolver_sweep_" + name_of(which));
            totals[static_cast<int>(which)].posted += counts.posted;
            if (any_optional && counts.posted > 0)
                ++totals[static_cast<int>(which)].optional_instances;
        }
    }
    for (auto which : {Which::Disjunctive, Which::Cumulative, Which::Strengthening}) {
        const auto & t = totals[static_cast<int>(which)];
        println(cerr, "sweep, {}: {} posted, on {} instances with optional rectangles", name_of(which), t.posted, t.optional_instances);
        if (0 == t.posted)
            fail("the sweep posted nothing from " + name_of(which) + " in " + to_string(max_rounds) +
                " rounds, so it checked no certificate over a projection");
        if (0 == t.optional_instances)
            fail("the sweep posted nothing from " + name_of(which) + " over optional rectangles in " + to_string(max_rounds) + " rounds (#1136)");
    }

    // Mutations: each presolver's own, over the projection's rows.
    expect_rejected(strip, Setup{.which = Which::Disjunctive, .disjunctive_mutation = inferred_disjunctive_mutation::ClaimRhsZero{}},
        "inferred disjunctive rhs zero");
    expect_rejected(strip, Setup{.which = Which::Cumulative, .cumulative_mutation = inferred_cumulative_mutation::ClaimTighterCapacity{}},
        "inferred cumulative tighter capacity");
    expect_rejected(bars, Setup{.which = Which::Strengthening, .strengthening_mutation = cumulative_strengthening_mutation::ClaimOneBetter{}},
        "strengthening one better");

    return EXIT_SUCCESS;
}
