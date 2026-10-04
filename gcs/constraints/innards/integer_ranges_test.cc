// The integer range rule (dev_docs/integer-ranges.md): every input lies in
// Integer::min_bounded_value() .. Integer::max_bounded_value(), and anything
// outside it throws IntegerOverflow. A view's offset lies in that range too, so
// a view's values reach about twice as far as a variable's. This checks both
// halves of the rule: inputs just outside the range are refused, and
// constraints over variables and views at the very edges of it solve correctly
// and write proofs that verify. The second half is what fixed the range at an
// eighth of the machine range rather than a quarter: at a quarter, LessThan,
// AllDifferent and Lex over views at the full reach all failed to write their
// model.

#include <gcs/constraints/all_different.hh>
#include <gcs/constraints/comparison.hh>
#include <gcs/constraints/equals.hh>
#include <gcs/constraints/innards/constraints_test_utils.hh>
#include <gcs/constraints/lex.hh>
#include <gcs/constraints/plus.hh>
#include <gcs/constraints/table.hh>
#include <gcs/exception.hh>
#include <gcs/problem.hh>
#include <gcs/solve.hh>

#include <cstddef>
#include <cstdlib>
#include <functional>
#include <iostream>
#include <optional>
#include <set>
#include <string>
#include <tuple>
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
using std::nullopt;
using std::set;
using std::string;
using std::tuple;
using std::vector;

#if defined(__cpp_lib_print) && defined(__cpp_lib_format)
using std::println;
#else
using fmt::println;
#endif

using namespace gcs;
using namespace gcs::test_innards;

namespace
{
    const Integer A = Integer::min_bounded_value();
    const Integer B = Integer::max_bounded_value();

    auto expect_overflow(const string & what, const function<void()> & f) -> void
    {
        println(cerr, "integer ranges: {} is refused", what);
        bool refused = false;
        try {
            f();
        }
        catch (const innards::IntegerOverflow &) {
            refused = true;
        }
        if (! refused)
            throw UnexpectedException{what + " was accepted, but lies outside the bounded range"};
    }

    auto run_refusal_tests() -> void
    {
        Problem p;
        auto x = p.create_integer_variable(0_i, 3_i, "x");
        expect_overflow("a view offset one below the range", [&] { [[maybe_unused]] auto v = x + (A - 1_i); });
        expect_overflow("a view offset one above the range", [&] { [[maybe_unused]] auto v = x - (A - 1_i); });
        expect_overflow("a composed view whose offsets sum past the range", [&] { [[maybe_unused]] auto v = (x + B) + 1_i; });
        expect_overflow("a constant one above the range", [&] { [[maybe_unused]] auto c = constant_variable(B + 1_i); });
        expect_overflow("a constant one below the range", [&] { [[maybe_unused]] auto c = constant_variable(A - 1_i); });
        expect_overflow("a constant folded past the range", [&] { [[maybe_unused]] auto c = constant_variable(B) + 1_i; });
        expect_overflow("a domain one below the range", [&] { [[maybe_unused]] auto v = p.create_integer_variable(A - 1_i, 0_i); });
        expect_overflow("a domain one above the range", [&] { [[maybe_unused]] auto v = p.create_integer_variable(0_i, B + 1_i); });

        // The edges themselves are fine, and the range is symmetric, so negating
        // them is too.
        [[maybe_unused]] auto in_range = vector<IntegerVariableID>{x + A, x + B, -x + A, -x + B, constant_variable(A), constant_variable(B),
            -constant_variable(B), -constant_variable(A), -(x + A), -(x + B)};
    }

    // Three variables, each over three values at one end of the range, each
    // used through a view whose offset is at one end of the range or zero.
    struct Term
    {
        bool at_top;
        bool negate;
        Integer offset;
    };

    struct Config
    {
        string name;
        vector<Term> terms;
    };

    auto value_of(const Term & t, Integer base_value) -> Integer
    {
        return (t.negate ? -base_value : base_value) + t.offset;
    }

    using Values = vector<Integer>;

    auto run_config(bool proofs, const Config & config, const string & constraint_name,
        const function<void(Problem &, const vector<IntegerVariableID> &)> & post, const function<bool(const Values &)> & satisfied) -> void
    {
        Problem p;
        vector<IntegerVariableID> bases, views;
        vector<vector<Integer>> base_values;
        for (std::size_t i = 0; i < config.terms.size(); ++i) {
            const auto & t = config.terms[i];
            auto lo = t.at_top ? B - 2_i : A, hi = t.at_top ? B : A + 2_i;
            bases.push_back(p.create_integer_variable(lo, hi, "x" + std::to_string(i)));
            views.push_back((t.negate ? -bases.back() : bases.back()) + t.offset);
            base_values.push_back({lo, lo + 1_i, hi});
        }

        set<tuple<vector<Integer>>> expected, actual;
        for (auto a : base_values[0])
            for (auto b : base_values[1])
                for (auto c : base_values[2]) {
                    Values vals{value_of(config.terms[0], a), value_of(config.terms[1], b), value_of(config.terms[2], c)};
                    if (satisfied(vals))
                        expected.emplace(vector<Integer>{a, b, c});
                }

        println(cerr, "integer ranges: {} over {}{}: expecting {} solutions", constraint_name, config.name, proofs ? " with proofs" : "",
            expected.size());
        post(p, views);
        auto proof_name = proofs ? make_optional("integer_ranges_test") : nullopt;
        // extract_from_state narrows to int, which cannot hold these values.
        solve_for_tests_with_callbacks(
            p, proof_name,
            [&](const CurrentState & state) -> bool {
                vector<Integer> values;
                for (const auto & b : bases)
                    values.push_back(state(b));
                actual.emplace(values);
                return true;
            },
            [](const CurrentState &) -> bool { return true; });
        check_results(proof_name, expected, actual);
    }

    auto run_edge_tests(bool proofs) -> void
    {
        vector<Config> configs{// Every view near the bottom of its reach, and every one near the top.
            {"the bottom", {{false, false, A}, {false, false, A}, {false, false, A}}},
            {"the top", {{true, false, B}, {true, false, B}, {true, false, B}}},
            // Plain variables and negations at the ends of the range, which the
            // Table rows can match.
            {"plain edges", {{false, false, 0_i}, {true, true, 0_i}, {true, false, 0_i}}},
            // The widest spread two terms can have: one view near the bottom of
            // its reach and one near the top, with a plain variable beside them.
            {"a spread", {{false, false, A}, {false, true, B}, {true, false, 0_i}}},
            {"negated views", {{true, true, A}, {false, true, B}, {false, true, A}}},
            // Offsets at both ends that cancel, so that the sum in Plus lands
            // near zero and has solutions.
            {"cancelling offsets", {{false, false, A}, {false, false, B}, {false, true, B}}}};

        for (const auto & config : configs) {
            run_config(
                proofs, config, "LessThan", [](Problem & p, const vector<IntegerVariableID> & v) { p.post(LessThan{v[0], v[1]}); },
                [](const Values & v) { return v[0] < v[1]; });
            run_config(
                proofs, config, "NotEquals", [](Problem & p, const vector<IntegerVariableID> & v) { p.post(NotEquals{v[0], v[2]}); },
                [](const Values & v) { return v[0] != v[2]; });
            run_config(
                proofs, config, "AllDifferent", [](Problem & p, const vector<IntegerVariableID> & v) { p.post(AllDifferent{v}); },
                [](const Values & v) { return v[0] != v[1] && v[0] != v[2] && v[1] != v[2]; });
            run_config(
                proofs, config, "LexGreaterEqual",
                [](Problem & p, const vector<IntegerVariableID> & v) { p.post(LexGreaterEqual{{v[0], v[1]}, {v[2], v[0]}}); },
                [](const Values & v) { return v[0] > v[2] || (v[0] == v[2] && v[1] >= v[0]); });
            run_config(
                proofs, config, "Plus", [](Problem & p, const vector<IntegerVariableID> & v) { p.post(Plus{v[0], v[2], v[1]}); },
                [](const Values & v) { return v[0] + v[2] == v[1]; });
            // Tuple values are inputs, so they lie in the range, though the views
            // reach beyond it: a row that names the ends of the range matches
            // only where a view takes such a value.
            run_config(
                proofs, config, "Table",
                [](Problem & p, const vector<IntegerVariableID> & v) {
                    p.post(Table{{v[0], v[2]}, SimpleTuples{{A, A}, {B, B}, {A, B}, {0_i, B}, {B - 1_i, A + 1_i}}});
                },
                [](const Values & v) {
                    auto pair = tuple{v[0], v[2]};
                    return pair == tuple{A, A} || pair == tuple{B, B} || pair == tuple{A, B} || pair == tuple{0_i, B} ||
                        pair == tuple{B - 1_i, A + 1_i};
                });
        }
    }
}

namespace
{
    // An objective that is a view at either end of the range, minimised and
    // maximised. A view beyond the range used to be too wide for a bit vector
    // of its own, and the conclusion then claimed a bound that included the
    // offset min: had dropped (#1209); such a view is now refused, and these
    // are the widest that remain.
    auto run_objective_test(bool proofs, Integer c, bool negate, bool maximise) -> void
    {
        println(cerr, "integer ranges: {} {}x + {}{}", maximise ? "maximise" : "minimise", negate ? "-" : "", c, proofs ? " with proofs" : "");
        Problem p;
        auto x = p.create_integer_variable(A, B, "x");
        auto y = p.create_integer_variable(0_i, 3_i, "y");
        p.post(Equals{x, y});
        auto objective = (negate ? -x : IntegerVariableID{x}) + c;
        if (maximise)
            p.maximise(objective);
        else
            p.minimise(objective);

        std::optional<Integer> best;
        string proof_name = "integer_ranges_objective";
        solve_with(p,
            SolveCallbacks{
                .solution = [&](const CurrentState & s) -> bool {
                    best = s(objective);
                    return true;
                },
                .stats_report = silent_stats_report() //
            },
            proofs ? make_optional<ProofOptions>(ProofFileNames{proof_name}) : nullopt);
        // x ranges over 0..3, so the objective's own part ranges over 0..3 or -3..0.
        auto expected = negate ? (maximise ? 0_i : -3_i) : (maximise ? 3_i : 0_i);
        if (best != expected + c)
            throw UnexpectedException{"wrong optimum"};
        if (proofs)
            verify_proof_and_clean_up(proof_name);
    }
}

auto main(int argc, char * argv[]) -> int
{
    establish_and_announce_seed(argc, argv);

    run_refusal_tests();

    for (bool proofs : {false, true}) {
        if (proofs && ! can_run_veripb())
            continue;
        run_edge_tests(proofs);
        for (auto c : {A, B})
            for (bool negate : {false, true})
                for (bool maximise : {false, true})
                    run_objective_test(proofs, c, negate, maximise);
    }

    return EXIT_SUCCESS;
}
