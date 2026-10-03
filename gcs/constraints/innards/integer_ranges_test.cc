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
#include <gcs/constraints/among.hh>
#include <gcs/constraints/bin_packing.hh>
#include <gcs/constraints/comparison.hh>
#include <gcs/constraints/cumulative.hh>
#include <gcs/constraints/difference.hh>
#include <gcs/constraints/element.hh>
#include <gcs/constraints/equals.hh>
#include <gcs/constraints/global_cardinality.hh>
#include <gcs/constraints/in.hh>
#include <gcs/constraints/innards/constraints_test_utils.hh>
#include <gcs/constraints/inverse.hh>
#include <gcs/constraints/knapsack.hh>
#include <gcs/constraints/lex.hh>
#include <gcs/constraints/linear.hh>
#include <gcs/constraints/logical.hh>
#include <gcs/constraints/mdd.hh>
#include <gcs/constraints/min_distance.hh>
#include <gcs/constraints/parity.hh>
#include <gcs/constraints/plus.hh>
#include <gcs/constraints/regular.hh>
#include <gcs/constraints/smart_table.hh>
#include <gcs/constraints/sort.hh>
#include <gcs/constraints/table.hh>
#include <gcs/constraints/value_precede.hh>
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
#include <unordered_map>
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
using std::nullopt;
using std::pair;
using std::set;
using std::string;
using std::tuple;
using std::unordered_map;
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
        expect_overflow("a domain one below the range", [&] { p.create_integer_variable(A - 1_i, 0_i); });
        expect_overflow("a domain one above the range", [&] { p.create_integer_variable(0_i, B + 1_i); });

        // The edges themselves are fine, and the range is symmetric, so negating
        // them is too.
        [[maybe_unused]] auto in_range = vector<IntegerVariableID>{x + A, x + B, -x + A, -x + B, constant_variable(A), constant_variable(B),
            -constant_variable(B), -constant_variable(A), -(x + A), -(x + B)};
    }

    // Every constraint parameter is an input. Each of these is one past an end
    // of the range and must be refused when the constraint is made; the edges
    // themselves must be accepted.
    auto run_parameter_refusal_tests() -> void
    {
        Problem p;
        auto x = p.create_integer_variable(0_i, 3_i, "x"), y = p.create_integer_variable(0_i, 3_i, "y"), z = p.create_integer_variable(0_i, 3_i, "z");
        auto over = B + 1_i, under = A - 1_i;

        vector<pair<string, function<void(Integer)>>> posts{
            {"AllDifferentExcept's excluded value", [&](Integer v) { p.post(AllDifferentExcept{{x, y}, {v}}); }},
            {"SymmetricAllDifferent's start", [&](Integer v) { p.post(SymmetricAllDifferent{{x, y}, v}); }},
            {"Among's value of interest", [&](Integer v) { p.post(Among{{x, y}, {v}, z}); }},
            {"BinPacking's size", [&](Integer v) { p.post(BinPacking{{x}, {v}, vector<IntegerVariableID>{y}}); }},
            {"BinPacking's capacity", [&](Integer v) { p.post(BinPacking{{x}, {1_i}, vector<Integer>{v}}); }},
            {"Cumulative's length", [&](Integer v) { p.post(Cumulative{{x}, {v}, {1_i}, 1_i}); }},
            {"DifferenceConstraints' weight", [&](Integer v) { p.post(DifferenceConstraints{{DifferenceEdge{x, y, v}}}); }},
            {"Element's index start", [&](Integer v) { p.post(Element{z, pair{x, v}, {y}}); }},
            {"ElementConstantArray's value", [&](Integer v) { p.post(ElementConstantArray{z, x, {v}}); }},
            {"GlobalCardinality's value", [&](Integer v) { p.post(GlobalCardinality{{x, y}, {v}, {z}}); }},
            {"In's value", [&](Integer v) { p.post(In{x, vector<Integer>{v}}); }},
            {"Inverse's start", [&](Integer v) { p.post(Inverse{{x}, {y}, v}); }},
            {"Knapsack's coefficient", [&](Integer v) { p.post(Knapsack{{v}, {1_i}, {x}, y, z}); }},
            {"a linear coefficient", [&](Integer v) { p.post(LinearEquality{WeightedSum{} + v * x, 0_i}); }},
            {"a linear right-hand side", [&](Integer v) { p.post(LinearLessThanEqual{WeightedSum{} + 1_i * x, v}); }},
            {"MDD's transition value", [&](Integer v) { p.post(MDD{{x}, {{{{v, 0}}}}, {1, 1}, {0}}); }},
            {"MinDistance's distance", [&](Integer v) { p.post(MinDistance{{x, y}, z, MinDistance::Matrix{{0_i, v}, {v, 0_i}}}); }},
            {"Regular's transition value", [&](Integer v) { p.post(Regular{{x}, 2, vector<unordered_map<Integer, long>>{{{v, 1}}, {}}, {1}}); }},
            {"SmartTable's value", [&](Integer v) { p.post(SmartTable{{x}, SmartTuples{{SmartTable::equals(x, v)}}}); }},
            {"ArgSort's offset", [&](Integer v) { p.post(ArgSort{{x}, {y}, v}); }},
            {"Table's tuple value", [&](Integer v) { p.post(Table{{x}, SimpleTuples{{v}}}); }},
            {"Table's wildcard tuple value", [&](Integer v) { p.post(Table{{x, y}, WildcardTuples{{v, Wildcard{}}}}); }},
            {"NegativeTable's tuple value", [&](Integer v) { p.post(NegativeTable{{x}, SimpleTuples{{v}}}); }},
            {"ValuePrecede's chain value", [&](Integer v) { p.post(ValuePrecede{v, 1_i, {x, y}}); }}};

        // A condition's value may be one past the top, since `x <= B` is stored
        // as `x < B + 1`; so these use two past it, and one below the bottom.
        auto cond_over = B + 2_i;
        vector<pair<string, function<void(Integer)>>> conditions{{"a comparison's condition", [&](Integer v) { p.post(LessThanIf{x, y, z == v}); }},
            {"an equality's condition", [&](Integer v) { p.post(EqualsIff{x, y, z >= v}); }},
            {"a Lex condition", [&](Integer v) { p.post(LexLessThanIf{{x}, {y}, z < v}); }},
            {"a linear constraint's condition", [&](Integer v) { p.post(LinearLessThanEqualIf{WeightedSum{} + 1_i * x, 1_i, z != v}); }},
            {"a literal of Or", [&](Integer v) { p.post(Or{{x == v, y == 1_i}, innards::TrueLiteral{}}); }},
            {"a literal of AndIf", [&](Integer v) { p.post(AndIf{{x == 1_i}, y == v}); }},
            {"a literal of ParityOdd", [&](Integer v) { p.post(ParityOdd{{x == v, y == 1_i}}); }}};

        // The edges pass the range check. Some constraints refuse a negative
        // value for reasons of their own, such as a length, which is not what
        // this is checking, so that refusal is let through.
        auto accepted = [](const function<void(Integer)> & post, Integer v) {
            try {
                post(v);
            }
            catch (const InvalidProblemDefinitionException &) {
            }
        };
        for (const auto & [what, post] : posts) {
            expect_overflow(what + " one above the range", [&] { post(over); });
            expect_overflow(what + " one below the range", [&] { post(under); });
            accepted(post, B);
            accepted(post, A);
        }
        for (const auto & [what, post] : conditions) {
            expect_overflow(what + " two above the range", [&] { post(cond_over); });
            expect_overflow(what + " one below the range", [&] { post(under); });
            accepted(post, B + 1_i);
            accepted(post, A);
        }

        // A regular expression's integers are compiled, and so checked, when
        // the constraint is installed.
        expect_overflow("an integer in a regular expression one above the range", [&] {
            Problem q;
            auto w = q.create_integer_variable(0_i, 1_i, "w");
            q.post(Regular{{w}, std::to_string(over.raw_value)});
            solve_with(q, SolveCallbacks{});
        });
        expect_overflow("an integer in a regular expression too long for any Integer", [&] {
            Problem q;
            auto w = q.create_integer_variable(0_i, 1_i, "w");
            q.post(Regular{{w}, "99999999999999999999999"});
            solve_with(q, SolveCallbacks{});
        });
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
            run_config(
                proofs, config, "ValuePrecede", [](Problem & p, const vector<IntegerVariableID> & v) { p.post(ValuePrecede{A, B, v}); },
                [](const Values & v) {
                    for (const auto & value : v) {
                        if (value == A)
                            return true;
                        if (value == B)
                            return false;
                    }
                    return true;
                });
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
    // MinDistance with the largest distance the range allows, and z a plain
    // variable over the whole range or a view at either end of it (#1168).
    // Two positions over two sites at distance B, so z is 0 when they share a
    // site and B when they do not.
    // AllDifferentExcept with a constant equal to an excluded value beside a
    // view at full reach. The pair's half-reification then includes the
    // literal `constant != excluded`, which is false, and the row used to be
    // written with the full reification coefficient, as big as the largest
    // rows the model has; pol steps over it gave VeriPB rows whose slack
    // overflows its 64-bit arithmetic, and it rejected the solution lines.
    auto run_all_different_except_test(bool proofs) -> void
    {
        struct Term
        {
            bool is_constant;
            Integer lo, hi; // the variable's domain, or the constant twice
            bool negate;
            Integer offset;
        };
        struct Shape
        {
            string name;
            vector<Term> terms;
            vector<Integer> excluded;
        };
        vector<Shape> shapes{{"A, -v + B, except A", {{true, A, A, false, 0_i}, {false, -1_i, 1_i, true, B}}, {A}},
            {"x + B, A, except A", {{false, B - 1_i, B, false, B}, {true, A, A, false, 0_i}}, {A}},
            {"x + A, B, except B", {{false, A, A + 1_i, false, A}, {true, B, B, false, 0_i}}, {B}},
            {"A, A, v + B, except A", {{true, A, A, false, 0_i}, {true, A, A, false, 0_i}, {false, -1_i, 1_i, false, B}}, {A}},
            {"x + B, y + A, except A", {{false, B - 1_i, B, false, B}, {false, A, A + 1_i, false, A}}, {A}}};

        for (const auto & shape : shapes) {
            Problem p;
            vector<IntegerVariableID> vars, bases;
            vector<pair<Integer, Integer>> base_domains;
            for (const auto & t : shape.terms) {
                if (t.is_constant) {
                    vars.push_back(constant_variable(t.lo));
                    continue;
                }
                bases.push_back(p.create_integer_variable(t.lo, t.hi));
                base_domains.emplace_back(t.lo, t.hi);
                vars.push_back((t.negate ? -bases.back() : IntegerVariableID{bases.back()}) + t.offset);
            }
            p.post(AllDifferentExcept{vars, shape.excluded});

            // Brute force over the base variables' values.
            auto satisfied = [&](const vector<Integer> & base_values) {
                vector<Integer> values;
                std::size_t next = 0;
                for (const auto & t : shape.terms) {
                    if (t.is_constant)
                        values.push_back(t.lo);
                    else {
                        values.push_back((t.negate ? -base_values[next] : base_values[next]) + t.offset);
                        ++next;
                    }
                }
                for (std::size_t i = 0; i < values.size(); ++i)
                    for (std::size_t j = i + 1; j < values.size(); ++j)
                        if (values[i] == values[j] && std::ranges::find(shape.excluded, values[i]) == shape.excluded.end())
                            return false;
                return true;
            };
            set<tuple<vector<Integer>>> expected, actual;
            vector<Integer> base_values(bases.size(), 0_i);
            auto recurse = [&](auto && self, std::size_t b) -> void {
                if (b == bases.size()) {
                    if (satisfied(base_values))
                        expected.emplace(base_values);
                    return;
                }
                for (auto v = base_domains[b].first; v <= base_domains[b].second; ++v) {
                    base_values[b] = v;
                    self(self, b + 1);
                }
            };
            recurse(recurse, 0);

            println(
                cerr, "integer ranges: AllDifferentExcept {}{}: expecting {} solutions", shape.name, proofs ? " with proofs" : "", expected.size());
            auto proof_name = proofs ? make_optional("integer_ranges_test") : nullopt;
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
    }

    auto run_min_distance_test(bool proofs) -> void
    {
        struct ZShape
        {
            string name;
            Integer lo, hi;
            bool negate;
            Integer offset;
        };
        vector<ZShape> shapes{{"z over the range", A, B, false, 0_i}, {"z = w + B", A, 0_i, false, B}, {"z = w + A", 0_i, B, false, A},
            {"z = -w + A", A, 0_i, true, A}, {"z = -w + B", 0_i, B, true, B}};
        for (const auto & shape : shapes)
            for (auto propagation : {MinDistancePropagation::CheckOnly, MinDistancePropagation::ForwardBound, MinDistancePropagation::PairSupport,
                     MinDistancePropagation::ForwardBoundMatch, MinDistancePropagation::PairSupportMatch}) {
                Problem p;
                auto x = p.create_integer_variable_vector(2, 0_i, 1_i, "x");
                auto w = p.create_integer_variable(shape.lo, shape.hi, "w");
                auto z = (shape.negate ? -w : IntegerVariableID{w}) + shape.offset;
                p.post(MinDistance{x, z, MinDistance::Matrix{{0_i, B}, {B, 0_i}}, std::nullopt, propagation});

                set<tuple<vector<Integer>>> expected, actual;
                for (auto a : {0_i, 1_i})
                    for (auto b : {0_i, 1_i}) {
                        auto distance = a == b ? 0_i : B;
                        auto w_value = shape.negate ? -(distance - shape.offset) : distance - shape.offset;
                        if (w_value >= shape.lo && w_value <= shape.hi)
                            expected.emplace(vector<Integer>{a, b, w_value});
                    }

                println(cerr, "integer ranges: MinDistance at distance B, {}, propagation {}{}: expecting {} solutions", shape.name,
                    static_cast<int>(propagation), proofs ? " with proofs" : "", expected.size());
                auto proof_name = proofs ? make_optional("integer_ranges_test") : nullopt;
                solve_for_tests_with_callbacks(
                    p, proof_name,
                    [&](const CurrentState & state) -> bool {
                        actual.emplace(vector<Integer>{state(x[0]), state(x[1]), state(w)});
                        return true;
                    },
                    [](const CurrentState &) -> bool { return true; });
                check_results(proof_name, expected, actual);
            }
    }

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
    run_parameter_refusal_tests();

    for (bool proofs : {false, true}) {
        if (proofs && ! can_run_veripb())
            continue;
        run_edge_tests(proofs);
        run_min_distance_test(proofs);
        run_all_different_except_test(proofs);
        for (auto c : {A, B})
            for (bool negate : {false, true})
                for (bool maximise : {false, true})
                    run_objective_test(proofs, c, negate, maximise);
    }

    return EXIT_SUCCESS;
}
