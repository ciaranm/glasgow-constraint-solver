#include <gcs/constraints/innards/constraints_test_utils.hh>
#include <gcs/constraints/innards/tabulation.hh>
#include <gcs/constraints/innards/triggers.hh>
#include <gcs/constraints/multiply/multiply_bc.hh>
#include <gcs/exception.hh>
#include <gcs/innards/inference_tracker.hh>
#include <gcs/innards/propagators.hh>
#include <gcs/innards/s_expr.hh>
#include <gcs/problem.hh>

#include <cstdlib>
#include <version>

#if defined(__cpp_lib_print) && defined(__cpp_lib_format)
#include <print>
#else
#include <fmt/core.h>
#include <fmt/ostream.h>
#endif
#include <iostream>
#include <memory>
#include <optional>
#include <random>
#include <set>
#include <tuple>
#include <utility>
#include <vector>

using std::cerr;
using std::flush;
using std::make_optional;
using std::make_shared;
using std::make_unique;
using std::mt19937;
using std::nullopt;
using std::optional;
using std::pair;
using std::random_device;
using std::set;
using std::tuple;
using std::unique_ptr;
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
    // A deliberately minimal tabulating constraint: it defines no OPB encoding
    // of its own, relying on an accompanying MultiplyBC over the same three
    // variables for the structural definition, and derives the product
    // relation's table in-proof for GAC. This is the mechanism the friendly
    // arithmetic constraints use to offer tabulated GAC without a table in the
    // OPB (issue #444); this test exists to establish that
    // build_table_in_proof's leaf backtrack RUP lines verify against MultiplyBC's
    // non-linear bit-product encoding, not just against a linear sum. When
    // claim_determined is set, the product is claimed as functionally
    // determined by the operands, additionally establishing that the skipped
    // level's parent backtrack lines verify by unit propagation pinning the
    // product through the bit-product encoding.
    class TabulateProductForTest : public Constraint
    {
    private:
        SimpleIntegerVariableID _v1, _v2, _v3;
        bool _claim_determined;

    public:
        TabulateProductForTest(SimpleIntegerVariableID v1, SimpleIntegerVariableID v2, SimpleIntegerVariableID v3, bool claim_determined) :
            _v1(v1), _v2(v2), _v3(v3), _claim_determined(claim_determined)
        {
        }

        [[nodiscard]] auto clone() const -> unique_ptr<Constraint> override
        {
            return make_unique<TabulateProductForTest>(_v1, _v2, _v3, _claim_determined);
        }

        auto install(Propagators & propagators, State &, ProofModel * const) && -> void override
        {
            Triggers triggers;
            triggers.on_change = {_v1, _v2, _v3};

            auto data = make_shared<optional<ExtensionalData>>(nullopt);
            propagators.install_initialiser(
                [data = data, v1 = _v1, v2 = _v2, v3 = _v3, claim_determined = _claim_determined](
                    State & state, auto & inference, ProofLogger * const logger) {
                    vector<DeterminedVariable> determined;
                    if (claim_determined)
                        determined.push_back({v3, [](const vector<Integer> & vals) -> optional<Integer> { return vals[0] * vals[1]; }});
                    *data = build_table_in_proof(
                        vector<IntegerVariableID>{v1, v2, v3}, determined, nullopt,
                        [](const vector<Integer> & vals) { return vals[0] * vals[1] == vals[2]; }, "multtab", "building GAC table for multiplication",
                        state, logger);
                    if (! data->has_value())
                        inference.infer(logger, FalseLiteral{}, JustifyUsingRUP{}, ExplicitReason{ReasonLiterals{}});
                },
                InitialiserPriority::Expensive);

            propagators.install(
                constraint_id(),
                [data = data](const State & state, auto & inference, ProofLogger * const logger) -> PropagatorState {
                    if (data->has_value())
                        return propagate_extensional(data->value(), state, inference, logger);
                    else
                        return PropagatorState::DisableUntilBacktrack;
                },
                triggers);
        }

        [[nodiscard]] auto s_expr(const ProofModel * const) const -> SExpr override
        {
            vector<SExpr> terms{SExpr::atom(as_string(_constraint_id)), SExpr::atom("test_tabulated_product")};
            return SExpr::list(std::move(terms));
        }
    };
}

auto run_tabulated_product_test(bool proofs, bool claim_determined, pair<int, int> v1_range, pair<int, int> v2_range, pair<int, int> v3_range) -> void
{
    print(cerr, "tabulated product {} {} {}{}{}", v1_range, v2_range, v3_range, claim_determined ? " claiming determined" : "",
        proofs ? " with proofs:" : ":");
    cerr << flush;
    set<tuple<int, int, int>> expected, actual;

    build_expected(expected, [](int a, int b, int c) { return a * b == c; }, v1_range, v2_range, v3_range);
    println(cerr, " expecting {} solutions", expected.size());

    Problem p;
    auto v1 = p.create_integer_variable(Integer(v1_range.first), Integer(v1_range.second), "v1");
    auto v2 = p.create_integer_variable(Integer(v2_range.first), Integer(v2_range.second), "v2");
    auto v3 = p.create_integer_variable(Integer(v3_range.first), Integer(v3_range.second), "v3");
    p.post(MultiplyBC{v1, v2, v3});
    p.post(TabulateProductForTest{v1, v2, v3, claim_determined});

    auto proof_name = proofs ? make_optional("tabulation_test") : nullopt;

    solve_for_tests_checking_gac(p, proof_name, expected, actual, tuple{v1, v2, v3});

    check_results(proof_name, expected, actual);
}

auto main(int, char *[]) -> int
{
    vector<tuple<pair<int, int>, pair<int, int>, pair<int, int>>> data = {
        {{1, 3}, {1, 3}, {1, 9}},      //
        {{-3, 3}, {-3, 3}, {-9, 9}},   // negatives and zero throughout
        {{0, 4}, {1, 3}, {0, 12}},     //
        {{-2, 2}, {2, 4}, {-10, 10}},  //
        {{-4, -2}, {-3, -1}, {2, 12}}, // both operands negative
        {{2, 3}, {2, 3}, {50, 60}},    // no satisfying tuple: empty table at the root
        {{0, 0}, {-3, 3}, {-2, 2}},    // fixed zero operand
        {{2, 2}, {3, 3}, {6, 6}},      // all fixed, tautology
        {{2, 2}, {3, 3}, {7, 7}},      // all fixed, contradiction
    };

    random_device rand_dev;
    mt19937 rand(rand_dev());
    for (int x = 0; x < 3; ++x)
        generate_random_data(rand, data, random_bounds(-6, 6, 1, 5), random_bounds(-6, 6, 1, 5), random_bounds(-20, 20, 5, 20));

    for (bool proofs : {false, true}) {
        if (proofs && ! can_run_veripb())
            continue;
        for (bool claim_determined : {false, true})
            for (auto & [r1, r2, r3] : data)
                run_tabulated_product_test(proofs, claim_determined, r1, r2, r3);
    }

    return EXIT_SUCCESS;
}
