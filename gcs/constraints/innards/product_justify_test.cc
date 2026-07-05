#include <gcs/constraints/innards/constraints_test_utils.hh>
#include <gcs/constraints/multiply/multiply_bc.hh>
#include <gcs/exception.hh>
#include <gcs/innards/inference_tracker.hh>
#include <gcs/innards/proofs/proof_logger.hh>
#include <gcs/innards/proofs/proof_model.hh>
#include <gcs/innards/proofs/pseudo_boolean.hh>
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
#include <set>
#include <tuple>
#include <utility>
#include <vector>

using std::cerr;
using std::flush;
using std::make_optional;
using std::make_shared;
using std::make_unique;
using std::nullopt;
using std::pair;
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
    // Each fragment emits a small, self-contained piece of proof against the
    // cake multiply encoding, at the root, under domains the test has pinned
    // in advance. The point of the harness is that a wrong fragment fails
    // veripb in a test that contains nothing else, rather than deep inside a
    // full propagation proof.
    enum class Fragment
    {
        TrivialRup, // emit an order-encoding bound as RUP: proves the wiring, nothing else
    };

    // A test-only constraint: defines the real cake multiply encoding for
    // x * y = z, runs one selected justification fragment in an initialiser,
    // and otherwise only rejects violating complete assignments (which is RUP
    // against the encoding), so that the solutions the solver logs agree with
    // the OPB while leaving every intermediate propagation to the fragment
    // under test.
    class ProductFragmentForTest : public Constraint
    {
    private:
        SimpleIntegerVariableID _v1, _v2, _v3;
        Fragment _fragment;

    public:
        ProductFragmentForTest(SimpleIntegerVariableID v1, SimpleIntegerVariableID v2, SimpleIntegerVariableID v3, Fragment fragment) :
            _v1(v1), _v2(v2), _v3(v3), _fragment(fragment)
        {
        }

        [[nodiscard]] auto clone() const -> unique_ptr<Constraint> override
        {
            return make_unique<ProductFragmentForTest>(_v1, _v2, _v3, _fragment);
        }

        auto install(Propagators & propagators, State & initial_state, ProofModel * const optional_model) && -> void override
        {
            auto encoding = make_shared<mult_bc::EncodingData>();
            if (optional_model)
                *encoding = mult_bc::define_encoding(*optional_model, initial_state, constraint_id(), as_string(constraint_id()), _v1, _v2, _v3);

            propagators.install_initialiser(
                [encoding = encoding, v1 = _v1, v2 = _v2, v3 = _v3, fragment = _fragment](State & state, auto &, ProofLogger * const logger) {
                    if (! logger)
                        return;
                    switch (fragment) {
                    case Fragment::TrivialRup:
                        logger->emit_rup_proof_line(WPBSum{} + 1_i * (v3 >= state.lower_bound(v3)) >= 1_i, ProofLevel::Top);
                        break;
                    }
                },
                InitialiserPriority::Expensive);

            Triggers triggers;
            triggers.on_instantiated = {_v1, _v2, _v3};
            propagators.install(
                constraint_id(),
                [v1 = _v1, v2 = _v2, v3 = _v3](const State & state, auto & inference, ProofLogger * const logger) -> PropagatorState {
                    auto a = state.optional_single_value(v1), b = state.optional_single_value(v2), c = state.optional_single_value(v3);
                    if (a && b && c && *a * *b != *c)
                        inference.contradiction(logger, JustifyUsingRUP{}, ExplicitReason{ReasonLiterals{v1 == *a, v2 == *b, v3 == *c}});
                    return PropagatorState::Enable;
                },
                triggers);
        }

        [[nodiscard]] auto s_expr(const ProofModel * const) const -> SExpr override
        {
            return SExpr::list({SExpr::atom(as_string(_constraint_id)), SExpr::atom("test_product_fragment")});
        }
    };
}

namespace
{
    auto run_fragment_test(
        bool proofs, Fragment fragment, const std::string & name, pair<int, int> v1_range, pair<int, int> v2_range, pair<int, int> v3_range) -> void
    {
        print(cerr, "product fragment {} over {} {} {}{}", name, v1_range, v2_range, v3_range, proofs ? " with proofs:" : ":");
        cerr << flush;

        set<tuple<int, int, int>> expected, actual;
        build_expected(expected, [](int a, int b, int c) { return a * b == c; }, v1_range, v2_range, v3_range);
        println(cerr, " expecting {} solutions", expected.size());

        Problem p;
        auto v1 = p.create_integer_variable(Integer(v1_range.first), Integer(v1_range.second), "v1");
        auto v2 = p.create_integer_variable(Integer(v2_range.first), Integer(v2_range.second), "v2");
        auto v3 = p.create_integer_variable(Integer(v3_range.first), Integer(v3_range.second), "v3");
        p.post(ProductFragmentForTest{v1, v2, v3, fragment});

        auto proof_name = proofs ? make_optional("product_justify_test") : nullopt;
        solve_for_tests(p, proof_name, actual, tuple{v1, v2, v3});
        check_results(proof_name, expected, actual);
    }
}

auto main(int, char *[]) -> int
{
    for (bool proofs : {false, true}) {
        if (proofs && ! can_run_veripb())
            break;

        run_fragment_test(proofs, Fragment::TrivialRup, "trivial rup", {2, 5}, {1, 3}, {2, 15});
        run_fragment_test(proofs, Fragment::TrivialRup, "trivial rup signed", {-3, 3}, {-2, 4}, {-12, 12});
    }

    return EXIT_SUCCESS;
}
