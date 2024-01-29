#include <gcs/constraints/linear/utils.hh>
#include <gcs/variable_id.hh>

#include <catch2/catch_test_macros.hpp>

#include <utility>

using namespace gcs;
using namespace gcs::innards;

using std::pair;

namespace gcs
{
    template <typename T_>
    auto operator==(const SumOf<T_> & a, const SumOf<T_> & b) -> bool
    {
        return a.terms == b.terms;
    }
}

TEST_CASE("Tidy up linear")
{
    SimpleIntegerVariableID v1{1}, v2{2};

    auto l1 = WeightedSum{} + 1_i * v1 + 0_i * v2;
    CHECK(tidy_up_linear(l1) == pair{TidiedUpLinear{SumOf<SimpleIntegerVariableID>{{v1}}}, 0_i});

    auto l2 = WeightedSum{} + 2_i * v1 + 0_i * v2;
    CHECK(tidy_up_linear(l2) == pair{TidiedUpLinear{SumOf<Weighted<SimpleIntegerVariableID>>{{Weighted<SimpleIntegerVariableID>{2_i, v1}}}}, 0_i});

    auto l3 = WeightedSum{} + 2_i * v1 + 2_i * (v2 + 1_i);
    CHECK(tidy_up_linear(l3) == pair{TidiedUpLinear{SumOf<Weighted<SimpleIntegerVariableID>>{{Weighted<SimpleIntegerVariableID>{2_i, v1}, Weighted<SimpleIntegerVariableID>{2_i, v2}}}}, -2_i});

    auto l4 = WeightedSum{} + 2_i * v1 + 2_i * -v2;
    CHECK(tidy_up_linear(l4) == pair{TidiedUpLinear{SumOf<Weighted<SimpleIntegerVariableID>>{{Weighted<SimpleIntegerVariableID>{2_i, v1}, Weighted<SimpleIntegerVariableID>{-2_i, v2}}}}, 0_i});

    auto l5 = WeightedSum{} + 2_i * v1 + 2_i * (-v2 + 1_i);
    CHECK(tidy_up_linear(l5) == pair{TidiedUpLinear{SumOf<Weighted<SimpleIntegerVariableID>>{{Weighted<SimpleIntegerVariableID>{2_i, v1}, Weighted<SimpleIntegerVariableID>{-2_i, v2}}}}, -2_i});

    auto l6 = WeightedSum{} + 0_i * v1 + 0_i * v2;
    CHECK(tidy_up_linear(l6) == pair{TidiedUpLinear{SumOf<SimpleIntegerVariableID>{{}}}, 0_i});

    auto l7 = WeightedSum{} + 0_i * v1 + 0_i * v2 + 6_i * 1_c;
    CHECK(tidy_up_linear(l7) == pair{TidiedUpLinear{SumOf<SimpleIntegerVariableID>{{}}}, -6_i});
}
