/* vim: set sw=4 sts=4 et foldmethod=syntax : */

#include <gcs/innards/linear_utils.hh>
#include <gcs/variable_id.hh>

#include <catch2/catch_test_macros.hpp>

#include <utility>

using namespace gcs;
using namespace gcs::innards;

using std::pair;

TEST_CASE("Sanitise linear")
{
    SimpleIntegerVariableID v1{1}, v2{2};

    Linear l1{pair{1_i, v1}, pair{0_i, v2}};
    CHECK(sanitise_linear(l1) == pair{SanitisedLinear{SimpleIntegerVariableIDs{v1}}, 0_i});

    Linear l2{pair{2_i, v1}, pair{0_i, v2}};
    CHECK(sanitise_linear(l2) == pair{SanitisedLinear{SimpleLinear{pair{2_i, v1}}}, 0_i});

    Linear l3{pair{2_i, v1}, pair{2_i, v2 + 1_i}};
    CHECK(sanitise_linear(l3) == pair{SanitisedLinear{SimpleLinear{pair{2_i, v1}, pair{2_i, v2}}}, -2_i});

    Linear l4{pair{2_i, v1}, pair{2_i, -v2}};
    CHECK(sanitise_linear(l4) == pair{SanitisedLinear{SimpleLinear{pair{2_i, v1}, pair{-2_i, v2}}}, 0_i});

    Linear l5{pair{2_i, v1}, pair{2_i, -v2 + 1_i}};
    CHECK(sanitise_linear(l5) == pair{SanitisedLinear{SimpleLinear{pair{2_i, v1}, pair{-2_i, v2}}}, -2_i});
}
