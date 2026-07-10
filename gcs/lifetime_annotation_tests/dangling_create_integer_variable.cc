#include <gcs/problem.hh>

// This file must not compile under -Werror=dangling: keeping a variable
// handle created by a temporary Problem must trigger clang's -Wdangling
// diagnostic, because the handle is only meaningful while its Problem is
// alive. If it compiles, the GCS_LIFETIME_BOUND annotation on
// Problem::create_integer_variable() or the GCS_GSL_POINTER annotation on
// SimpleIntegerVariableID has stopped working. See valid_uses.cc for the
// corrected twin.

auto dangling() -> unsigned long long
{
    auto id = gcs::Problem{}.create_integer_variable(gcs::Integer{1}, gcs::Integer{3});
    return id.index;
}
