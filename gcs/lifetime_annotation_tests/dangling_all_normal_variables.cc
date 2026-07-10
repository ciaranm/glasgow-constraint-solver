#include <gcs/problem.hh>

// This file must not compile under -Werror=dangling: binding a reference to
// the result of Problem::all_normal_variables() on a temporary Problem must
// trigger clang's -Wdangling diagnostic. If it compiles, the
// GCS_LIFETIME_BOUND annotations in gcs/problem.hh have stopped working. See
// valid_uses.cc for the corrected twin.

auto dangling() -> unsigned long long
{
    const auto & vars = gcs::Problem{}.all_normal_variables();
    return vars.size();
}
