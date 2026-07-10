#include <gcs/array_param.hh>

#include <vector>

// This file must not compile under -Werror=dangling: binding a reference to
// the contents of a temporary ArrayParam must trigger clang's -Wdangling
// diagnostic. If it compiles, the GCS_LIFETIME_BOUND annotations in
// gcs/array_param.hh have stopped working. See valid_uses.cc for the
// corrected twin.

auto dangling() -> int
{
    const std::vector<int> & v = *gcs::VectorArrayParam<int>{{1, 2, 3}};
    return v[0];
}
