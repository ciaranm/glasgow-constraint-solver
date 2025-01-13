#include <gcs/exception.hh>
#include <gcs/innards/power.hh>

#include <limits>

using namespace gcs;
using namespace gcs::innards;

using std::numeric_limits;

auto gcs::innards::power2(Integer i) -> Integer
{
    if (i < 0_i || i.raw_value >= numeric_limits<decltype(i.raw_value)>::digits)
        throw UnimplementedException{"Would get overflow on power2"};
    return Integer{(1_i).raw_value << i.raw_value};
}
