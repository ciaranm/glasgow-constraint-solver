#include <gcs/exception.hh>
#include <gcs/innards/power.hh>

#include <limits>
#include <optional>

using namespace gcs;
using namespace gcs::innards;

using std::nullopt;
using std::numeric_limits;
using std::optional;

auto gcs::innards::power2(Integer i) -> Integer
{
    if (i < 0_i || i.raw_value >= numeric_limits<decltype(i.raw_value)>::digits)
        throw UnimplementedException{"Would get overflow on power2"};
    return Integer{(1_i).raw_value << i.raw_value};
}

auto gcs::innards::checked_integer_power(Integer base, Integer exp) -> optional<Integer>
{
    if (exp == 0_i)
        return 1_i;
    if (base == 1_i)
        return 1_i;
    if (base == -1_i)
        return ((exp.raw_value & 1) == 0) ? 1_i : -1_i;
    if (exp < 0_i)
        return nullopt;
    if (base == 0_i)
        return 0_i;

    long long result = 1;
    long long b = base.raw_value;
    long long e = exp.raw_value;
    while (e > 0) {
        if (e & 1)
            if (__builtin_mul_overflow(result, b, &result))
                return nullopt;
        e >>= 1;
        if (e > 0)
            if (__builtin_mul_overflow(b, b, &b))
                return nullopt;
    }
    return Integer{result};
}
