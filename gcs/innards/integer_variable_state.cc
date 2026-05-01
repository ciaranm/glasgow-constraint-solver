#include <gcs/innards/integer_variable_state.hh>
#include <util/overloaded.hh>

#include <version>

#if defined(__cpp_lib_format)
#include <format>
using std::format;
#else
#include <fmt/core.h>
using fmt::format;
#endif

using namespace gcs;
using namespace gcs::innards;

using std::string;

auto gcs::innards::debug_string(const IntegerVariableState & ivar) -> string
{
    return overloaded{
        [](const IntegerVariableConstantState & c) {
            return format("const {}", c.value.raw_value);
        },
        [](const IntegerVariableRangeState & r) {
            return format("range {}..{}", r.lower.raw_value, r.upper.raw_value);
        },
        [](const IntegerVariableSmallSetState & s) {
            string result = "small set";
            for (int i = 0; i < Bits::number_of_bits; ++i)
                if (s.bits.test(i))
                    result += format(" {}", i);
            return result;
        },
        [](const IntegerVariableIntervalSetState & s) {
            string result = "iset";
            for (const auto & [l, u] : s.values->each_interval())
                result += format(" {}..{}", l.raw_value, u.raw_value);
            return result;
        }}
        .visit(ivar);
}
