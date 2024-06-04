#include <gcs/innards/integer_variable_state.hh>
#include <util/overloaded.hh>

using namespace gcs;
using namespace gcs::innards;

using std::string;
using std::to_string;

auto gcs::innards::debug_string(const IntegerVariableState & ivar) -> string
{
    return overloaded{
        [](const IntegerVariableConstantState & c) {
            return "const " + to_string(c.value.raw_value);
        },
        [](const IntegerVariableRangeState & r) {
            return "range " + to_string(r.lower.raw_value) + ".." + to_string(r.upper.raw_value);
        },
        [](const IntegerVariableSmallSetState & s) {
            string result = "small set";
            for (int i = 0; i < Bits::number_of_bits; ++i)
                if (s.bits.test(i))
                    result += " " + to_string(i);
            return result;
        },
        [](const IntegerVariableIntervalSetState & s) {
            string result = "iset";
            for (const auto & [l, u] : s.values->each_interval())
                result += " " + to_string(l.raw_value) + ".." + to_string(u.raw_value);
            return result;
        }}
        .visit(ivar);
}
