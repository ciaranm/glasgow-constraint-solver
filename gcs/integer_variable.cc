/* vim: set sw=4 sts=4 et foldmethod=syntax : */

#include <gcs/integer_variable.hh>
#include <util/overloaded.hh>

using namespace gcs;

using std::string;
using std::to_string;
using std::visit;

auto gcs::debug_string(const IntegerVariable & ivar) -> string
{
    return visit(overloaded {
            [] (const IntegerConstant & c) {
                return "const " + to_string(c.value.raw_value);
            },
            [] (const IntegerRangeVariable & r) {
                return "range " + to_string(r.lower.raw_value) + ".." + to_string(r.upper.raw_value);
            },
            [] (const IntegerSmallSetVariable & s) {
                string result = "small set";
                for (int i = 0 ; i < Bits::number_of_bits ; ++i)
                    if (s.bits.test(i))
                        result += " " + to_string(i);
                return result;
            },
            [] (const IntegerSetVariable & s) {
                string result = "set";
                for (auto & v : *s.values)
                    result += " " + to_string(v.raw_value);
                return result;
            },
            [] (const IntegerOffsetVariable & s) {
                return "offset " + to_string(s.offset.raw_value) + " on " + to_string(s.var.index);
            } }, ivar);
}

