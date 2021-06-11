/* vim: set sw=4 sts=4 et foldmethod=syntax : */

#include <gcs/integer_variable.hh>
#include <util/overloaded.hh>

using namespace gcs;

using std::make_optional;
using std::nullopt;
using std::optional;
using std::visit;

auto gcs::lower_bound(const IntegerVariable & var) -> Integer
{
    return visit(overloaded {
            [] (const IntegerRangeVariable & v) { return v.lower; },
            [] (const IntegerConstant & v) { return v.value; },
            [] (const IntegerSmallSetVariable & v) { return v.lower + Integer{ v.bits.countr_zero() }; },
            [] (const IntegerSetVariable & v) { return *v.values->begin(); }
            }, var);
}

auto gcs::upper_bound(const IntegerVariable & var) -> Integer
{
    return visit(overloaded {
            [] (const IntegerRangeVariable & v) { return v.upper; },
            [] (const IntegerConstant & v) { return v.value; },
            [] (const IntegerSmallSetVariable & v) { return v.lower + Integer{ Bits::number_of_bits } - Integer{ v.bits.countl_zero() }; },
            [] (const IntegerSetVariable & v) { return *v.values->rbegin(); }
            }, var);
}

auto gcs::in_domain(const IntegerVariable & var, const Integer val) -> bool
{
    return visit(overloaded {
            [val] (const IntegerRangeVariable & v) { return val >= v.lower && val <= v.upper; },
            [val] (const IntegerConstant & v) { return val == v.value; },
            [val] (const IntegerSmallSetVariable & v) {
                if (val < v.lower || val > (v.lower + Integer{ Bits::number_of_bits - 1 }))
                    return false;
                else
                    return v.bits.test((val - v.lower).raw_value);
            },
            [val] (const IntegerSetVariable & v) { return v.values->end() != v.values->find(val); }
            }, var);
}

auto gcs::optional_single_value(const IntegerVariable & var) -> optional<Integer>
{
    return visit(overloaded {
            [] (const IntegerRangeVariable & v) -> optional<Integer> {
                if (v.lower == v.upper)
                    return make_optional(v.lower);
                else
                    return nullopt;
            },
            [] (const IntegerConstant & v) -> optional<Integer> {
                return make_optional(v.value);
            },
            [] (const IntegerSmallSetVariable & v) -> optional<Integer> {
                if (v.bits.has_single_bit())
                    return make_optional(v.lower + Integer{ v.bits.countr_zero() });
                else
                    return nullopt;
            },
            [] (const IntegerSetVariable & v) -> optional<Integer> {
                if (1 == v.values->size())
                    return make_optional(*v.values->begin());
                else
                    return nullopt;
            }
            }, var);
}

auto gcs::domain_size(const IntegerVariable & var) -> Integer
{
    return visit(overloaded {
            [] (const IntegerConstant &)           { return Integer{ 1 }; },
            [] (const IntegerRangeVariable & r)    { return r.upper - r.lower + Integer{ 1 }; },
            [] (const IntegerSmallSetVariable & s) { return Integer{ s.bits.popcount() }; },
            [] (const IntegerSetVariable & s)      { return Integer(s.values->size()); }
            }, var);
}

