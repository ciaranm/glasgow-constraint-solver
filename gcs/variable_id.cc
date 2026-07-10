#include <gcs/variable_id.hh>

#include <util/overloaded.hh>

using namespace gcs;

using std::string;

auto gcs::operator+(IntegerVariableID v, Integer o) -> IntegerVariableID
{
    // An offset of zero is the identity: return the variable itself rather than
    // a do-nothing view, mirroring the constant-folding in the other branches.
    return overloaded{
        [&](const SimpleIntegerVariableID & v) -> IntegerVariableID {
            return o == 0_i ? IntegerVariableID{v} : IntegerVariableID{ViewOfIntegerVariableID{v, false, o}};
        },                                                                                                                      //
        [&](const ConstantIntegerVariableID & v) -> IntegerVariableID { return ConstantIntegerVariableID{v.const_value + o}; }, //
        [&](const ViewOfIntegerVariableID & v) -> IntegerVariableID {
            auto then_add = v.then_add + o;
            if (! v.negate_first && then_add == 0_i)
                return v.actual_variable;
            return ViewOfIntegerVariableID{v.actual_variable, v.negate_first, then_add};
        } //
    }
        .visit(v);
}

auto gcs::operator-(IntegerVariableID v, Integer o) -> IntegerVariableID
{
    return overloaded{
        [&](const SimpleIntegerVariableID & v) -> IntegerVariableID { return ViewOfIntegerVariableID{v, false, -o}; },          //
        [&](const ConstantIntegerVariableID & v) -> IntegerVariableID { return ConstantIntegerVariableID{v.const_value - o}; }, //
        [&](const ViewOfIntegerVariableID & v) -> IntegerVariableID {
            return ViewOfIntegerVariableID{v.actual_variable, v.negate_first, v.then_add - o};
        } //
    }
        .visit(v);
}

auto gcs::operator-(IntegerVariableID v) -> IntegerVariableID
{
    return overloaded{
        [&](const SimpleIntegerVariableID & v) -> IntegerVariableID { return ViewOfIntegerVariableID{v, true, 0_i}; },       //
        [&](const ConstantIntegerVariableID & v) -> IntegerVariableID { return ConstantIntegerVariableID{-v.const_value}; }, //
        [&](const ViewOfIntegerVariableID & v) -> IntegerVariableID {
            return ViewOfIntegerVariableID{v.actual_variable, ! v.negate_first, -v.then_add};
        } //
    }
        .visit(v);
}
