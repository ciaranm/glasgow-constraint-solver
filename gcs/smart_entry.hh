#ifndef GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_SMART_ENTRY_HH
#define GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_SMART_ENTRY_HH

#include <variant>
#include <vector>
#include <gcs/variable_id.hh>
#include <gcs/integer.hh>
#include <algorithm> //std::sort
using namespace gcs;


using DomainPair = std::pair<std::vector<Integer>, std::vector<Integer>>;
using Domain = std::vector<Integer>;

// Filters: maybe reuse these elsewhere
//    Domain filter(Domain& dom) {
//        Domain new_dom{};
//        for(const auto& val : dom) {
//            if(val != this->value) {
//                new_dom.emplace_back(val);
//            }
//        }
//        return new_dom;
//    }

//    DomainPair filter(Domain& dom_1, Domain& dom_2) {
//        Domain new_dom{};
//        std::sort(dom_1.begin(), dom_1.end());
//        std::sort(dom_2.begin(), dom_2.end());
//        std::set_intersection(dom_1.begin(),dom_1.end(),
//                              dom_2.begin(),dom_2.end(),
//                              back_inserter(new_dom));
//        return DomainPair{new_dom, new_dom};
//    }

//    DomainPair filter(Domain& dom_1, Domain& dom_2) {
//        Domain new_dom_1{};
//        Domain new_dom_2{};
//        std::sort(dom_1.begin(), dom_1.end());
//        std::sort(dom_2.begin(), dom_2.end());
//        std::set_difference(dom_1.begin(),dom_1.end(),
//                              dom_2.begin(),dom_2.end(),
//                              back_inserter(new_dom_1));
//        std::set_difference(dom_2.begin(),dom_2.end(),
//                            dom_1.begin(),dom_1.end(),
//                            back_inserter(new_dom_2));
//        return DomainPair{new_dom_1, new_dom_2};
//    }

enum ConstraintType {
    LESS_THAN,
    LESS_THAN_EQUAL,
    EQUAL,
    NOT_EQUAL,
    GREATER_THAN,
    GREATER_THAN_EQUAL,
    IN,
    NOT_IN
};

/**
 * \brief Smart entries for smart tables
 */
struct BinaryEntry {
    IntegerVariableID var_1;
    IntegerVariableID var_2;
    ConstraintType constraint_type;

    // Constructor
    BinaryEntry(IntegerVariableID var_1, IntegerVariableID var_2, ConstraintType constraint_type)
    : var_1(var_1), var_2(var_2), constraint_type(constraint_type) {};
};

struct UnaryValueEntry {
    IntegerVariableID var;
    Integer value;
    ConstraintType constraint_type;

    // Constructor
    UnaryValueEntry(const IntegerVariableID &var, const Integer &value, ConstraintType constraint_type)
    : var(var), value(value),constraint_type(constraint_type) {};
};

struct UnarySetEntry {
    IntegerVariableID var;
    std::vector<Integer> values;
    ConstraintType constraint_type;

    // Constructor
    UnarySetEntry(const IntegerVariableID &var, const std::vector<Integer> &values, ConstraintType constraint_type)
    : var(var), values(values), constraint_type(constraint_type) {};
};

using SmartEntry = std::variant<BinaryEntry, UnaryValueEntry, UnarySetEntry>;

using SmartTuples = std::vector<std::vector<SmartEntry>>;

struct EqualsValue : UnaryValueEntry{
    EqualsValue(const IntegerVariableID &var, const Integer &value) : UnaryValueEntry(
            var, value, ConstraintType::EQUAL) {};
};

struct NotEqualsValue : UnaryValueEntry{
    NotEqualsValue(const IntegerVariableID &var, const Integer &value) : UnaryValueEntry(
            var, value, ConstraintType::NOT_EQUAL) {}
};
struct GreaterThanValue : UnaryValueEntry{
    GreaterThanValue(const IntegerVariableID &var, const Integer &value)
            : UnaryValueEntry(var, value, ConstraintType::GREATER_THAN) {}
};

struct GreaterThanEqualValue : UnaryValueEntry{
    GreaterThanEqualValue(const IntegerVariableID &var, const Integer &value)
            : UnaryValueEntry(var, value, ConstraintType::GREATER_THAN_EQUAL) {}
};

struct LessThanValue : UnaryValueEntry{
    LessThanValue(const IntegerVariableID &var, const Integer &value) : UnaryValueEntry(
            var, value, ConstraintType::LESS_THAN) {}
};

struct LessThanEqualValue : UnaryValueEntry{
    LessThanEqualValue(const IntegerVariableID &var, const Integer &value)
            : UnaryValueEntry(var, value, ConstraintType::LESS_THAN_EQUAL) {}
};

struct InSet : UnarySetEntry {
    InSet(const IntegerVariableID& var, const std::vector<Integer> & values)
        : UnarySetEntry(var, values, ConstraintType::IN) {}
};

struct NotInSet : UnarySetEntry {
    NotInSet(const IntegerVariableID& var, const std::vector<Integer> & values)
            : UnarySetEntry(var, values, ConstraintType::NOT_IN) {}
};

struct EqualsVar : BinaryEntry{
    EqualsVar(const IntegerVariableID &var_1, const IntegerVariableID & var_2) : BinaryEntry(
            var_1, var_2, ConstraintType::EQUAL) {};
};

struct NotEqualsVar : BinaryEntry{
    NotEqualsVar(const IntegerVariableID &var_1, const IntegerVariableID & var_2) : BinaryEntry(
            var_1, var_2,  ConstraintType::NOT_EQUAL) {}
};
struct GreaterThanVar : BinaryEntry{
    GreaterThanVar(const IntegerVariableID &var_1, const IntegerVariableID & var_2)
            : BinaryEntry(var_1, var_2,  ConstraintType::GREATER_THAN) {}
};

struct GreaterThanEqualVar : BinaryEntry{
    GreaterThanEqualVar(const IntegerVariableID &var_1, const IntegerVariableID & var_2)
            : BinaryEntry(var_1, var_2,  ConstraintType::GREATER_THAN_EQUAL) {}
};

struct LessThanVar : BinaryEntry{
    LessThanVar(const IntegerVariableID &var_1, const IntegerVariableID & var_2) : BinaryEntry(
            var_1, var_2,  ConstraintType::LESS_THAN) {}
};

struct LessThanEqualVar : BinaryEntry{
    LessThanEqualVar(const IntegerVariableID &var_1, const IntegerVariableID & var_2)
            : BinaryEntry(var_1, var_2,  ConstraintType::LESS_THAN_EQUAL) {}
};



#endif