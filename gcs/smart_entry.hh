#ifndef GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_SMART_ENTRY_HH
#define GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_SMART_ENTRY_HH

#include <variant>
#include <vector>
#include <gcs/variable_id.hh>
#include <gcs/integer.hh>
#include <algorithm> //std::sort
using namespace gcs;

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

/**
 * Sugar classes so users can create SmartEntries a bit more easily.
 */
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
