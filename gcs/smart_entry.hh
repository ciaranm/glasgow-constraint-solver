#ifndef GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_SMART_ENTRY_HH
#define GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_SMART_ENTRY_HH

#include <algorithm>
#include <gcs/integer.hh>
#include <gcs/variable_id.hh>
#include <variant>
#include <vector>

namespace gcs
{
    namespace innards
    {
        enum class ConstraintType
        {
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
        struct BinaryEntry
        {
            IntegerVariableID var_1;
            IntegerVariableID var_2;
            ConstraintType constraint_type;

            // Constructor
            BinaryEntry(IntegerVariableID var_1, IntegerVariableID var_2, ConstraintType constraint_type)
            : var_1(var_1), var_2(var_2), constraint_type(constraint_type) {};
        };

        struct UnaryValueEntry
        {
            IntegerVariableID var;
            Integer value;
            ConstraintType constraint_type;

            // Constructor
            UnaryValueEntry(const IntegerVariableID & var, const Integer & value, ConstraintType constraint_type) :
                var(var), value(value), constraint_type(constraint_type){};
        };

        struct UnarySetEntry
        {
            IntegerVariableID var;
            std::vector<Integer> values;
            ConstraintType constraint_type;

            // Constructor
            UnarySetEntry(const IntegerVariableID & var, const std::vector<Integer> & values, ConstraintType constraint_type) :
                var(var), values(values), constraint_type(constraint_type){};
        };
    }

    using SmartEntry = std::variant<innards::BinaryEntry, innards::UnaryValueEntry, innards::UnarySetEntry>;

    using SmartTuples = std::vector<std::vector<SmartEntry>>;

    struct EqualsValue : innards::UnaryValueEntry
    {
        EqualsValue(const IntegerVariableID & var, const Integer & value) :
            UnaryValueEntry(
                var, value, innards::ConstraintType::EQUAL){};
    };

    struct NotEqualsValue : innards::UnaryValueEntry
    {
        NotEqualsValue(const IntegerVariableID & var, const Integer & value) :
            UnaryValueEntry(
                var, value, innards::ConstraintType::NOT_EQUAL)
        {
        }
    };

    struct GreaterThanValue : innards::UnaryValueEntry
    {
        GreaterThanValue(const IntegerVariableID & var, const Integer & value) :
            UnaryValueEntry(var, value, innards::ConstraintType::GREATER_THAN)
        {
        }
    };

    struct GreaterThanEqualValue : innards::UnaryValueEntry
    {
        GreaterThanEqualValue(const IntegerVariableID & var, const Integer & value) :
            UnaryValueEntry(var, value, innards::ConstraintType::GREATER_THAN_EQUAL)
        {
        }
    };

    struct LessThanValue : innards::UnaryValueEntry
    {
        LessThanValue(const IntegerVariableID & var, const Integer & value) :
            UnaryValueEntry(
                var, value, innards::ConstraintType::LESS_THAN)
        {
        }
    };

    struct LessThanEqualValue : innards::UnaryValueEntry
    {
        LessThanEqualValue(const IntegerVariableID & var, const Integer & value) :
            UnaryValueEntry(var, value, innards::ConstraintType::LESS_THAN_EQUAL)
        {
        }
    };

    struct InSet : innards::UnarySetEntry
    {
        InSet(const IntegerVariableID & var, const std::vector<Integer> & values) :
            UnarySetEntry(var, values, innards::ConstraintType::IN)
        {
        }
    };

    struct NotInSet : innards::UnarySetEntry
    {
        NotInSet(const IntegerVariableID & var, const std::vector<Integer> & values) :
            UnarySetEntry(var, values, innards::ConstraintType::NOT_IN)
        {
        }
    };

    struct EqualsVar : innards::BinaryEntry
    {
        EqualsVar(const IntegerVariableID & var_1, const IntegerVariableID & var_2) :
            BinaryEntry(
                var_1, var_2, innards::ConstraintType::EQUAL){};
    };

    struct NotEqualsVar : innards::BinaryEntry
    {
        NotEqualsVar(const IntegerVariableID & var_1, const IntegerVariableID & var_2) :
            BinaryEntry(
                var_1, var_2, innards::ConstraintType::NOT_EQUAL)
        {
        }
    };

    struct GreaterThanVar : innards::BinaryEntry
    {
        GreaterThanVar(const IntegerVariableID & var_1, const IntegerVariableID & var_2) :
            BinaryEntry(var_1, var_2, innards::ConstraintType::GREATER_THAN)
        {
        }
    };

    struct GreaterThanEqualVar : innards::BinaryEntry
    {
        GreaterThanEqualVar(const IntegerVariableID & var_1, const IntegerVariableID & var_2) :
            BinaryEntry(var_1, var_2, innards::ConstraintType::GREATER_THAN_EQUAL)
        {
        }
    };

    struct LessThanVar : innards::BinaryEntry
    {
        LessThanVar(const IntegerVariableID & var_1, const IntegerVariableID & var_2) :
            BinaryEntry(
                var_1, var_2, innards::ConstraintType::LESS_THAN)
        {
        }
    };

    struct LessThanEqualVar : innards::BinaryEntry
    {
        LessThanEqualVar(const IntegerVariableID & var_1, const IntegerVariableID & var_2) :
            BinaryEntry(var_1, var_2, innards::ConstraintType::LESS_THAN_EQUAL)
        {
        }
    };
}

#endif
