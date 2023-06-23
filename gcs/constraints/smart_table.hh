#ifndef GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_SMART_TABLE_HH
#define GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_SMART_TABLE_HH

#include <gcs/constraint.hh>
#include <gcs/extensional.hh>
#include <gcs/variable_id.hh>

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
        struct BinaryEntry final
        {
            IntegerVariableID var_1;
            IntegerVariableID var_2;
            ConstraintType constraint_type;
        };

        struct UnaryValueEntry final
        {
            IntegerVariableID var;
            Integer value;
            ConstraintType constraint_type;
        };

        struct UnarySetEntry final
        {
            IntegerVariableID var;
            std::vector<Integer> values;
            ConstraintType constraint_type;
        };
    }

    using SmartEntry = std::variant<innards::BinaryEntry, innards::UnaryValueEntry, innards::UnarySetEntry>;

    using SmartTuples = std::vector<std::vector<SmartEntry>>;

    /**
     * \brief Constrain that the specified variables are equal to one of the specified
     * smart tuples.
     *
     * \ingroup Constraints
     * \see Table
     */
    class SmartTable : public Constraint
    {
    private:
        const std::vector<IntegerVariableID> _vars;
        SmartTuples _tuples;

    public:
        explicit SmartTable(std::vector<IntegerVariableID> vars, SmartTuples tuples);
        virtual auto clone() const -> std::unique_ptr<Constraint> override;
        virtual auto describe_for_proof() -> std::string override;
        virtual auto install(innards::Propagators &, innards::State &) && -> void override;

        [[nodiscard]] static inline auto equals(const IntegerVariableID & a, const IntegerVariableID & b) -> SmartEntry
        {
            return innards::BinaryEntry{a, b, innards::ConstraintType::EQUAL};
        }

        [[nodiscard]] static inline auto equals(const IntegerVariableID & a, Integer b) -> SmartEntry
        {
            return innards::UnaryValueEntry{a, b, innards::ConstraintType::EQUAL};
        }

        [[nodiscard]] static inline auto not_equals(const IntegerVariableID & a, const IntegerVariableID & b) -> SmartEntry
        {
            return innards::BinaryEntry{a, b, innards::ConstraintType::NOT_EQUAL};
        }

        [[nodiscard]] static inline auto not_equals(const IntegerVariableID & a, Integer b) -> SmartEntry
        {
            return innards::UnaryValueEntry{a, b, innards::ConstraintType::NOT_EQUAL};
        }

        [[nodiscard]] static inline auto greater_than_equal(const IntegerVariableID & a, const IntegerVariableID & b) -> SmartEntry
        {
            return innards::BinaryEntry{a, b, innards::ConstraintType::GREATER_THAN_EQUAL};
        }

        [[nodiscard]] static inline auto greater_than_equal(const IntegerVariableID & a, Integer b) -> SmartEntry
        {
            return innards::UnaryValueEntry{a, b, innards::ConstraintType::GREATER_THAN_EQUAL};
        }

        [[nodiscard]] static inline auto greater_than(const IntegerVariableID & a, const IntegerVariableID & b) -> SmartEntry
        {
            return innards::BinaryEntry{a, b, innards::ConstraintType::GREATER_THAN};
        }

        [[nodiscard]] static inline auto greater_than(const IntegerVariableID & a, Integer b) -> SmartEntry
        {
            return innards::UnaryValueEntry{a, b, innards::ConstraintType::GREATER_THAN};
        }

        [[nodiscard]] static inline auto less_than_equal(const IntegerVariableID & a, const IntegerVariableID & b) -> SmartEntry
        {
            return innards::BinaryEntry{a, b, innards::ConstraintType::LESS_THAN_EQUAL};
        }

        [[nodiscard]] static inline auto less_than_equal(const IntegerVariableID & a, Integer b) -> SmartEntry
        {
            return innards::UnaryValueEntry{a, b, innards::ConstraintType::LESS_THAN_EQUAL};
        }

        [[nodiscard]] static inline auto less_than(const IntegerVariableID & a, const IntegerVariableID & b) -> SmartEntry
        {
            return innards::BinaryEntry{a, b, innards::ConstraintType::LESS_THAN};
        }

        [[nodiscard]] static inline auto less_than(const IntegerVariableID & a, Integer b) -> SmartEntry
        {
            return innards::UnaryValueEntry{a, b, innards::ConstraintType::LESS_THAN};
        }

        [[nodiscard]] static inline auto in_set(const IntegerVariableID & a, std::vector<Integer> b) -> SmartEntry
        {
            return innards::UnarySetEntry{a, move(b), innards::ConstraintType::IN};
        }

        [[nodiscard]] static inline auto not_in_set(const IntegerVariableID & a, std::vector<Integer> b) -> SmartEntry
        {
            return innards::UnarySetEntry{a, move(b), innards::ConstraintType::NOT_IN};
        }
    };
}

#endif // GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_SMART_TABLE_HH
