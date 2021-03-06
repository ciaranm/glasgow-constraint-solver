/* vim: set sw=4 sts=4 et foldmethod=syntax : */

#ifndef GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_VARIABLE_ID_HH
#define GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_VARIABLE_ID_HH

#include <gcs/integer.hh>

#include <string>
#include <utility>
#include <variant>

namespace gcs
{
    /**
     * \brief A VariableID corresponding to a genuine, simple integer variable.
     *
     * Usually you can work with IntegerVariableID instead, but some operations
     * specifically require a genuine variable.
     *
     * \sa IntegerVariableID
     * \ingroup Core
     */
    struct SimpleIntegerVariableID
    {
        unsigned long long index;

        explicit SimpleIntegerVariableID(unsigned long long x) :
            index(x)
        {
        }

        [[nodiscard]] auto operator<=>(const SimpleIntegerVariableID &) const = default;
    };

    /**
     * \brief A VariableID corresponding to a SimpleIntegerVariableID, but
     * possibly negated, and possibly with a constant added to its value.
     *
     * Usually this will be constructed using `var + 42_i` or `-var`.
     *
     * \sa IntegerVariableID
     * \ingroup Core
     */
    struct ViewOfIntegerVariableID
    {
        SimpleIntegerVariableID actual_variable;
        bool negate_first;
        Integer then_add;

        explicit ViewOfIntegerVariableID(SimpleIntegerVariableID a, bool n, Integer o) :
            actual_variable(a),
            negate_first(n),
            then_add(o)
        {
        }

        [[nodiscard]] auto operator<=>(const ViewOfIntegerVariableID &) const = default;
    };

    /**
     * \brief A constant value that behaves like an IntegerVariableID.
     *
     * Can be constructed using gcs::operator""_c(), for example `42_c`,
     * or using gcs::constant_variable().  Constants can be used anywhere that
     * an IntegerVariableID is expected, avoiding the need to create a variable
     * that has only a single value.
     *
     * \sa IntegerVariableID
     * \sa gcs::operator""_c()
     * \sa gcs::constant_variable()
     * \ingroup Core
     */
    struct ConstantIntegerVariableID
    {
        Integer const_value;

        explicit ConstantIntegerVariableID(Integer x) :
            const_value(x)
        {
        }

        [[nodiscard]] auto operator<=>(const ConstantIntegerVariableID &) const = default;
    };

    /**
     * An IntegerVariableID can be a SimpleIntegerVariableID, a
     * ViewOfIntegerVariableID, or a ConstantIntegerVariableID.
     *
     * \ingroup Core
     */
    using IntegerVariableID = std::variant<SimpleIntegerVariableID, ViewOfIntegerVariableID, ConstantIntegerVariableID>;

    /**
     * \brief Create an IntegerVariableID for a constant value.
     *
     * \sa IntegerVariableID
     * \sa gcs::operator""_c()
     * \ingroup Core
     */
    [[nodiscard]] inline auto constant_variable(const Integer x) -> IntegerVariableID
    {
        return ConstantIntegerVariableID{x};
    }

    /**
     * \brief Create an IntegerVariableID for a constant literal value.
     *
     * \sa IntegerVariableID
     * \sa gcs::constant_variable()
     * \ingroup Core
     */
    [[nodiscard]] inline auto operator"" _c(unsigned long long v) -> ConstantIntegerVariableID
    {
        return ConstantIntegerVariableID{Integer(v)};
    }

    /**
     * \brief Constants can be negated.
     *
     * \ingroup Core
     * \sa ConstantIntegerVariableID
     */
    [[nodiscard]] inline auto operator-(ConstantIntegerVariableID a) -> ConstantIntegerVariableID
    {
        return ConstantIntegerVariableID{-a.const_value};
    }

    /**
     * \brief Given an IntegerVariableID, produce another IntegerVariableID that
     * is the same except with its value offset by a constant.
     *
     * \ingroup Core
     * \sa IntegerVariableID
     * \sa ViewOfIntegerVariableID
     */
    [[nodiscard]] auto operator+(IntegerVariableID v, Integer offset) -> IntegerVariableID;

    /**
     * \brief Given an IntegerVariableID, produce another IntegerVariableID that
     * is the same except with its value offset by a constant.
     *
     * \ingroup Core
     * \sa IntegerVariableID
     * \sa ViewOfIntegerVariableID
     */
    [[nodiscard]] auto operator-(IntegerVariableID v, Integer offset) -> IntegerVariableID;

    /**
     * \brief Given an IntegerVariableID, produce another IntegerVariableID that
     * is the same except with its value negated.
     *
     * \ingroup Core
     * \sa IntegerVariableID
     * \sa ViewOfIntegerVariableID
     */
    [[nodiscard]] auto operator-(IntegerVariableID v) -> IntegerVariableID;

    /**
     * \brief Currently, we only have integer variables, so a VariableID is an
     * IntegerVariableID.
     *
     * \ingroup Core
     * \sa IntegerVariableID
     */
    using VariableID = std::variant<IntegerVariableID>;
}

#endif
