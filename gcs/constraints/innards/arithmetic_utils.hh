#ifndef GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_CONSTRAINTS_INNARDS_ARITHMETIC_UTILS_HH
#define GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_CONSTRAINTS_INNARDS_ARITHMETIC_UTILS_HH

#include <gcs/constraint_id.hh>
#include <gcs/integer.hh>
#include <gcs/variable_id.hh>

#include <util/overloaded.hh>

#include <optional>
#include <string>

namespace gcs::innards
{
    /**
     * \brief A distinct ConstraintID for a child constraint installed by a
     * compound constraint, derived from the parent's identity and a role.
     *
     * Children installed directly (never going through Problem::post) would
     * otherwise all render as `unnamed`, and two children of the same family
     * would then emit colliding `@c[unnamed][role]` OPB labels. NamedConstraint
     * holds a view into a string owned elsewhere, so the built names are
     * interned in a process-lifetime pool (deliberately never freed; the count
     * is bounded by the number of constraints ever posted).
     *
     * \ingroup Innards
     */
    [[nodiscard]] auto child_constraint_id(const ConstraintID & parent, const std::string & role) -> ConstraintID;
    /**
     * \brief An IntegerVariableID, decomposed: v = coeff * var + offset, or
     * just the constant offset if var is absent. Views are affine, and the
     * arithmetic constraints dispatch on this structure.
     *
     * \ingroup Innards
     */
    struct AffineForm
    {
        std::optional<SimpleIntegerVariableID> var;
        Integer coeff{0_i};
        Integer offset{0_i};
    };

    [[nodiscard]] inline auto affine_of(const IntegerVariableID & v) -> AffineForm
    {
        return overloaded{[&](const SimpleIntegerVariableID & s) { return AffineForm{s, 1_i, 0_i}; },
            [&](const ViewOfIntegerVariableID & w) { return AffineForm{w.actual_variable, w.negate_first ? -1_i : 1_i, w.then_add}; },
            [&](const ConstantIntegerVariableID & c) { return AffineForm{std::nullopt, 0_i, c.const_value}; }}
            .visit(v);
    }

    /**
     * \brief a * b without the overflow throw: an overflowing product cannot
     * equal any representable value, so for relation-membership tests it is
     * simply not in the relation.
     *
     * \ingroup Innards
     */
    [[nodiscard]] inline auto product_if_representable(Integer a, Integer b) -> std::optional<Integer>
    {
        long long result;
        if (__builtin_mul_overflow(a.raw_value, b.raw_value, &result))
            return std::nullopt;
        return Integer{result};
    }
}

#endif
