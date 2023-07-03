#ifndef GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_EXPRESSION_HH
#define GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_EXPRESSION_HH

#include <gcs/integer.hh>
#include <gcs/variable_id.hh>

#include <concepts>
#include <iosfwd>
#include <vector>

namespace gcs
{
    /**
     * \defgroup Expressions Lightweight data structures for dealing with sums of weighted terms and similar.
     */

    /**
     * \brief A variable or similar with an associated Integer weight.
     *
     * Often this is created by writing `42_i * var` or similar.
     *
     * \ingroup Expressions
     */
    template <typename Var_>
    struct Weighted final
    {
        Integer coefficient;
        Var_ variable;

        [[nodiscard]] constexpr auto operator<=>(const Weighted<Var_> &) const = default;
    };

    /**
     * \brief Allow `42_i * var` to create a Weighted variable.
     *
     * \ingroup Expressions
     */
    template <typename Var_>
    [[nodiscard]] inline auto operator*(Integer i, Var_ v) -> Weighted<Var_>
    {
        return Weighted<Var_>{i, v};
    }

    /**
     * \brief A `Weighted<Var_>` can be written to a `std::ostream` if its variable can be.
     *
     * \ingroup Expressions
     */
    template <typename Var_>
    auto operator<<(std::ostream & s, const Weighted<Var_> & var) -> std::ostream &
    {
        return s << var.coefficient << "*" << var.variable;
    }

    /**
     * \brief A syntactic sum of terms.
     *
     * Often this is created by writing `42_i * var1 + 23 * var2`.
     *
     * \ingroup Expressions
     */
    template <typename Term_>
    struct SumOf final
    {
        std::vector<Term_> terms;
    };

    /**
     * We can add a term to a SumOf using `+`.
     *
     * \ingroup Expressions
     */
    template <typename Var_, typename Add_>
    [[nodiscard]] inline auto operator+(SumOf<Weighted<Var_>> a, Weighted<Add_> b) -> SumOf<Weighted<Var_>>
    requires std::constructible_from<Var_, Add_>
    {
        a.terms.push_back(Weighted<Var_>{b.coefficient, b.variable});
        return a;
    }

    /**
     * SumOf can be appended to using `+=`.
     *
     * \ingroup Expressions
     */
    template <typename Var_, typename Add_>
    inline auto operator+=(SumOf<Weighted<Var_>> & a, Weighted<Add_> b) -> SumOf<Weighted<Var_>> & requires std::constructible_from<Var_, Add_>
    {
        a.terms.push_back(Weighted<Var_>{b.coefficient, b.variable});
        return a;
    }

    /**
     * A syntactic sum of integer variables multiplied by integer coefficients (that is,
     * a linear expression).
     *
     * \ingroup Expressions
     */
    using WeightedSum = SumOf<Weighted<IntegerVariableID>>;
}

#endif
