#ifndef GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_CONSTRAINTS_INNARDS_PRODUCT_BOUNDS_HH
#define GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_CONSTRAINTS_INNARDS_PRODUCT_BOUNDS_HH

#include <gcs/exception.hh>
#include <gcs/integer.hh>

#include <algorithm>
#include <utility>

namespace gcs::innards
{
    /**
     * \brief Floor division: the largest q with q * b <= a. Unlike operator/,
     * which truncates towards zero, this rounds towards negative infinity.
     *
     * \ingroup Innards
     */
    [[nodiscard]] constexpr auto div_floor(Integer a, Integer b) -> Integer
    {
        return ((a >= 0_i) != (b >= 0_i)) && (a != 0_i) ? (1_i - abs(a)) / abs(b) - 1_i : a / b;
    }

    /**
     * \brief Ceiling division: the smallest q with q * b >= a.
     *
     * \ingroup Innards
     */
    [[nodiscard]] constexpr auto div_ceil(Integer a, Integer b) -> Integer
    {
        return ((a >= 0_i) == (b >= 0_i)) && (a != 0_i) ? (abs(a) - 1_i) / abs(b) + 1_i : a / b;
    }

    /**
     * \brief Floor of the square root of a non-negative value.
     *
     * \ingroup Innards
     */
    [[nodiscard]] constexpr auto isqrt(Integer n) -> Integer
    {
        if (n < 0_i)
            throw UnexpectedException{"isqrt of negative value"};
        if (n < 2_i)
            return n;
        // Newton's method on integers: converges for any positive start >= isqrt(n).
        auto x = n, y = (x + 1_i) / 2_i;
        while (y < x) {
            x = y;
            y = (x + n / x) / 2_i;
        }
        return x;
    }

    /**
     * \brief Ceiling of the square root of a non-negative value.
     *
     * \ingroup Innards
     */
    [[nodiscard]] constexpr auto ceil_isqrt(Integer n) -> Integer
    {
        auto r = isqrt(n);
        return r * r == n ? r : r + 1_i;
    }

    /**
     * \brief Bounds of x * y over the box [x_min, x_max] * [y_min, y_max]:
     * the smallest and largest corner products.
     *
     * \ingroup Innards
     */
    [[nodiscard]] constexpr auto product_bounds(Integer x_min, Integer x_max, Integer y_min, Integer y_max) -> std::pair<Integer, Integer>
    {
        auto x1y1 = x_min * y_min;
        auto x2y1 = x_max * y_min;
        auto x1y2 = x_min * y_max;
        auto x2y2 = x_max * y_max;
        return {std::min({x1y1, x1y2, x2y1, x2y2}), std::max({x1y1, x1y2, x2y1, x2y2})};
    }

    /**
     * \brief Exact bounds of x * x for x in [lo, hi]. Unlike product_bounds
     * on the same interval twice, the result is never negative.
     *
     * \ingroup Innards
     */
    [[nodiscard]] constexpr auto square_bounds(Integer lo, Integer hi) -> std::pair<Integer, Integer>
    {
        auto lo2 = lo * lo, hi2 = hi * hi;
        if (lo <= 0_i && 0_i <= hi)
            return {0_i, std::max(lo2, hi2)};
        return {std::min(lo2, hi2), std::max(lo2, hi2)};
    }

    /**
     * \brief The hull of { x in [x_lo, x_hi] : x * x in [z_lo, z_hi] }. May
     * return an empty interval (first > second) if no value is supported.
     *
     * \ingroup Innards
     */
    [[nodiscard]] constexpr auto square_filter(Integer x_lo, Integer x_hi, Integer z_lo, Integer z_hi) -> std::pair<Integer, Integer>
    {
        if (z_hi < 0_i)
            return {1_i, 0_i};
        // x * x <= z_hi iff |x| <= u, and x * x >= z_lo iff |x| >= m, so the
        // supported set is [x_lo, x_hi] intersect ([-u, -m] union [m, u]).
        auto u = isqrt(z_hi);
        auto lo = std::max(x_lo, -u), hi = std::min(x_hi, u);
        if (z_lo > 0_i) {
            auto m = ceil_isqrt(z_lo);
            if (lo > -m)
                lo = std::max(lo, m);
            if (hi < m)
                hi = std::min(hi, -m);
        }
        return {lo, hi};
    }

    /**
     * \brief Outcome of quotient filtering: what bounds (if any) the box of y
     * and z imposes on x in x * y = z.
     *
     * \ingroup Innards
     */
    struct QuotientFilter
    {
        enum class Kind
        {
            NoFilter,          ///< zero is in the bounds of both y and z, any x works
            EmptyBecauseYZero, ///< y is fixed to zero but z excludes zero: no x works
            Bounds,            ///< x is bounded (possibly first > second, meaning empty)
        };

        Kind kind;
        Integer lo{0_i};
        Integer hi{0_i};
    };

    /**
     * \brief Filter x in x * y = z from the bounds of y and z. This is based
     * on the case breakdown in JaCoP:
     * https://github.com/radsz/jacop/blob/develop/src/main/java/org/jacop/core/IntDomain.java#L1377
     *
     * The result is sound but not exact: in the sign-fixed-y case the corner
     * quotients can leave an unsupported endpoint, and in the y-spans-zero
     * case only the symmetric magnitude bound is derived.
     *
     * \ingroup Innards
     */
    [[nodiscard]] constexpr auto quotient_filter(Integer y_min, Integer y_max, Integer z_min, Integer z_max) -> QuotientFilter
    {
        using Kind = QuotientFilter::Kind;

        if (z_min <= 0_i && z_max >= 0_i && y_min <= 0_i && y_max >= 0_i) {
            // 0 is in the bounds of both y and z so no filtering possible
            return {Kind::NoFilter};
        }
        else if (y_min == 0_i && y_max == 0_i) {
            // y == 0 and 0 not in bounds of z => no possible values for x
            return {Kind::EmptyBecauseYZero};
        }
        else if (y_min < 0_i && y_max > 0_i) {
            // y contains -1, 0, 1 and z has either all positive or all negative values
            auto largest = std::max(abs(z_min), abs(z_max));
            return {Kind::Bounds, -largest, largest};
        }
        else {
            // y is zero-or-sign-fixed: drop a zero endpoint, then take quotient corners
            if (y_min == 0_i)
                y_min = 1_i;
            else if (y_max == 0_i)
                y_max = -1_i;
            auto smallest = std::min({div_ceil(z_min, y_min), div_ceil(z_min, y_max), div_ceil(z_max, y_min), div_ceil(z_max, y_max)});
            auto largest = std::max({div_floor(z_min, y_min), div_floor(z_min, y_max), div_floor(z_max, y_min), div_floor(z_max, y_max)});
            return {Kind::Bounds, smallest, largest};
        }
    }
}

#endif
