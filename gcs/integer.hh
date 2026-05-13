#ifndef GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_INTEGER_HH
#define GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_INTEGER_HH

#include <gcs/innards/integer_overflow.hh>

#include <cstddef>
#include <cstdlib>
#include <functional>
#include <limits>
#include <ostream>
#include <string>
#include <version>

#if defined(__cpp_lib_print) && defined(__cpp_lib_format)
#include <format>
#else
#include <fmt/core.h>
#endif

namespace gcs
{
    /**
     * \defgroup IntegerWrapper Type-safe integer wrapper
     */

    /**
     * \brief Wrapper class around integer values, for type safety.
     *
     * Use gcs::operator""_i to create a literal, for example 42_i.
     *
     * Integer has arithmetic and comparison operations that are defined as you
     * would expect.
     *
     * \ingroup Core
     * \ingroup IntegerWrapper
     */
    struct Integer final
    {
        long long raw_value;

        explicit constexpr Integer(long long v) :
            raw_value(v)
        {
        }

        [[nodiscard]] auto to_string() const -> std::string
        {
            return std::to_string(raw_value);
        }

        /**
         * \brief Convert to a std::size_t for use as a 0-based container index.
         *
         * Use in preference to .raw_value when subscripting a vector / bitset /
         * std::ranges::views::drop / .at(): it documents intent and acts as a
         * grep-able sentinel for "this Integer is being used as an index, not as
         * generic numeric data". Behaviour is undefined if the value is negative.
         */
        [[nodiscard]] constexpr auto as_index() const noexcept -> std::size_t
        {
            return static_cast<std::size_t>(raw_value);
        }

        ///@{
        /**
         * Standard arithmetic, comparison, and related operations for Integer.
         */

        [[nodiscard]] constexpr auto operator<=>(const Integer &) const = default;

        constexpr auto operator++() -> Integer &
        {
            if (raw_value == std::numeric_limits<long long>::max())
                innards::throw_integer_overflow("++", raw_value);
            ++raw_value;
            return *this;
        }

        constexpr auto operator++(int) -> Integer
        {
            Integer old = *this;
            operator++();
            return old;
        }

        constexpr auto operator--() -> Integer &
        {
            if (raw_value == std::numeric_limits<long long>::min())
                innards::throw_integer_overflow("--", raw_value);
            --raw_value;
            return *this;
        }

        constexpr auto operator--(int) -> Integer
        {
            Integer old = *this;
            operator--();
            return old;
        }

        ///@}

        static inline constexpr auto min_value() -> const Integer
        {
            return Integer(std::numeric_limits<decltype(raw_value)>::min());
        }

        static inline constexpr auto max_value() -> const Integer
        {
            return Integer(std::numeric_limits<decltype(raw_value)>::max());
        }
    };

    ///@{
    /**
     * \name Standard arithmetic, comparison, and related operations for Integer.
     *
     * \ingroup IntegerWrapper
     * \sa Integer
     */

    [[nodiscard]] constexpr inline auto operator+(Integer a, Integer b) -> Integer
    {
        long long r;
        if (__builtin_add_overflow(a.raw_value, b.raw_value, &r))
            innards::throw_integer_overflow("+", a.raw_value, b.raw_value);
        return Integer{r};
    }

    constexpr inline auto operator+=(Integer & a, Integer b) -> Integer &
    {
        if (__builtin_add_overflow(a.raw_value, b.raw_value, &a.raw_value))
            innards::throw_integer_overflow("+=", a.raw_value, b.raw_value);
        return a;
    }

    [[nodiscard]] constexpr inline auto operator-(Integer a, Integer b) -> Integer
    {
        long long r;
        if (__builtin_sub_overflow(a.raw_value, b.raw_value, &r))
            innards::throw_integer_overflow("-", a.raw_value, b.raw_value);
        return Integer{r};
    }

    constexpr inline auto operator-=(Integer & a, Integer b) -> Integer &
    {
        if (__builtin_sub_overflow(a.raw_value, b.raw_value, &a.raw_value))
            innards::throw_integer_overflow("-=", a.raw_value, b.raw_value);
        return a;
    }

    [[nodiscard]] constexpr inline auto operator*(Integer a, Integer b) -> Integer
    {
        long long r;
        if (__builtin_mul_overflow(a.raw_value, b.raw_value, &r))
            innards::throw_integer_overflow("*", a.raw_value, b.raw_value);
        return Integer{r};
    }

    [[nodiscard]] constexpr inline auto operator/(Integer a, Integer b) -> Integer
    {
        if (b.raw_value == 0)
            innards::throw_integer_overflow("/", a.raw_value, b.raw_value);
        if (a.raw_value == std::numeric_limits<long long>::min() && b.raw_value == -1)
            innards::throw_integer_overflow("/", a.raw_value, b.raw_value);
        return Integer{a.raw_value / b.raw_value};
    }

    [[nodiscard]] constexpr inline auto operator%(Integer a, Integer b) -> Integer
    {
        if (b.raw_value == 0)
            innards::throw_integer_overflow("%", a.raw_value, b.raw_value);
        if (a.raw_value == std::numeric_limits<long long>::min() && b.raw_value == -1)
            innards::throw_integer_overflow("%", a.raw_value, b.raw_value);
        return Integer{a.raw_value % b.raw_value};
    }

    [[nodiscard]] constexpr inline auto operator-(Integer a) -> Integer
    {
        if (a.raw_value == std::numeric_limits<long long>::min())
            innards::throw_integer_overflow("-", a.raw_value);
        return Integer{-a.raw_value};
    }

    ///@}

    /**
     * \brief An Integer can be written to an ostream.
     *
     * \ingroup IntegerWrapper
     */
    inline auto operator<<(std::ostream & s, Integer i) -> std::ostream &
    {
        return s << i.raw_value;
    }

    /**
     * \brief An Integer can be used with libfmt (via ADL) and std::format (via std::formatter specialisation).
     *
     * \ingroup IntegerWrapper
     */
    constexpr inline auto format_as(Integer i) -> long long
    {
        return i.raw_value;
    }

    /**
     * \brief Absolute value of an Integer.
     *
     * \ingroup IntegerWrapper
     */
    inline auto abs(Integer i) -> Integer
    {
        if (i.raw_value == std::numeric_limits<long long>::min())
            innards::throw_integer_overflow("abs", i.raw_value);
        return Integer{std::llabs(i.raw_value)};
    }

    /**
     * \brief Create an Integer from a literal.
     *
     * \ingroup IntegerWrapper
     */
    [[nodiscard]] constexpr inline auto operator""_i(unsigned long long v) -> Integer
    {
        return Integer(v);
    }
}

#if defined(__cpp_lib_format) && defined(__cpp_lib_print)
template <>
struct std::formatter<gcs::Integer> : std::formatter<long long> {
    template <typename FormatContext_>
    auto format(gcs::Integer i, FormatContext_ & ctx) const
    {
        return std::formatter<long long>::format(i.raw_value, ctx);
    }
};
#endif

template <>
struct std::hash<gcs::Integer>
{
    [[nodiscard]] inline auto operator()(const gcs::Integer & v) const noexcept -> std::size_t
    {
        return hash<long long>{}(v.raw_value);
    }
};

#endif
