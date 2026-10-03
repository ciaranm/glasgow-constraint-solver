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

        explicit constexpr Integer(long long v) : raw_value(v)
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

        static inline constexpr auto min_value() -> Integer
        {
            return Integer(std::numeric_limits<decltype(raw_value)>::min());
        }

        static inline constexpr auto max_value() -> Integer
        {
            return Integer(std::numeric_limits<decltype(raw_value)>::max());
        }

        /**
         * \name The range every input to the solver must lie in.
         *
         * A variable's declared domain, a constant, a view's offset, and every
         * Integer a constraint takes as a parameter (a coefficient, a tuple
         * value, a distance, and so on) must lie within these. An input outside
         * them throws IntegerOverflow, as early as possible: domains, constants
         * and views check it themselves, and constraints check their
         * parameters when they are constructed. See dev_docs/integer-ranges.md.
         *
         * The range is an eighth of the machine range, three bits of headroom,
         * and symmetric, so that negating an input never leaves it: maximising
         * `x + c` negates `c`, which the caller never sees.
         * Two of those are what writing the proof model costs: a half-reified
         * row's reification constant is the sum of the positive contributions
         * of *every* term, so a row relating two variables needs room for both,
         * and that constant is then negated when the row is rendered in `>=`
         * form -- and the most negative machine integer has no negation. At a
         * quarter of the machine range `LessThan`, `Plus` and `AllDifferent`
         * all write their model, and at a half all three abort part-way through
         * (issue #852). The third bit is for views: since a view's offset lies
         * in this range too, a view's values can reach twice as far as a
         * variable's, and a row over two views at that reach needs the extra
         * bit, measured on `LessThan`, `AllDifferent` and `Lex`.
         *
         * Arithmetic is deliberately *not* held to this: intermediate results
         * are expected to exceed it, which is what the headroom is for. Where a
         * constraint's own arithmetic over in-range inputs cannot fit in an
         * Integer, as a product of two wide variables can't, it throws
         * IntegerOverflow rather than answering wrongly.
         */
        ///@{
        static inline constexpr auto min_bounded_value() -> Integer
        {
            return Integer(-(std::numeric_limits<decltype(raw_value)>::max() / 8));
        }

        static inline constexpr auto max_bounded_value() -> Integer
        {
            return Integer(std::numeric_limits<decltype(raw_value)>::max() / 8);
        }
        ///@}

        /**
         * \name The widest domain an auxiliary variable may have.
         *
         * A constraint sometimes needs a variable of its own over the values of
         * a view, and a view can reach twice as far as a declared variable. So
         * an auxiliary may span a quarter of the machine range, enough for any
         * view's values and for a magnitude sized to their bit width. That is
         * where the declared range itself used to sit, and is the same reach a
         * view's own proof bit vector has. Problem refuses a declared domain
         * outside min_bounded_value() .. max_bounded_value(); State refuses any
         * domain, declared or auxiliary, outside these.
         */
        ///@{
        static inline constexpr auto min_auxiliary_value() -> Integer
        {
            return Integer(-(std::numeric_limits<decltype(raw_value)>::max() / 4));
        }

        static inline constexpr auto max_auxiliary_value() -> Integer
        {
            return Integer(std::numeric_limits<decltype(raw_value)>::max() / 4);
        }
        ///@}
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
        if (innards::add_overflows(a.raw_value, b.raw_value, &r))
            innards::throw_integer_overflow("+", a.raw_value, b.raw_value);
        return Integer{r};
    }

    constexpr inline auto operator+=(Integer & a, Integer b) -> Integer &
    {
        // Into a local rather than straight into a: on overflow the builtin stores
        // the wrapped result, which the message would then report as the left
        // operand, and which would be left in a (issue #1003).
        long long r;
        if (innards::add_overflows(a.raw_value, b.raw_value, &r))
            innards::throw_integer_overflow("+=", a.raw_value, b.raw_value);
        a.raw_value = r;
        return a;
    }

    [[nodiscard]] constexpr inline auto operator-(Integer a, Integer b) -> Integer
    {
        long long r;
        if (innards::sub_overflows(a.raw_value, b.raw_value, &r))
            innards::throw_integer_overflow("-", a.raw_value, b.raw_value);
        return Integer{r};
    }

    constexpr inline auto operator-=(Integer & a, Integer b) -> Integer &
    {
        // Into a local rather than straight into a, as for +=.
        long long r;
        if (innards::sub_overflows(a.raw_value, b.raw_value, &r))
            innards::throw_integer_overflow("-=", a.raw_value, b.raw_value);
        a.raw_value = r;
        return a;
    }

    [[nodiscard]] constexpr inline auto operator*(Integer a, Integer b) -> Integer
    {
        long long r;
        if (innards::mul_overflows(a.raw_value, b.raw_value, &r))
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

    namespace innards
    {
        /**
         * \brief Return \a v, or throw IntegerOverflow if it lies outside
         * Integer::min_bounded_value() .. Integer::max_bounded_value(), the
         * range every input to the solver must lie in. \a what names the
         * input in the message, for example "a view's offset".
         *
         * \ingroup IntegerWrapper
         */
        constexpr inline auto require_bounded(Integer v, const char * what) -> Integer
        {
            if (v < Integer::min_bounded_value() || v > Integer::max_bounded_value())
                throw_outside_bounded_range(what, v.raw_value);
            return v;
        }
    }
}

#if defined(__cpp_lib_format) && defined(__cpp_lib_print)
template <>
struct std::formatter<gcs::Integer> : std::formatter<long long>
{
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
