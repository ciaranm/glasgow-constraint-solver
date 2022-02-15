/* vim: set sw=4 sts=4 et foldmethod=syntax : */

#ifndef GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_INTEGER_HH
#define GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_INTEGER_HH

#include <ostream>
#include <string>

namespace gcs
{
    struct Integer
    {
        long long raw_value;

        explicit Integer(long long v) :
            raw_value(v)
        {
        }

        [[nodiscard]] auto to_string() const -> std::string
        {
            return std::to_string(raw_value);
        }

        [[nodiscard]] auto operator<=>(const Integer &) const = default;

        auto operator++() -> Integer &
        {
            ++raw_value;
            return *this;
        }

        auto operator++(int) -> Integer
        {
            Integer old = *this;
            operator++();
            return old;
        }

        auto operator--() -> Integer &
        {
            --raw_value;
            return *this;
        }

        auto operator--(int) -> Integer
        {
            Integer old = *this;
            operator--();
            return old;
        }
    };

    [[nodiscard]] inline auto operator+(Integer a, Integer b) -> Integer
    {
        return Integer{a.raw_value + b.raw_value};
    }

    inline auto operator+=(Integer & a, Integer b) -> Integer &
    {
        a.raw_value += b.raw_value;
        return a;
    }

    [[nodiscard]] inline auto operator-(Integer a, Integer b) -> Integer
    {
        return Integer{a.raw_value - b.raw_value};
    }

    inline auto operator-=(Integer & a, Integer b) -> Integer &
    {
        a.raw_value -= b.raw_value;
        return a;
    }

    [[nodiscard]] inline auto operator*(Integer a, Integer b) -> Integer
    {
        return Integer{a.raw_value * b.raw_value};
    }

    [[nodiscard]] inline auto operator/(Integer a, Integer b) -> Integer
    {
        return Integer{a.raw_value / b.raw_value};
    }

    [[nodiscard]] inline auto operator%(Integer a, Integer b) -> Integer
    {
        return Integer{a.raw_value % b.raw_value};
    }

    [[nodiscard]] inline auto operator-(Integer a) -> Integer
    {
        return Integer{-a.raw_value};
    }

    [[nodiscard]] inline auto operator"" _i(unsigned long long v) -> Integer
    {
        return Integer(v);
    }

    inline auto operator<<(std::ostream & s, Integer i) -> std::ostream &
    {
        return s << i.raw_value;
    }

    inline auto abs(Integer i) -> Integer
    {
        return Integer{std::llabs(i.raw_value)};
    }
}

#endif
