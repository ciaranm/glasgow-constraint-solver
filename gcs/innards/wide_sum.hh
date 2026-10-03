#ifndef GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_INNARDS_WIDE_SUM_HH
#define GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_INNARDS_WIDE_SUM_HH

#include <gcs/innards/integer_overflow.hh>
#include <gcs/integer.hh>

#include <compare>
#include <limits>
#include <optional>
#include <string>

namespace gcs::innards
{
    /**
     * \brief An exact sum of Integers, held in 128 bits so that the order the
     * terms arrive in cannot make it overflow.
     *
     * Summing in an Integer throws as soon as a partial sum leaves the machine
     * range, even when the terms still to come bring it back: nine terms at the
     * top of the bounded range and nine at the bottom sum to zero, but not in
     * that order. This accumulates exactly instead, and narrow() reports
     * whether the *total* fits. It is two's complement over two unsigned words,
     * rather than __int128, which MSVC lacks; it cannot itself overflow before
     * 2^63 additions.
     *
     * See dev_docs/integer-ranges.md: a sum a constraint genuinely needs that
     * does not fit is still an IntegerOverflow, from narrow_or_throw().
     *
     * \ingroup Innards
     */
    class WideSum
    {
    private:
        unsigned long long _lo = 0, _hi = 0;

        static constexpr auto sign_word(Integer v) -> unsigned long long
        {
            return v.raw_value < 0 ? ~0ULL : 0ULL;
        }

    public:
        constexpr WideSum() = default;

        constexpr explicit WideSum(Integer v) : _lo(static_cast<unsigned long long>(v.raw_value)), _hi(sign_word(v))
        {
        }

        constexpr auto operator+=(Integer v) -> WideSum &
        {
            return *this += WideSum{v};
        }

        constexpr auto operator-=(Integer v) -> WideSum &
        {
            return *this += -WideSum{v};
        }

        constexpr auto operator+=(const WideSum & other) -> WideSum &
        {
            auto old = _lo;
            _lo += other._lo;
            _hi += other._hi + (_lo < old ? 1ULL : 0ULL);
            return *this;
        }

        constexpr auto operator-=(const WideSum & other) -> WideSum &
        {
            return *this += -other;
        }

        [[nodiscard]] constexpr auto operator-() const -> WideSum
        {
            WideSum result;
            result._lo = ~_lo + 1ULL;
            result._hi = ~_hi + (result._lo == 0ULL ? 1ULL : 0ULL);
            return result;
        }

        [[nodiscard]] friend constexpr auto operator+(WideSum a, const WideSum & b) -> WideSum
        {
            return a += b;
        }

        [[nodiscard]] friend constexpr auto operator+(WideSum a, Integer b) -> WideSum
        {
            return a += b;
        }

        [[nodiscard]] friend constexpr auto operator-(WideSum a, const WideSum & b) -> WideSum
        {
            return a -= b;
        }

        [[nodiscard]] friend constexpr auto operator-(WideSum a, Integer b) -> WideSum
        {
            return a -= b;
        }

        [[nodiscard]] friend constexpr auto operator<=>(const WideSum & a, const WideSum & b) -> std::strong_ordering
        {
            // The high words compare as signed, the low words as unsigned.
            if (auto c = static_cast<long long>(a._hi) <=> static_cast<long long>(b._hi); c != 0)
                return c;
            return a._lo <=> b._lo;
        }

        [[nodiscard]] friend constexpr auto operator==(const WideSum & a, const WideSum & b) -> bool = default;

        [[nodiscard]] friend constexpr auto operator<=>(const WideSum & a, Integer b) -> std::strong_ordering
        {
            return a <=> WideSum{b};
        }

        [[nodiscard]] friend constexpr auto operator==(const WideSum & a, Integer b) -> bool
        {
            return a == WideSum{b};
        }

        /// The total divided by \a divisor, if that divides it exactly and the
        /// quotient fits in an Integer. For solving `divisor * x = total` for an
        /// x that must be an Integer: a total past Integer's range can still have
        /// one, when the divisor is large. A total that fits takes the native
        /// operations; one that does not, bitwise long division.
        [[nodiscard]] constexpr auto divided_exactly_by(Integer divisor) const -> std::optional<Integer>
        {
            if (divisor == Integer{0})
                return std::nullopt;
            if (auto total = narrow()) {
                // The one native quotient that does not fit.
                if (*total == Integer::min_value() && divisor == Integer{-1})
                    return std::nullopt;
                if (*total % divisor != Integer{0})
                    return std::nullopt;
                return *total / divisor;
            }
            bool negative_total = static_cast<long long>(_hi) < 0;
            auto magnitude = negative_total ? -*this : *this;
            // Two's complement magnitude of the divisor, safe for the most
            // negative Integer.
            auto d = divisor.raw_value < 0 ? ~static_cast<unsigned long long>(divisor.raw_value) + 1ULL
                                           : static_cast<unsigned long long>(divisor.raw_value);
            unsigned long long remainder = 0, q_lo = 0, q_hi = 0;
            for (int bit = 127; bit >= 0; --bit) {
                auto word = bit >= 64 ? magnitude._hi : magnitude._lo;
                auto next = (word >> (bit % 64)) & 1ULL;
                // remainder < d <= 2^63, so this cannot wrap.
                remainder = (remainder << 1) | next;
                if (remainder >= d) {
                    remainder -= d;
                    if (bit >= 64)
                        q_hi |= 1ULL << (bit - 64);
                    else
                        q_lo |= 1ULL << bit;
                }
            }
            if (remainder != 0 || q_hi != 0)
                return std::nullopt;
            WideSum quotient;
            quotient._lo = q_lo;
            if (negative_total != (divisor.raw_value < 0))
                quotient = -quotient;
            return quotient.narrow();
        }

        /// The total, if it fits in an Integer.
        [[nodiscard]] constexpr auto narrow() const -> std::optional<Integer>
        {
            constexpr auto top = static_cast<unsigned long long>(std::numeric_limits<long long>::max());
            if ((_hi == 0ULL && _lo <= top) || (_hi == ~0ULL && _lo > top))
                return Integer{static_cast<long long>(_lo)};
            return std::nullopt;
        }

        /// The total, or IntegerOverflow if it does not fit in an Integer. \a
        /// what names the sum in the message.
        [[nodiscard]] auto narrow_or_throw(const char * what = "a sum") const -> Integer
        {
            if (auto v = narrow())
                return *v;
            throw IntegerOverflow{std::string{what} + " does not fit in an Integer"};
        }
    };
}

#endif
