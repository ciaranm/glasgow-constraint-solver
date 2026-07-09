#ifndef GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_INNARDS_INTEGER_OVERFLOW_HH
#define GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_INNARDS_INTEGER_OVERFLOW_HH

#include <gcs/exception.hh>

#include <limits>
#include <type_traits>

namespace gcs::innards
{
    /**
     * \brief Thrown when an Integer arithmetic operation would overflow,
     * divide by zero, or otherwise produce an undefined result.
     */
    class IntegerOverflow : public UnexpectedException
    {
    public:
        IntegerOverflow(const char * op, long long a, long long b);
        IntegerOverflow(const char * op, long long a);
    };

    [[noreturn]] auto throw_integer_overflow(const char * op, long long a, long long b) -> void;
    [[noreturn]] auto throw_integer_overflow(const char * op, long long a) -> void;

    // Portable checked arithmetic. Each of these mirrors the semantics of the
    // GCC / Clang __builtin_{add,sub,mul}_overflow builtins: the function
    // returns true if the operation overflows the range of Int_, and otherwise
    // stores the mathematically-correct result in *out and returns false. On
    // GCC and Clang they forward to the builtins; MSVC has no equivalent, so a
    // branch-based checked fallback is used there. The fallback is written to be
    // free of any signed overflow (which would itself be undefined behaviour):
    // every intermediate is proven in range before it is computed.
#if defined(__has_builtin)
#define GCS_HAS_BUILTIN(x) __has_builtin(x)
#else
#define GCS_HAS_BUILTIN(x) 0
#endif

    template <typename Int_>
    [[nodiscard]] constexpr auto add_overflows(Int_ a, Int_ b, Int_ * out) -> bool
    {
        static_assert(std::is_integral_v<Int_>);
#if GCS_HAS_BUILTIN(__builtin_add_overflow)
        return __builtin_add_overflow(a, b, out);
#else
        constexpr auto max = std::numeric_limits<Int_>::max();
        constexpr auto min = std::numeric_limits<Int_>::min();
        if (b >= Int_{0}) {
            if (a > max - b)
                return true;
        }
        else if (a < min - b)
            return true;
        *out = static_cast<Int_>(a + b);
        return false;
#endif
    }

    template <typename Int_>
    [[nodiscard]] constexpr auto sub_overflows(Int_ a, Int_ b, Int_ * out) -> bool
    {
        static_assert(std::is_integral_v<Int_>);
#if GCS_HAS_BUILTIN(__builtin_sub_overflow)
        return __builtin_sub_overflow(a, b, out);
#else
        constexpr auto max = std::numeric_limits<Int_>::max();
        constexpr auto min = std::numeric_limits<Int_>::min();
        if (b >= Int_{0}) {
            if (a < min + b)
                return true;
        }
        else if (a > max + b)
            return true;
        *out = static_cast<Int_>(a - b);
        return false;
#endif
    }

    template <typename Int_>
    [[nodiscard]] constexpr auto mul_overflows(Int_ a, Int_ b, Int_ * out) -> bool
    {
        static_assert(std::is_integral_v<Int_>);
#if GCS_HAS_BUILTIN(__builtin_mul_overflow)
        return __builtin_mul_overflow(a, b, out);
#else
        constexpr auto max = std::numeric_limits<Int_>::max();
        if constexpr (std::is_signed_v<Int_>) {
            constexpr auto min = std::numeric_limits<Int_>::min();
            // Classic CERT INT32-C division-based check: every division below has
            // a non-zero divisor whose sign keeps the quotient in range.
            if (a > Int_{0}) {
                if (b > Int_{0}) {
                    if (a > max / b)
                        return true;
                }
                else if (b < min / a)
                    return true;
            }
            else {
                if (b > Int_{0}) {
                    if (a < min / b)
                        return true;
                }
                else if (a != Int_{0} && b < max / a)
                    return true;
            }
        }
        else if (a != Int_{0} && b > max / a)
            return true;
        *out = static_cast<Int_>(a * b);
        return false;
#endif
    }

#undef GCS_HAS_BUILTIN
}

#endif
