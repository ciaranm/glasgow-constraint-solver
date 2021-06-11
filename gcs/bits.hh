/* vim: set sw=4 sts=4 et foldmethod=syntax : */

#ifndef GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_BITS_HH
#define GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_BITS_HH 1

#include <bit>
#include <limits>

namespace gcs
{
    struct Bits
    {
        unsigned long long raw_value;

        static constexpr int number_of_bits = std::numeric_limits<decltype(raw_value)>::digits;

        explicit Bits(unsigned long long v) :
            raw_value(v)
        {
        }

        [[ nodiscard ]] auto popcount() const -> int
        {
            return std::popcount(raw_value);
        }

        [[ nodiscard ]] auto has_single_bit() const -> bool
        {
            return std::has_single_bit(raw_value);
        }

        [[ nodiscard ]] auto countr_zero() const -> int
        {
            return std::countr_zero(raw_value);
        }

        [[ nodiscard ]] auto countl_zero() const -> int
        {
            return std::countl_zero(raw_value);
        }

        [[ nodiscard ]] auto test(int idx) const -> bool
        {
            return raw_value & (1ull << idx);
        }

        auto set(int idx) -> void
        {
            raw_value |= (1ull << idx);
        }

        auto reset(int idx) -> void
        {
            raw_value &= ~(1ull << idx);
        }

        [[ nodiscard ]] auto none() const -> bool
        {
            return 0ull == raw_value;
        }
    };
}

#endif
