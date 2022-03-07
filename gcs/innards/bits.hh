/* vim: set sw=4 sts=4 et foldmethod=syntax : */

#ifndef GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_BITS_HH
#define GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_BITS_HH

#include <algorithm>
#include <bit>
#include <limits>

namespace gcs::innards
{
    /**
     * \brief A fixed size bitset.
     *
     * \ingroup Innards
     */
    struct Bits
    {
        using BitWord = unsigned long long;

        static const constexpr int n_words = 2;

        static const constexpr int bits_per_word = std::numeric_limits<BitWord>::digits;

        static constexpr int number_of_bits = bits_per_word * n_words;

        BitWord data[n_words];

        explicit Bits()
        {
            std::fill(data, data + n_words, 0);
        }

        [[nodiscard]] auto popcount() const -> int
        {
            return std::popcount(data[0]) + std::popcount(data[1]);
        }

        [[nodiscard]] auto has_single_bit() const -> bool
        {
            return 1 == popcount();
        }

        [[nodiscard]] auto countr_zero() const -> int
        {
            int r = std::countr_zero(data[0]);
            if (r == bits_per_word)
                r += std::countr_zero(data[1]);
            return r;
        }

        [[nodiscard]] auto countl_zero() const -> int
        {
            int r = std::countl_zero(data[1]);
            if (r == bits_per_word)
                r += std::countl_zero(data[0]);
            return r;
        }

        [[nodiscard]] auto test(int a) const -> bool
        {
            return data[a / bits_per_word] & (BitWord{1} << (a % bits_per_word));
        }

        auto set(int a) -> void
        {
            data[a / bits_per_word] |= (BitWord{1} << (a % bits_per_word));
        }

        auto reset(int a) -> void
        {
            data[a / bits_per_word] &= ~(BitWord{1} << (a % bits_per_word));
        }

        [[nodiscard]] auto none() const -> bool
        {
            return (0ull == data[0]) && (0ull == data[1]);
        }
    };
}

#endif
