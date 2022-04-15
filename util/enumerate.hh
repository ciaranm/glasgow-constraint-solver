/* vim: set sw=4 sts=4 et foldmethod=syntax : */

#ifndef GLASGOW_CONSTRAINT_SOLVER_GUARD_UTIL_ENUMERATE_HH
#define GLASGOW_CONSTRAINT_SOLVER_GUARD_UTIL_ENUMERATE_HH

#include <iterator>
#include <tuple>
#include <utility>

namespace gcs
{
    template <typename Range_>
    auto enumerate(Range_ && range)
    {
        using Iterator_ = decltype(std::begin(range));

        struct EnumerateIterator
        {
            std::size_t index;
            Iterator_ iterator;

            auto operator++() -> EnumerateIterator
            {
                ++index;
                ++iterator;
                return *this;
            }

            auto operator!=(const EnumerateIterator & other) const -> bool
            {
                return iterator != other.iterator;
            }

            auto operator*() const
            {
                return std::tie(index, *iterator);
            }
        };

        struct Enumerate
        {
            Range_ range;

            auto begin() -> EnumerateIterator
            {
                return EnumerateIterator{0, std::begin(range)};
            }

            auto end() -> EnumerateIterator
            {
                return EnumerateIterator{0, std::end(range)};
            }
        };

        return Enumerate(std::forward<Range_>(range));
    }
}

#endif
