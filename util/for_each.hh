/* vim: set sw=4 sts=4 et foldmethod=syntax : */

#ifndef GLASGOW_CONSTRAINT_SOLVER_GUARD_UTIL_FOR_EACH_HH
#define GLASGOW_CONSTRAINT_SOLVER_GUARD_UTIL_FOR_EACH_HH 1

#include <iterator>

namespace gcs
{
    template <typename T_, typename F_>
    auto for_each_distinct_pair(T_ & c, F_ f) -> void
    {
        for (auto first = c.begin(), end = c.end(); first != end; ++first)
            for (auto second = std::next(first); second != end; ++second)
                f(*first, *second);
    }

    template <typename T_, typename F_>
    auto for_each_with_index(T_ & c, F_ f) -> void
    {
        typename T_::size_type idx{0};
        auto v = c.begin(), end = c.end();
        for (; v != end; ++idx, ++v)
            f(*v, idx);
    }
}

#endif
