/* vim: set sw=4 sts=4 et foldmethod=syntax : */

#ifndef GLASGOW_CONSTRAINT_SOLVER_GUARD_UTIL_GENERALISE_HH
#define GLASGOW_CONSTRAINT_SOLVER_GUARD_UTIL_GENERALISE_HH 1

#include <variant>

namespace gcs
{
    template <typename T_, typename A_>
    auto inline generalise(A_ & a) -> T_
    {
        return std::visit([](auto & x) -> T_ { return x; }, a);
    }
}

#endif
