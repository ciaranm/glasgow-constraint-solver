#ifndef GLASGOW_CONSTRAINT_SOLVER_GUARD_UTIL_STRINGIFY_TUPLE_HH
#define GLASGOW_CONSTRAINT_SOLVER_GUARD_UTIL_STRINGIFY_TUPLE_HH

#include <tuple>
#include <utility>

namespace gcs
{
    template <typename T_, size_t... i_>
    [[nodiscard]] auto stringify_tuple(const T_ & t, std::index_sequence<i_...>) -> std::string
    {
        std::string result = "(";
        (..., (result.append(i_ == 0 ? "" : ", ").append(std::to_string(std::get<i_>(t)))));
        result.append(")");
        return result;
    }

    template <typename... T_>
    [[nodiscard]] auto stringify_tuple(const std::tuple<T_...> & t) -> std::string
    {
        return stringify_tuple(t, std::make_index_sequence<sizeof...(T_)>());
    }

    template <typename P_, typename Q_>
    [[nodiscard]] auto stringify_tuple(const std::pair<P_, Q_> & t) -> std::string
    {
        return stringify_tuple(t, std::make_index_sequence<2>());
    }
}

#endif
