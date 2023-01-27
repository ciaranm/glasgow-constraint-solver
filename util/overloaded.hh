#ifndef GLASGOW_CONSTRAINT_SOLVER_GUARD_UTIL_OVERLOADED_HH
#define GLASGOW_CONSTRAINT_SOLVER_GUARD_UTIL_OVERLOADED_HH

#include <utility>
#include <variant>

template <class... Ts_>
struct overloaded : Ts_...
{
    using Ts_::operator()...;

    // This exists solely because I haven't found a way of getting clang-format
    // to do something sane if you write visit(overloaded{ ... }, x).
    template <typename... Args_>
    auto visit(Args_ &&... a) -> decltype(auto)
    {
        return std::visit(*this, std::forward<Args_>(a)...);
    }
};

template <class... Ts_>
overloaded(Ts_...) -> overloaded<Ts_...>;

#endif
