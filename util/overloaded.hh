/* vim: set sw=4 sts=4 et foldmethod=syntax : */

#ifndef GLASGOW_CONSTRAINT_SOLVER_GUARD_UTIL_OVERLOADED_HH
#define GLASGOW_CONSTRAINT_SOLVER_GUARD_UTIL_OVERLOADED_HH 1

template <class... Ts_> struct overloaded : Ts_... { using Ts_::operator()...; };
template <class... Ts_> overloaded(Ts_ ...) -> overloaded<Ts_...>;

#endif
