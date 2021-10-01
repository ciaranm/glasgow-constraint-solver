/* vim: set sw=4 sts=4 et foldmethod=syntax : */

#include <gcs/stats.hh>

#include <algorithm>
#include <chrono>
#include <ostream>

using namespace gcs;

using std::ostream;
using std::sort;

auto gcs::operator<< (ostream & o, const Stats & s) -> ostream &
{
    o << "cnfs: " << s.n_cnfs << '\n';
    o << "propagators: " << s.n_propagators << '\n';
    o << "propagations:";
    auto p = s.propagation_function_calls;
    sort(p.begin(), p.end(), [&] (const auto & a, const auto & b) -> bool {
            auto [ ta, ca, na ] = a;
            auto [ tb, cb, nb ] = b;
            return a < b;
            });
    for (auto & [ t, c, n ] : p)
        o << " " << n << ": " << (t.count() / 1'000'000.0d) << "s / " << c << ";";
    o << '\n';
    o << "recursions: " << s.recursions << '\n';
    o << "failures: " << s.failures << '\n';
    o << "max depth:  " << s.max_depth << '\n';
    o << "solutions: "  << s.solutions << '\n';
    o << "solve time: " << (s.solve_time.count() / 1'000'000.0d) << "s" << '\n';
    return o;
}

