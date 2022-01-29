/* vim: set sw=4 sts=4 et foldmethod=syntax : */

#include <gcs/stats.hh>

#include <algorithm>
#include <chrono>
#include <ostream>

using namespace gcs;

using std::ostream;
using std::sort;

auto gcs::operator<<(ostream & o, const Stats & s) -> ostream &
{
    o << "cnfs: " << s.n_cnfs << '\n';
    o << "propagators: " << s.n_propagators << '\n';
    o << "recursions: " << s.recursions << '\n';
    o << "failures: " << s.failures << '\n';
    o << "propagations: " << s.propagations << '\n';
    o << "max depth:  " << s.max_depth << '\n';
    o << "solutions: " << s.solutions << '\n';
    o << "solve time: " << (s.solve_time.count() / 1'000'000.0) << "s" << '\n';
    return o;
}
