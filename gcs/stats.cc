#include <gcs/stats.hh>

#include <chrono>
#include <ostream>

using namespace gcs;

using std::ostream;

auto gcs::operator<<(ostream & o, const Stats & s) -> ostream &
{
    o << "propagators: " << s.n_propagators << '\n';
    if (0 != s.idempotence_downgrades)
        o << "idempotence downgrades: " << s.idempotence_downgrades << '\n';
    o << "recursions: " << s.recursions << '\n';
    o << "failures: " << s.failures << '\n';
    o << "propagations: " << s.propagations << " " << s.effectful_propagations << " " << s.contradicting_propagations << '\n';
    o << "max depth:  " << s.max_depth << '\n';
    o << "restarts: " << s.restarts << '\n';
    o << "solutions: " << s.solutions << '\n';
    o << "solve time: " << (s.solve_time.count() / 1'000'000.0) << "s" << '\n';
    return o;
}
