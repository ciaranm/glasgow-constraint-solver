#include <gcs/restarts.hh>

using namespace gcs;

namespace
{
    // The i-th term (i >= 1) of the Luby sequence 1, 1, 2, 1, 1, 2, 4, ...,
    // via Knuth's reluctant doubling.
    auto luby_term(unsigned long long i) -> unsigned long long
    {
        for (unsigned long long k = 1;;) {
            auto block = (1ULL << k) - 1;
            if (i == block)
                return 1ULL << (k - 1);
            if (i < block) {
                i = i - ((1ULL << (k - 1)) - 1);
                k = 1;
            }
            else
                ++k;
        }
    }
}

RestartSchedule::RestartSchedule(unsigned long long scale) :
    _scale(scale),
    _index(1)
{
}

auto RestartSchedule::luby(unsigned long long scale) -> RestartSchedule
{
    return RestartSchedule{scale};
}

auto RestartSchedule::current_cutoff() const -> unsigned long long
{
    return luby_term(_index) * _scale;
}

auto RestartSchedule::advance() -> void
{
    ++_index;
}
