#include <gcs/restarts.hh>

#include <catch2/catch_test_macros.hpp>

#include <vector>

using namespace gcs;

using std::vector;

namespace
{
    // The cutoffs a schedule produces over its first n terms, starting from its
    // initial cutoff and advancing between each.
    auto first_cutoffs(RestartSchedule schedule, unsigned n) -> vector<unsigned long long>
    {
        vector<unsigned long long> cutoffs;
        for (unsigned i = 0; i < n; ++i) {
            cutoffs.push_back(schedule.current_cutoff());
            schedule.advance();
        }
        return cutoffs;
    }
}

TEST_CASE("Luby schedule follows the Luby sequence")
{
    // 1, 1, 2, 1, 1, 2, 4, 1, 1, 2, 1, 1, 2, 4, 8, ...
    CHECK(first_cutoffs(RestartSchedule::luby(1), 15) ==
        vector<unsigned long long>{1, 1, 2, 1, 1, 2, 4, 1, 1, 2, 1, 1, 2, 4, 8});
}

TEST_CASE("Luby schedule scales every cutoff")
{
    CHECK(first_cutoffs(RestartSchedule::luby(100), 7) ==
        vector<unsigned long long>{100, 100, 200, 100, 100, 200, 400});
}

TEST_CASE("Luby schedule keeps returning to small cutoffs")
{
    // The reluctant-doubling property we rely on for testability: even far out,
    // a 1*scale cutoff keeps recurring (so short and long runs interleave).
    auto schedule = RestartSchedule::luby(1);
    bool saw_one_after_the_first_block = false;
    for (unsigned i = 0; i < 64; ++i) {
        if (i >= 7 && schedule.current_cutoff() == 1)
            saw_one_after_the_first_block = true;
        schedule.advance();
    }
    CHECK(saw_one_after_the_first_block);
}
