#include <gcs/innards/interval_tree.hh>

#include <catch2/catch_test_macros.hpp>

#include <algorithm>
#include <random>
#include <set>
#include <utility>
#include <vector>

using namespace gcs;
using namespace gcs::innards;

using std::mt19937;
using std::pair;
using std::set;
using std::uniform_int_distribution;
using std::vector;

namespace
{
    auto collect_containing(const IntervalTree & tree, Integer lo, Integer hi) -> vector<pair<Integer, Integer>>
    {
        vector<pair<Integer, Integer>> result;
        tree.for_each_containing(lo, hi, [&](Integer c, Integer d) { result.emplace_back(c, d); });
        return result;
    }

    auto collect_contained_in(const IntervalTree & tree, Integer lo, Integer hi) -> vector<pair<Integer, Integer>>
    {
        vector<pair<Integer, Integer>> result;
        tree.for_each_contained_in(lo, hi, [&](Integer c, Integer d) { result.emplace_back(c, d); });
        return result;
    }
}

TEST_CASE("Simple containment queries")
{
    IntervalTree tree;
    tree.insert(1_i, 10_i);
    tree.insert(3_i, 7_i);
    tree.insert(5_i, 5_i);
    tree.insert(8_i, 12_i);

    CHECK(collect_containing(tree, 5_i, 5_i) == vector<pair<Integer, Integer>>{{1_i, 10_i}, {3_i, 7_i}, {5_i, 5_i}});
    CHECK(collect_containing(tree, 4_i, 6_i) == vector<pair<Integer, Integer>>{{1_i, 10_i}, {3_i, 7_i}});
    CHECK(collect_containing(tree, 9_i, 11_i) == vector<pair<Integer, Integer>>{{8_i, 12_i}});
    CHECK(collect_containing(tree, 0_i, 20_i).empty());

    CHECK(collect_contained_in(tree, 1_i, 10_i) == vector<pair<Integer, Integer>>{{1_i, 10_i}, {3_i, 7_i}, {5_i, 5_i}});
    CHECK(collect_contained_in(tree, 3_i, 7_i) == vector<pair<Integer, Integer>>{{3_i, 7_i}, {5_i, 5_i}});
    CHECK(collect_contained_in(tree, 4_i, 20_i) == vector<pair<Integer, Integer>>{{5_i, 5_i}, {8_i, 12_i}});
    CHECK(collect_contained_in(tree, 6_i, 6_i).empty());
}

TEST_CASE("Duplicate inserts are ignored")
{
    IntervalTree tree;
    tree.insert(2_i, 4_i);
    tree.insert(2_i, 4_i);
    CHECK(collect_containing(tree, 3_i, 3_i) == vector<pair<Integer, Integer>>{{2_i, 4_i}});
}

TEST_CASE("Randomised against brute force")
{
    mt19937 rand{77};
    for (int round = 0; round < 50; ++round) {
        IntervalTree tree;
        set<pair<Integer, Integer>> reference;

        uniform_int_distribution<int> value{-20, 20};
        for (int n = 0; n < 100; ++n) {
            auto a = Integer{value(rand)}, b = Integer{value(rand)};
            if (b < a)
                std::swap(a, b);
            tree.insert(a, b);
            reference.emplace(a, b);
        }

        for (int q = 0; q < 50; ++q) {
            auto a = Integer{value(rand)}, b = Integer{value(rand)};
            if (b < a)
                std::swap(a, b);

            vector<pair<Integer, Integer>> expected_containing, expected_contained;
            for (const auto & [c, d] : reference) {
                if (c <= a && b <= d)
                    expected_containing.emplace_back(c, d);
                if (a <= c && d <= b)
                    expected_contained.emplace_back(c, d);
            }

            CHECK(collect_containing(tree, a, b) == expected_containing);
            CHECK(collect_contained_in(tree, a, b) == expected_contained);
        }
    }
}
