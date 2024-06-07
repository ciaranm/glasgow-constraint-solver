#ifndef GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_INNARDS_INTERVAL_SET_HH
#define GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_INNARDS_INTERVAL_SET_HH

#include <gcs/innards/interval_set-fwd.hh>

#include <cstdlib>
#include <vector>

#if __has_cpp_attribute(__cpp_lib_generator)
#include <generator>
#else
#include <__generator.hpp>
#endif

namespace gcs::innards
{
    template <typename Int_>
    class IntervalSet
    {
    private:
        using Intervals = std::vector<std::pair<Int_, Int_>>;
        Intervals intervals;

    public:
        IntervalSet() = default;

        IntervalSet(Int_ lower, Int_ upper) :
            intervals({{lower, upper}})
        {
        }

        IntervalSet(const IntervalSet & other) = default;

        IntervalSet(IntervalSet && other) = default;

        ~IntervalSet() = default;

        auto operator=(const IntervalSet &) -> IntervalSet & = default;

        auto operator=(IntervalSet &&) -> IntervalSet & = default;

        [[nodiscard]] auto empty() const -> bool
        {
            return intervals.empty();
        }

        [[nodiscard]] auto size() const -> Int_
        {
            Int_ result(0);
            for (auto & [l, u] : intervals)
                result += u - l + Int_(1);
            return result;
        }

        auto erase(Int_ value) -> void
        {
            for (auto iter = intervals.begin(), iter_end = intervals.end(); iter != iter_end; ++iter) {
                if (value >= iter->first && value <= iter->second) {
                    if (iter->first == iter->second) {
                        intervals.erase(iter);
                        return;
                    }
                    else if (value == iter->first) {
                        iter->first += Int_(1);
                    }
                    else if (value == iter->second) {
                        iter->second -= Int_(1);
                    }
                    else {
                        // 4..9 erase 7 -> 4..6 8..9
                        auto new_range = *iter;
                        iter->second = value - Int_(1);
                        new_range.first = value + Int_(1);
                        intervals.insert(next(iter), new_range);
                        return;
                    }
                }
                else if (iter->first > value)
                    return;
            }
        }

        auto erase_less_than(Int_ value) -> void
        {
            auto iter = intervals.begin(), iter_end = intervals.end();
            for (; iter != iter_end; ++iter) {
                if (iter->first <= value && value <= iter->second) {
                    iter->first = value;
                    if (iter != intervals.begin())
                        intervals.erase(intervals.begin(), iter);
                    return;
                }
                else if (value < iter->first) {
                    intervals.erase(intervals.begin(), iter);
                    return;
                }
            }

            if (iter == iter_end && ! intervals.empty() && intervals.back().second < value)
                intervals.clear();
        }

        auto erase_greater_than(Int_ value) -> void
        {
            auto iter = intervals.begin(), iter_end = intervals.end();
            for (; iter != iter_end; ++iter) {
                if (iter->first <= value && value <= iter->second) {
                    iter->second = value;
                    intervals.erase(next(iter), intervals.end());
                    return;
                }
                else if (value < iter->first) {
                    intervals.erase(iter, intervals.end());
                    return;
                }
            }
        }

        [[nodiscard]] auto lower() const -> Int_
        {
            return intervals.front().first;
        }

        [[nodiscard]] auto upper() const -> Int_
        {
            return intervals.back().second;
        }

        [[nodiscard]] auto contains(Int_ value) const -> bool
        {
            for (auto & [l, u] : intervals) {
                if (l <= value && value <= u)
                    return true;
                if (u > value)
                    return false;
            }

            return false;
        }

        [[nodiscard]] auto has_holes() const -> bool
        {
            return intervals.size() > 1;
        }

        auto clear() -> void
        {
            intervals.clear();
        }

        auto insert_at_end(Int_ value) -> void
        {
            if (intervals.empty())
                intervals.emplace_back(value, value);
            else if (intervals.back().second == value - Int_(1))
                intervals.back().second++;
            else
                intervals.emplace_back(value, value);
        }

        auto insert_at_end(Int_ lower, Int_ upper) -> void
        {
            if (intervals.empty())
                intervals.emplace_back(lower, upper);
            else if (intervals.back().second == lower - Int_(1))
                intervals.back().second = upper;
            else
                intervals.emplace_back(lower, upper);
        }

        [[nodiscard]] auto each() const -> std::generator<Int_>
        {
            return [](const Intervals & intervals) -> std::generator<Int_> {
                for (const auto & [l, u] : intervals)
                    for (Int_ i = l; i <= u; ++i)
                        co_yield i;
            }(intervals);
        }

        [[nodiscard]] auto each_interval() const -> std::generator<std::pair<Int_, Int_>>
        {
            return [](const Intervals & intervals) -> std::generator<std::pair<Int_, Int_>> {
                for (const auto & i : intervals)
                    co_yield i;
            }(intervals);
        }

        [[nodiscard]] auto each_gap() const -> std::generator<Int_>
        {
            return [](const Intervals & intervals) -> std::generator<Int_> {
                for (std::size_t p = 0; p < intervals.size() - 1; ++p)
                    for (Int_ i = intervals[p].second + Int_{1}; i != intervals[p + 1].first; ++i)
                        co_yield i;
            }(intervals);
        }

        [[nodiscard]] auto each_gap_interval() const -> std::generator<std::pair<Int_, Int_>>
        {
            return [](const Intervals & intervals) -> std::generator<std::pair<Int_, Int_>> {
                for (std::size_t p = 0; p < intervals.size() - 1; ++p)
                    co_yield std::pair{intervals[p].second + Int_{1}, intervals[p + 1].first};
            }(intervals);
        }

        [[nodiscard]] auto each_reversed() const -> std::generator<Int_>
        {
            return [](const Intervals & intervals) -> std::generator<Int_> {
                for (auto lu = intervals.rbegin(); lu != intervals.rend(); ++lu)
                    for (Int_ i = lu->second; i >= lu->first; --i)
                        co_yield i;
            }(intervals);
        }
    };
}

#endif
