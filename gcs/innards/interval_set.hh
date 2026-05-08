#ifndef GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_INNARDS_INTERVAL_SET_HH
#define GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_INNARDS_INTERVAL_SET_HH

#include <gcs/innards/interval_set-fwd.hh>

#include <gch/small_vector.hpp>

#include <cstdlib>
#include <utility>
#include <version>

#ifdef __cpp_lib_generator
#include <generator>
#else
#include <__generator.hpp>
#endif

namespace gcs::innards
{
    /**
     * \brief A set of integers stored as a sorted sequence of disjoint closed intervals.
     *
     * Intended for cases where the set may be large but can be compactly described by a
     * small number of contiguous ranges. For example, the set {1, 2, 3, 4, 8, 9, 10}
     * is stored internally as two intervals [1..4] and [8..10].
     *
     * Intervals are always maintained in sorted order with no two intervals touching
     * or overlapping.
     *
     * \tparam Int_ The integer type used for values and bounds. Must support arithmetic
     * and comparison operators, and construction from a literal zero or one.
     *
     * \ingroup Innards
     */
    template <typename Int_>
    class IntervalSet
    {
    private:
        // Inline capacity tuned for the dominant case in the solver: variable
        // domains usually start as a single contiguous interval, and after a
        // handful of != assertions still have ≤ 2 intervals. Bigger values pay
        // for unused inline storage on every variable and on every snapshot
        // copy at new_epoch().
        static constexpr std::size_t inline_intervals = 2;
        using Intervals = gch::small_vector<std::pair<Int_, Int_>, inline_intervals>;
        Intervals intervals;

    public:
        /**
         * \name Constructors, destructors, and assignment operators.
         * @{
         */

        /**
         * \brief Constructs an empty set.
         */
        IntervalSet() = default;

        /**
         * \brief Constructs a set containing the single closed interval [lower..upper].
         */
        IntervalSet(Int_ lower, Int_ upper) :
            intervals({{lower, upper}})
        {
        }

        IntervalSet(const IntervalSet & other) = default;

        IntervalSet(IntervalSet && other) = default;

        ~IntervalSet() = default;

        auto operator=(const IntervalSet &) -> IntervalSet & = default;

        auto operator=(IntervalSet &&) -> IntervalSet & = default;

        ///@}

        /**
         * \name Querying the set.
         * @{
         */

        /**
         * \brief Returns true if the set contains no values.
         */
        [[nodiscard]] auto empty() const -> bool
        {
            return intervals.empty();
        }

        /**
         * \brief Returns the total number of values across all intervals.
         *
         * This is the number of distinct integers in the set, not the number of
         * intervals used to represent it.
         */
        [[nodiscard]] auto size() const -> Int_
        {
            Int_ result(0);
            for (auto & [l, u] : intervals)
                result += u - l + Int_(1);
            return result;
        }

        /**
         * \brief Returns the smallest value in the set.
         *
         * \note The set must not be empty.
         *
         * \sa upper()
         */
        [[nodiscard]] auto lower() const -> Int_
        {
            return intervals.front().first;
        }

        /**
         * \brief Returns the largest value in the set.
         *
         * \note The set must not be empty.
         *
         * \sa lower()
         */
        [[nodiscard]] auto upper() const -> Int_
        {
            return intervals.back().second;
        }

        /**
         * \brief Returns true if \p value is a member of this set.
         *
         * \sa contains_any_of()
         */
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

        /**
         * \brief Returns true if this set and \p other share at least one value.
         *
         * \sa contains()
         */
        [[nodiscard]] auto contains_any_of(const IntervalSet & other) const -> bool
        {
            auto i = intervals.begin();
            auto j = other.intervals.begin();

            while (i != intervals.end() && j != other.intervals.end()) {
                if (i->first <= j->second && j->first <= i->second)
                    return true;
                if (i->second < j->second)
                    ++i;
                else
                    ++j;
            }

            return false;
        }

        /**
         * \brief Returns true if the set cannot be described by a single interval.
         *
         * Equivalently, returns true if there is at least one integer strictly between
         * lower() and upper() that is not in the set.
         *
         * \sa lower(), upper(), each_gap(), each_gap_interval()
         */
        [[nodiscard]] auto has_holes() const -> bool
        {
            return intervals.size() > 1;
        }

        ///@}

        /**
         * \name Modifying the set.
         * @{
         */

        /**
         * \brief Removes a single value from the set.
         *
         * If \p value is not in the set, does nothing. If \p value falls in
         * the interior of an interval, that interval is split into two.
         */
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

        /**
         * \brief Removes all values strictly less than \p value.
         *
         * Equivalent to intersecting the set with [value, +inf).
         *
         * \sa erase_greater_than()
         */
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

        /**
         * \brief Removes all values strictly greater than \p value.
         *
         * Equivalent to intersecting the set with (-inf, value].
         *
         * \sa erase_less_than()
         */
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

        /**
         * \brief Removes all values, leaving the set empty.
         */
        auto clear() -> void
        {
            intervals.clear();
        }

        /**
         * \brief Appends a single value to the set.
         *
         * \p value must be greater than or equal to upper() if the set is non-empty,
         * i.e. values must be inserted in non-decreasing order. If \p value is
         * exactly upper() + 1, it is merged into the last interval rather than
         * starting a new one.
         *
         * \sa insert_at_end(Int_, Int_)
         */
        auto insert_at_end(Int_ value) -> void
        {
            if (intervals.empty())
                intervals.emplace_back(value, value);
            else if (intervals.back().second == value - Int_(1))
                intervals.back().second++;
            else
                intervals.emplace_back(value, value);
        }

        /**
         * \brief Appends a closed interval [lower..upper] to the set.
         *
         * \p lower must be greater than or equal to upper() if the set is non-empty,
         * i.e. intervals must be inserted in non-decreasing order. If \p lower is
         * exactly upper() + 1, the new interval is merged into the last interval
         * rather than starting a new one.
         *
         * \sa insert_at_end(Int_)
         */
        auto insert_at_end(Int_ lower, Int_ upper) -> void
        {
            if (intervals.empty())
                intervals.emplace_back(lower, upper);
            else if (intervals.back().second == lower - Int_(1))
                intervals.back().second = upper;
            else
                intervals.emplace_back(lower, upper);
        }

        ///@}

        /**
         * \name Iteration.
         * @{
         */

        /**
         * \brief Returns a generator that yields each value in the set in ascending order.
         *
         * \sa each_reversed(), each_interval()
         */
        [[nodiscard]] auto each() const -> std::generator<Int_>
        {
            return [](const Intervals & intervals) -> std::generator<Int_> {
                for (const auto & [l, u] : intervals)
                    for (Int_ i = l; i <= u; ++i)
                        co_yield i;
            }(intervals);
        }

        /**
         * \brief Returns a generator that yields each stored interval as a
         * (lower, upper) pair, in ascending order.
         *
         * \sa each(), each_gap_interval()
         */
        [[nodiscard]] auto each_interval() const -> std::generator<std::pair<Int_, Int_>>
        {
            return [](const Intervals & intervals) -> std::generator<std::pair<Int_, Int_>> {
                for (const auto & i : intervals)
                    co_yield i;
            }(intervals);
        }

        /**
         * \brief Returns a generator that yields each integer strictly between lower()
         * and upper() that is not a member of the set, in ascending order.
         *
         * \sa each_gap_interval(), has_holes()
         */
        [[nodiscard]] auto each_gap() const -> std::generator<Int_>
        {
            return [](const Intervals & intervals) -> std::generator<Int_> {
                for (std::size_t p = 0; p < intervals.size() - 1; ++p)
                    for (Int_ i = intervals[p].second + Int_{1}; i != intervals[p + 1].first; ++i)
                        co_yield i;
            }(intervals);
        }

        /**
         * \brief Returns a generator that yields each gap in the set as a half-open
         * (first, next) pair, in ascending order.
         *
         * Each yielded pair (a, b) represents the half-open range [a, b): a is the
         * first absent value after an interval, and b is the lower bound of the next
         * interval (the first present value after the gap). This is consistent with
         * each_gap(), which iterates <code>i = a; i != b; ++i</code>.
         *
         * \sa each_gap(), has_holes()
         */
        [[nodiscard]] auto each_gap_interval() const -> std::generator<std::pair<Int_, Int_>>
        {
            return [](const Intervals & intervals) -> std::generator<std::pair<Int_, Int_>> {
                for (std::size_t p = 0; p < intervals.size() - 1; ++p)
                    co_yield std::pair{intervals[p].second + Int_{1}, intervals[p + 1].first};
            }(intervals);
        }

        /**
         * \brief Returns a generator that yields each maximal interval of values
         * that are present in this set and absent from \p other, in ascending order.
         *
         * Each yielded pair (l, u) represents the closed interval [l, u] — both
         * endpoints are values that are in <code>*this</code> and not in
         * \p other, mirroring each_interval()'s convention. Per-value
         * iteration is <code>for (Int_ v = l; v <= u; ++v)</code>. (Note: this
         * differs from each_gap_interval(), which yields half-open ranges.)
         *
         * Equivalent to (but cheaper than) iterating each value in the set and
         * testing membership in \p other one at a time: walks both interval lists
         * via merge in <code>O(intervals(this) + intervals(other) + |output|)</code>.
         *
         * Use this when implementing set-difference inference patterns. The
         * yielded intervals can be expanded to per-value via a nested loop, or
         * later passed wholesale to an interval-level inference primitive.
         *
         * \sa each_interval(), each_gap_interval()
         */
        [[nodiscard]] auto each_interval_minus(const IntervalSet & other) const -> std::generator<std::pair<Int_, Int_>>
        {
            return [](Intervals self_intervals, Intervals other_intervals) -> std::generator<std::pair<Int_, Int_>> {
                auto j = other_intervals.begin();
                for (auto i = self_intervals.begin(); i != self_intervals.end(); ++i) {
                    Int_ cur = i->first;
                    while (j != other_intervals.end() && j->second < cur)
                        ++j;
                    while (j != other_intervals.end() && j->first <= i->second) {
                        if (j->first > cur)
                            co_yield std::pair{cur, j->first - Int_{1}};
                        cur = j->second + Int_{1};
                        if (cur > i->second)
                            break;
                        ++j;
                    }
                    if (cur <= i->second)
                        co_yield std::pair{cur, i->second};
                }
            }(intervals, other.intervals);
        }

        /**
         * \brief Returns a generator that yields each value in the set in descending order.
         *
         * \sa each()
         */
        [[nodiscard]] auto each_reversed() const -> std::generator<Int_>
        {
            return [](const Intervals & intervals) -> std::generator<Int_> {
                for (auto lu = intervals.rbegin(); lu != intervals.rend(); ++lu)
                    for (Int_ i = lu->second; i >= lu->first; --i)
                        co_yield i;
            }(intervals);
        }

        ///@}
    };
}

#endif
