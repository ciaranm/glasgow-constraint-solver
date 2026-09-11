#ifndef GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_CONSTRAINTS_INNARDS_NO_OVERLAP_WALK_HH
#define GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_CONSTRAINTS_INNARDS_NO_OVERLAP_WALK_HH

#include <gcs/exception.hh>
#include <gcs/integer.hh>
#include <gcs/interval_set.hh>

#include <cstddef>
#include <utility>
#include <vector>

namespace gcs::innards
{
    /**
     * \brief One move of the no-overlap walk.
     *
     * The walk is the certificate that two domains are disjoint, stated over
     * *runs* rather than values: see walk_no_overlap() for what it maintains and
     * why these are the moves.
     *
     * \ingroup Innards
     */
    enum class NoOverlapStep
    {
        AnchorV1Lower,    ///< the walk starts at v1's lower bound: `v1 >= lo`.
        JumpToV2Lower,    ///< `v2 >= lo`, so where the two are equal v1 is there too. lo == hi.
        SkipV1Hole,       ///< v1 has no value in [lo, hi], so it is already past hi.
        SkipV2Hole,       ///< v2 has no value in [lo, hi], so where they are equal neither has v1.
        StopAboveV1Upper, ///< `v1 <= lo` and the walk has reached hi > lo: contradiction.
        StopAboveV2Upper  ///< `v2 <= lo` and the walk has reached hi > lo: contradiction, where they are equal.
    };

    /**
     * \brief Walk two disjoint domains, reporting a certificate of their
     * disjointness whose length is the number of runs it takes to say it, not
     * the number of values the domains span.
     *
     * The walk carries one invariant up the number line: at each point p, the
     * facts reported so far (together with whatever makes the two operands
     * equal --- a reification condition for `equals`, an index tuple's guard for
     * `Element`) force `v1 >= p`. It starts at v1's lower bound, and each move
     * pushes p past one maximal run of values v1 cannot take --- either because
     * v1 itself has nothing there, or because *v2* has nothing there and where
     * they are equal v1 must be wherever v2 is. p is strictly increasing, so the
     * walk stops after at most one move per interval of either domain, and it
     * stops by running p off the top of one of the two domains, which is the
     * contradiction the conclusion needs.
     *
     * A caller turns each move into proof lines. What each move owes, given a
     * checker carrying `v1 >= p` and the reason's literals as units:
     *
     *   - `AnchorV1Lower`: nothing; the reason literal is the fact.
     *   - `JumpToV2Lower`: one lemma, turning `v2 >= lo` into `v1 >= lo`.
     *   - `SkipV1Hole`: nothing; that and `v1 >= lo` meet in the range literal's
     *     own reverse reification, which gives `v1 >= hi + 1`.
     *   - `SkipV2Hole`: two lemmas; `v1 >= lo` crosses to `v2 >= lo`, that and
     *     the literal give `v2 >= hi + 1` through v2's reverse reification, and
     *     that crosses back.
     *   - `StopAboveV1Upper`: nothing; `v1 >= p` and it are opposite ends of v1's
     *     own order chain.
     *   - `StopAboveV2Upper`: one lemma; `v1 >= p` crosses to `v2 >= p`, against it.
     *
     * \p d1 and \p d2 must be non-empty and disjoint, which is exactly the
     * condition the rules using this fire under.
     *
     * \ingroup Innards
     */
    template <typename Step_>
    auto walk_no_overlap(const IntervalSet<Integer> & d1, const IntervalSet<Integer> & d2, Step_ && step) -> void
    {
        std::vector<std::pair<Integer, Integer>> i1, i2;
        for (const auto & i : d1.each_interval())
            i1.push_back(i);
        for (const auto & i : d2.each_interval())
            i2.push_back(i);
        if (i1.empty() || i2.empty())
            throw UnexpectedException{"no-overlap walk over an empty domain"};

        auto [lb1, ub1] = std::pair{i1.front().first, i1.back().second};
        auto [lb2, ub2] = std::pair{i2.front().first, i2.back().second};

        // Establish `v1 >= p` for the first time. If v2 starts above v1 does,
        // v2's own lower bound gets us there and v1's is never mentioned --
        // which is what makes the bounds-disjoint case a two-literal reason.
        auto p = lb1;
        if (p < lb2) {
            step(NoOverlapStep::JumpToV2Lower, lb2, lb2);
            p = lb2;
        }
        else
            step(NoOverlapStep::AnchorV1Lower, lb1, lb1);

        // The cursors only ever move forwards, because p does; each keeps the
        // first interval of its domain that has not already been passed.
        std::size_t j1 = 0, j2 = 0;
        while (true) {
            if (p > ub1) {
                step(NoOverlapStep::StopAboveV1Upper, ub1, p);
                return;
            }
            if (p > ub2) {
                step(NoOverlapStep::StopAboveV2Upper, ub2, p);
                return;
            }

            // p <= ub1 and p <= ub2, so neither search runs off the end.
            while (i1[j1].second < p)
                ++j1;
            while (i2[j2].second < p)
                ++j2;

            if (p < i1[j1].first) {
                // p is outside v1. It may be outside v2 as well, in which case
                // the v2-free run from here could be the longer of the two and
                // taking it would end the walk in fewer moves. Take v1's anyway:
                // its move costs no lemmas, v2's costs two, and the choice only
                // ever changes the move count by a constant factor -- the bound
                // is one move per interval of either domain either way.
                auto hi = i1[j1].first - 1_i;
                step(NoOverlapStep::SkipV1Hole, p, hi);
                p = hi + 1_i;
            }
            else {
                // p is a value of v1, so disjointness says it is not one of v2,
                // and v2's next interval starts strictly above it.
                if (i2[j2].first <= p)
                    throw UnexpectedException{"no-overlap walk over domains that do overlap"};
                auto hi = i2[j2].first - 1_i;
                step(NoOverlapStep::SkipV2Hole, p, hi);
                p = hi + 1_i;
            }
        }
    }
}

#endif
