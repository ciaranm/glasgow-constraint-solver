/* The bounds consistent AllDifferent propagator against a brute-force
 * reference, at the root, on thousands of small random instances.
 *
 * The data-driven all_different_test checks, at every search node, that each
 * bound the propagator leaves has a bounds(Z) support; this checks the other
 * direction too, that it leaves no bound it could have moved, and that it
 * fails exactly when there is no solution with every variable inside its
 * bounds. Together those pin the algorithm to exactly bounds(Z) consistency,
 * which matters because it is a union-find sweep whose correctness is not
 * obvious from reading it.
 *
 * The reference is the greatest fixpoint of: move each bound to the nearest
 * value in the variable's domain that extends to an all-different assignment
 * in which every other variable lies between its own bounds. Holes in the
 * domains are there on purpose: the propagator reads only bounds, but the
 * state snaps a bound it writes past a hole, and the fixpoint has to account
 * for that. */

#include <gcs/constraints/all_different.hh>
#include <gcs/innards/propagators.hh>
#include <gcs/innards/state.hh>
#include <gcs/problem.hh>
#include <gcs/stats.hh>

#include <catch2/catch_test_macros.hpp>

#include <algorithm>
#include <optional>
#include <random>
#include <sstream>
#include <string>
#include <utility>
#include <vector>

using namespace gcs;
using namespace gcs::innards;

using std::mt19937;
using std::nullopt;
using std::optional;
using std::pair;
using std::string;
using std::stringstream;
using std::uniform_int_distribution;
using std::vector;

namespace
{
    // Can every variable other than `fixed` take a distinct value between its
    // bounds, with `fixed` taking `value`?
    auto extendable(const vector<pair<int, int>> & bounds, std::size_t fixed, int value) -> bool
    {
        vector<int> used{value};
        vector<std::size_t> others;
        for (std::size_t i = 0; i < bounds.size(); ++i)
            if (i != fixed)
                others.push_back(i);

        auto search = [&](auto && self, std::size_t k) -> bool {
            if (k == others.size())
                return true;
            auto [lo, hi] = bounds[others[k]];
            for (int v = lo; v <= hi; ++v)
                if (std::ranges::find(used, v) == used.end()) {
                    used.push_back(v);
                    if (self(self, k + 1))
                        return true;
                    used.pop_back();
                }
            return false;
        };
        return search(search, 0);
    }

    // The bounds(Z) fixpoint over the given domains, or nullopt if some
    // variable has no supported value left.
    auto reference(const vector<vector<int>> & domains) -> optional<vector<pair<int, int>>>
    {
        vector<pair<int, int>> bounds;
        for (const auto & d : domains)
            bounds.emplace_back(d.front(), d.back());

        bool changed = true;
        while (changed) {
            changed = false;
            for (std::size_t i = 0; i < domains.size(); ++i) {
                optional<int> new_lo, new_hi;
                for (int v : domains[i])
                    if (v >= bounds[i].first && v <= bounds[i].second && extendable(bounds, i, v)) {
                        new_lo = v;
                        break;
                    }
                if (! new_lo)
                    return nullopt;
                for (auto it = domains[i].rbegin(); it != domains[i].rend(); ++it)
                    if (*it >= bounds[i].first && *it <= bounds[i].second && extendable(bounds, i, *it)) {
                        new_hi = *it;
                        break;
                    }
                if (*new_lo != bounds[i].first || *new_hi != bounds[i].second) {
                    bounds[i] = {*new_lo, *new_hi};
                    changed = true;
                }
            }
        }
        return bounds;
    }

    auto describe(const vector<vector<int>> & domains) -> string
    {
        stringstream s;
        for (const auto & d : domains) {
            s << "{";
            for (auto v : d)
                s << " " << v;
            s << " } ";
        }
        return s.str();
    }
}

TEST_CASE("BC AllDifferent reaches exactly bounds(Z) consistency at the root")
{
    unsigned instances = 0, failures = 0, moved = 0;
    for (unsigned seed = 0; seed < 5000; ++seed) {
        mt19937 rand{seed};
        auto pick = [&](int lo, int hi) { return uniform_int_distribution<int>{lo, hi}(rand); };

        auto n = pick(2, 6);
        vector<vector<int>> domains;
        for (int i = 0; i < n; ++i) {
            auto lo = pick(-5, 5);
            auto hi = lo + pick(0, 5);
            vector<int> d;
            for (int v = lo; v <= hi; ++v)
                // Punch the occasional hole, never at a bound.
                if (v == lo || v == hi || pick(1, 100) > 20)
                    d.push_back(v);
            domains.push_back(d);
        }
        INFO("seed " << seed << ": " << describe(domains));

        Problem p;
        vector<IntegerVariableID> vars;
        for (const auto & d : domains) {
            if (d.size() == 1 && pick(0, 1))
                vars.push_back(constant_variable(Integer{d.front()}));
            else {
                vector<Integer> values;
                for (auto v : d)
                    values.push_back(Integer{v});
                vars.push_back(p.create_integer_variable(values));
            }
        }
        p.post(AllDifferent{vars}.with_consistency(consistency::BC{}));

        Stats stats;
        auto state = p.create_state_for_new_search(nullptr);
        auto propagators = p.create_propagators(state, stats, nullptr);
        auto ok = propagators.initialise(state, nullptr) && propagators.propagate(Literals{}, state, nullptr);

        auto expected = reference(domains);
        ++instances;
        if (! expected) {
            ++failures;
            CHECK_FALSE(ok);
        }
        else {
            REQUIRE(ok);
            for (std::size_t i = 0; i < vars.size(); ++i) {
                INFO("variable " << i);
                CHECK(state.lower_bound(vars[i]) == Integer{(*expected)[i].first});
                CHECK(state.upper_bound(vars[i]) == Integer{(*expected)[i].second});
                if ((*expected)[i] != pair{domains[i].front(), domains[i].back()})
                    ++moved;
            }
        }
    }

    // The instances have to exercise both the failures and the bound moves,
    // or agreeing with the reference says little.
    INFO(instances << " instances, " << failures << " infeasible, " << moved << " bounds moved");
    CHECK(failures >= 50);
    CHECK(moved >= 1000);
}
