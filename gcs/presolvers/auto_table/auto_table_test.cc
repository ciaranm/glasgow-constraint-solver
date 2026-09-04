/* The AutoTable presolver, and specifically the size of the table it installs.
 *
 * #809 gave the tabulated extensional propagators access to the compact-table
 * arm, through ExtensionalCompactTable::create_for_auto(), which hands one back
 * only for a table of at least ExtensionalCompactTable::min_tuples --- 64 ---
 * entries. #835 then measured what the suite actually reaches on the AutoTable
 * half of that: 29 tabulations across four tests, the largest 22 tuples, none
 * of them eligible. Replacing that call site with a literal null and running
 * the whole of ctest confirms it: all 801 other tests pass.
 *
 * The fixture below is the one that notices. Three variables of an AllDifferent
 * over 0..7 tabulate to 268 tuples, comfortably the other side of the
 * threshold, and cheaply enough that the subproblem search finding them is not
 * worth measuring.
 *
 * Two things are pinned here, and they are different depths. That the table is
 * *offered* the compact algorithm is what AutoTableStats::compact_table says,
 * and it is what the null above breaks. That the propagator then *takes* it is
 * decided during search --- table::Auto watches 32 wakes first --- and no
 * figure reports it, so it was established by measurement instead: this fixture
 * decides at wake 32 on a mean live set of 28 and adopts. Sabotaging
 * seed_compact_table_from_live_set() to keep one tuple makes the enumeration
 * below disagree with the plain model, which is the standing consequence: the
 * compact filtering runs here, so breaking it fails this test.
 */

#include <gcs/constraints/all_different.hh>
#include <gcs/constraints/comparison.hh>
#include <gcs/constraints/extensional_utils.hh>
#include <gcs/constraints/innards/constraints_test_utils.hh>
#include <gcs/constraints/linear.hh>
#include <gcs/presolvers/auto_table.hh>
#include <gcs/problem.hh>
#include <gcs/solve.hh>

#include <catch2/catch_test_macros.hpp>

#include <memory>
#include <optional>
#include <set>
#include <string>
#include <utility>
#include <vector>

using namespace gcs;
using namespace gcs::test_innards;

using std::make_optional;
using std::make_shared;
using std::move;
using std::nullopt;
using std::optional;
using std::set;
using std::shared_ptr;
using std::string;
using std::vector;

namespace
{
    /// Six variables over 0..`domain` - 1, two disjoint AllDifferents, a total,
    /// and an ordering to break the symmetry between the two triples. The
    /// tabulated scope is the first AllDifferent's, so the table has one entry
    /// per ordered triple of distinct values that the rest of the model does not
    /// rule out at the root.
    struct Instance
    {
        Integer domain;
        Integer total;
    };

    /// 268 tuples, measured: of the 336 ordered triples of distinct values over
    /// 0..7, that is how many have a completion --- three more distinct values,
    /// the first of them above v[0], totalling 21 with them. The tabulation is
    /// exact here rather than a superset, which is worth knowing when reading
    /// the number but is not what the tests below rest on: they need only that
    /// it is the far side of 64.
    constexpr Instance big{8_i, 21_i};

    /// The same shape over half the domain, and 16 tuples of a possible 24, so
    /// that what separates the two outcomes below is the size of the table and
    /// nothing else about the model.
    constexpr Instance small{4_i, 9_i};

    struct Outcome
    {
        set<vector<long long>> solutions;
        shared_ptr<AutoTableStats> block = make_shared<AutoTableStats>();
    };

    auto enumerate(const Instance & instance, bool presolve, const optional<string> & proof_name) -> Outcome
    {
        Outcome outcome;

        Problem p;
        auto v = p.create_integer_variable_vector(6, 0_i, instance.domain - 1_i, "v");
        p.post(AllDifferent{vector<IntegerVariableID>{v[0], v[1], v[2]}});
        p.post(AllDifferent{vector<IntegerVariableID>{v[3], v[4], v[5]}});
        p.post(WeightedSum{} + 1_i * v[0] + 1_i * v[1] + 1_i * v[2] //
                + 1_i * v[3] + 1_i * v[4] + 1_i * v[5] ==
            instance.total);
        p.post(LessThan{v[0], v[3]});

        if (presolve)
            p.add_presolver(AutoTable{vector<IntegerVariableID>{v[0], v[1], v[2]}, outcome.block});

        solve(
            p,
            [&](const CurrentState & s) -> bool {
                vector<long long> solution;
                for (const auto & var : v)
                    solution.push_back(s(var).raw_value);
                outcome.solutions.emplace(move(solution));
                return true;
            },
            proof_name ? make_optional<ProofOptions>(*proof_name) : nullopt);

        return outcome;
    }
}

TEST_CASE("AutoTable tabulates past the compact table's threshold")
{
    auto tabulated = enumerate(big, true, nullopt);

    // The point of the fixture: below this, create_for_auto() hands back a null
    // and the propagator has only ever had the live-set arm.
    CHECK(tabulated.block->tuples >= innards::ExtensionalCompactTable::min_tuples);
    CHECK(tabulated.block->compact_table);

    // And the answers are the ones the model has without the presolver, which is
    // what says taking the arm was safe: the tabulation, the compact table's
    // support masks and its incremental live-word update all sit between this
    // enumeration and the plain one.
    auto plain = enumerate(big, false, nullopt);
    CHECK(! plain.solutions.empty());
    CHECK(tabulated.solutions == plain.solutions);
}

TEST_CASE("AutoTable below the compact table's threshold gets the live-set arm")
{
    // The same model over half the domain, so that the figure checked above is
    // reporting the size of the table rather than being true of every table.
    auto tabulated = enumerate(small, true, nullopt);

    CHECK(tabulated.block->tuples > 0);
    CHECK(tabulated.block->tuples < innards::ExtensionalCompactTable::min_tuples);
    CHECK(! tabulated.block->compact_table);

    auto plain = enumerate(small, false, nullopt);
    CHECK(! plain.solutions.empty());
    CHECK(tabulated.solutions == plain.solutions);
}

TEST_CASE("A proof of a tabulation past the threshold verifies")
{
    // The tabulation half of #809 is proof-checked through odd_even_sum, which
    // run_test_and_verify.bash runs; this is the AutoTable half of the same
    // thing. The presolver's own derivation is a pair of redundance lines per
    // tuple, and the propagator it installs takes NoHint, so every inference it
    // then makes has to be RUP against them --- including the ones the compact
    // arm is responsible for, which is what is new here.
    const auto proof_name = "auto_table_presolver_compact_arm_test";

    auto tabulated = enumerate(big, true, proof_name);
    REQUIRE(tabulated.block->compact_table);
    CHECK(verify_proof_and_dispose(proof_name));
}
