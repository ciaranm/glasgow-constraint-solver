/* Element's consistency::Auto end to end, through gcs::solve_with(), which is
 * where the choice between the result's two propagators is made.
 *
 * The property that matters (dev_docs/optional-interior-pruning.md) is that
 * switching off a pruning nothing observes changes no bound at any fixpoint,
 * so a search whose brancher only reads bounds must explore exactly the same
 * tree whether the elements are forced to GAC or left to Auto. Soundness alone
 * would not catch a wrong switch-off, since both arms are sound, so the test
 * compares trees. It also has to be able to fail: the fixtures are checked to
 * include models where Auto does switch something off, and models where BC
 * really does explore a different tree from GAC, so that Auto has to have kept
 * the pruning there to pass.
 *
 * The other promise is that the choice never changes the encoding, which is
 * checked by comparing the OPB files byte for byte. */

#include <gcs/constraints/all_different.hh>
#include <gcs/constraints/comparison.hh>
#include <gcs/constraints/element.hh>
#include <gcs/constraints/equals.hh>
#include <gcs/constraints/innards/constraints_test_utils.hh>
#include <gcs/constraints/linear.hh>
#include <gcs/expression.hh>
#include <gcs/innards/propagators.hh>
#include <gcs/problem.hh>
#include <gcs/search_heuristics.hh>
#include <gcs/solve.hh>
#include <gcs/stats.hh>

#include <catch2/catch_test_macros.hpp>

#include <fstream>
#include <iterator>
#include <optional>
#include <random>
#include <sstream>
#include <string>
#include <tuple>
#include <utility>
#include <variant>
#include <vector>

using namespace gcs;
using namespace gcs::innards;
using namespace gcs::test_innards;

using std::ifstream;
using std::istreambuf_iterator;
using std::mt19937;
using std::nullopt;
using std::optional;
using std::string;
using std::uniform_int_distribution;
using std::vector;

namespace
{
    // One random model, as data, so that it can be built again at each level.
    struct ElementSpec
    {
        int result;
        int first_index, second_index; // second_index < 0 for one dimension
        vector<vector<Integer>> table; // a single row for one dimension
    };

    struct ModelSpec
    {
        int n_indices, index_size;
        int n_results;
        vector<ElementSpec> elements;
        vector<std::pair<int, int>> results_equal_to_fresh; // (result, fresh variable)
        int n_fresh;
        vector<std::pair<int, int>> results_not_equal;
        vector<std::pair<int, int>> results_less_than;
        vector<int> results_all_different;
        vector<std::pair<int, int>> indices_not_equal;
        bool optimise;
    };

    auto random_model(mt19937 & rand) -> ModelSpec
    {
        auto pick = [&](int lo, int hi) { return uniform_int_distribution<int>{lo, hi}(rand); };
        auto chance = [&](int percent) { return pick(1, 100) <= percent; };

        ModelSpec m;
        m.n_indices = pick(2, 4);
        m.index_size = pick(2, 4);
        m.n_results = pick(2, 5);
        for (int r = 0; r < m.n_results; ++r) {
            ElementSpec e;
            e.result = r;
            e.first_index = pick(0, m.n_indices - 1);
            // Two dimensions sometimes, with the index repeated sometimes, as in
            // qap's D[x_i][x_i].
            e.second_index = chance(40) ? (chance(25) ? e.first_index : pick(0, m.n_indices - 1)) : -1;
            auto rows = e.second_index < 0 ? 1 : m.index_size;
            for (int row = 0; row < rows; ++row) {
                e.table.emplace_back();
                for (int col = 0; col < m.index_size; ++col)
                    e.table.back().push_back(Integer{pick(0, 6)});
            }
            m.elements.push_back(std::move(e));
        }

        m.n_fresh = 0;
        for (int r = 0; r < m.n_results; ++r)
            if (chance(30))
                m.results_equal_to_fresh.emplace_back(r, m.n_fresh++);
        for (int r = 0; r + 1 < m.n_results; ++r) {
            if (chance(25))
                m.results_not_equal.emplace_back(r, r + 1);
            if (chance(25))
                m.results_less_than.emplace_back(r, r + 1);
        }
        // An all-different over the results is the observer whose conclusions
        // most often move a bound when it can see holes (a Hall set among the
        // results' possible entries), so it is common here.
        if (chance(50))
            for (int r = 0; r < m.n_results; ++r)
                m.results_all_different.push_back(r);
        for (int i = 0; i + 1 < m.n_indices; ++i)
            if (chance(30))
                m.indices_not_equal.emplace_back(i, i + 1);
        m.optimise = chance(50);
        return m;
    }

    struct Outcome
    {
        unsigned long long recursions = 0, solutions = 0;
        optional<Integer> best;

        auto operator==(const Outcome &) const -> bool = default;
    };

    // How much propagating it took, which Auto must also match exactly when
    // every element runs the arm a forced level would.
    struct Counts
    {
        unsigned long long propagations = 0, effectful = 0;

        auto operator==(const Counts &) const -> bool = default;
    };

    auto build(const ModelSpec & m, const ElementConsistency & level, Problem & p, vector<IntegerVariableID> & branch_on)
        -> optional<IntegerVariableID>
    {
        vector<IntegerVariableID> indices, results, fresh;
        for (int i = 0; i < m.n_indices; ++i)
            indices.push_back(p.create_integer_variable(0_i, Integer{m.index_size - 1}));
        // Results range wider than any entry, so that holes matter.
        for (int r = 0; r < m.n_results; ++r)
            results.push_back(p.create_integer_variable(-1_i, 8_i));
        for (int f = 0; f < m.n_fresh; ++f)
            fresh.push_back(p.create_integer_variable(-1_i, 8_i));

        for (const auto & e : m.elements) {
            if (e.second_index < 0)
                p.post(ElementConstantArray{results[e.result], indices[e.first_index], e.table.at(0)}.with_consistency(level));
            else
                p.post(Element2DConstantArray{results[e.result], indices[e.first_index], indices[e.second_index], e.table}.with_consistency(level));
        }
        for (const auto & [r, f] : m.results_equal_to_fresh)
            p.post(Equals{results[r], fresh[f]});
        for (const auto & [a, b] : m.results_not_equal)
            p.post(NotEquals{results[a], results[b]});
        for (const auto & [a, b] : m.results_less_than)
            p.post(LessThan{results[a], results[b]});
        if (! m.results_all_different.empty()) {
            vector<IntegerVariableID> vars;
            for (auto r : m.results_all_different)
                vars.push_back(results[r]);
            p.post(AllDifferent{vars});
        }
        for (const auto & [a, b] : m.indices_not_equal)
            p.post(NotEquals{indices[a], indices[b]});

        // The fresh variables first: an equality passes a result's holes on to
        // them, so under BC the smallest value left can be one no entry
        // supplies, and trying it costs a node that GAC does not spend. That
        // is what makes BC's tree differ, and what Auto has to avoid.
        branch_on = fresh;
        branch_on.insert(branch_on.end(), indices.begin(), indices.end());

        if (! m.optimise)
            return nullopt;
        auto obj = p.create_integer_variable(-100_i, 100_i);
        WeightedSum sum;
        for (int r = 0; r < m.n_results; ++r)
            sum += Integer{r + 1} * results[r];
        p.post(std::move(sum) == 1_i * obj);
        p.minimise(obj);
        return obj;
    }

    auto solve_model(const ModelSpec & m, const ElementConsistency & level, const optional<string> & proof_name = nullopt, Counts * counts = nullptr)
        -> Outcome
    {
        Problem p;
        vector<IntegerVariableID> branch_on;
        auto obj = build(m, level, p, branch_on);

        Outcome outcome;
        auto stats = solve_with(p,
            SolveCallbacks{.solution = [&](const CurrentState & s) -> bool {
                               if (obj)
                                   outcome.best = s(*obj);
                               return true;
                           },
                // A brancher that reads only bounds: in order, and the
                // smallest value in then out, each a bound literal.
                .branch = branch_with(variable_order::in_order(branch_on), value_order::smallest_in()),
                .stats_report = silent_stats_report()},
            proof_name ? optional{ProofOptions{*proof_name}} : nullopt);
        outcome.recursions = stats.recursions;
        outcome.solutions = stats.solutions;
        if (counts)
            *counts = Counts{stats.propagations, stats.effectful_propagations};
        return outcome;
    }

    // How many optional prunings the solver would switch off for this model,
    // out of how many: what solve_with() decides, asked of the same installed
    // propagators.
    auto count_switched_off(const ModelSpec & m) -> std::pair<std::size_t, std::size_t>
    {
        Problem p;
        vector<IntegerVariableID> branch_on;
        build(m, consistency::Auto{}, p, branch_on);
        Stats stats;
        auto state = p.create_state_for_new_search(nullptr);
        auto propagators = p.create_propagators(state, stats, nullptr);
        auto verdicts = propagators.analyse_optional_interior_pruning();
        std::size_t off = 0;
        for (const auto & v : verdicts)
            if (! v.needed)
                ++off;
        return std::pair{off, verdicts.size()};
    }

    auto file_contents(const string & name) -> string
    {
        ifstream f{name};
        REQUIRE(f);
        return string{istreambuf_iterator<char>{f}, istreambuf_iterator<char>{}};
    }
}

TEST_CASE("Under a bounds-only brancher, Auto explores exactly the tree GAC does")
{
    unsigned long long some_switched_off = 0, bc_differs_from_gac = 0;
    for (unsigned seed = 0; seed < 2000; ++seed) {
        mt19937 rand{seed};
        auto m = random_model(rand);
        INFO("seed " << seed);

        Counts gac_counts, auto_counts, bc_counts;
        auto gac = solve_model(m, consistency::GAC{}, nullopt, &gac_counts);
        auto automatic = solve_model(m, consistency::Auto{}, nullopt, &auto_counts);
        CHECK(automatic == gac);

        // Where Auto chose the same arm for every element, it must also have
        // propagated exactly as that arm forced does, not just searched the
        // same tree.
        auto bc = solve_model(m, consistency::BC{}, nullopt, &bc_counts);
        auto [off, pairs] = count_switched_off(m);
        if (off == pairs)
            CHECK(auto_counts == bc_counts);
        else if (off == 0)
            CHECK(auto_counts == gac_counts);

        if (off > 0)
            ++some_switched_off;
        if (bc != gac)
            ++bc_differs_from_gac;
    }

    // Without these the comparison above could pass by never switching
    // anything off, or by never meeting a model where switching off the
    // wrong thing would show.
    INFO("switched something off in " << some_switched_off << ", BC differed from GAC in " << bc_differs_from_gac);
    CHECK(some_switched_off >= 500);
    CHECK(bc_differs_from_gac >= 15);
}

TEST_CASE("The choice of arm never changes the OPB encoding")
{
    // A model where Auto switches everything off, and one where it keeps a
    // pruning, so that both outcomes of the choice are compared.
    for (unsigned seed = 0; seed < 40; ++seed) {
        mt19937 rand{seed};
        auto m = random_model(rand);
        INFO("seed " << seed);

        vector<string> opbs;
        for (auto [label, level] : {std::pair{"gac", ElementConsistency{consistency::GAC{}}}, std::pair{"bc", ElementConsistency{consistency::BC{}}},
                 std::pair{"auto", ElementConsistency{consistency::Auto{}}}}) {
            auto name = string{"element_auto_test_"} + label;
            solve_model(m, level, name);
            opbs.push_back(file_contents(name + ".opb"));
            if (can_run_veripb())
                verify_proof_and_clean_up(name);
        }
        CHECK(opbs.at(0) == opbs.at(1));
        CHECK(opbs.at(0) == opbs.at(2));
    }
}

TEST_CASE("An AllDifferent keeps Auto's pruning on only at the level that reads holes")
{
    // An element's result is observed by nothing but an AllDifferent, so the
    // verdict is AllDifferent's own declaration: generalised arc consistency
    // reads interiors, and bounds consistency and value consistency do not.
    // Value consistency reads only which variables are fixed, and a hole is
    // never the last value to go; it used to share GAC's on_change triggers
    // and so declared otherwise (#992).
    for (auto [label, level, expect_needed] :
        {std::tuple{"gac", AllDifferentConsistency{consistency::GAC{}}, true}, std::tuple{"bc", AllDifferentConsistency{consistency::BC{}}, false},
            std::tuple{"vc", AllDifferentConsistency{consistency::VC{}}, false}}) {
        INFO(label);
        Problem p;
        auto idx = p.create_integer_variable(0_i, 3_i);
        auto result = p.create_integer_variable(-1_i, 8_i);
        auto other = p.create_integer_variable(-1_i, 8_i);
        p.post(ElementConstantArray{result, idx, vector<Integer>{1_i, 5_i, 2_i, 7_i}}.with_consistency(consistency::Auto{}));
        p.post(AllDifferent{vector<IntegerVariableID>{result, other}}.with_consistency(level));

        Stats stats;
        auto state = p.create_state_for_new_search(nullptr);
        auto propagators = p.create_propagators(state, stats, nullptr);
        auto verdicts = propagators.analyse_optional_interior_pruning();
        REQUIRE(verdicts.size() == 1);
        CHECK(verdicts.at(0).needed == expect_needed);
    }
}
