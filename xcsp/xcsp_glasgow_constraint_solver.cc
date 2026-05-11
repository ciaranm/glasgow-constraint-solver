#include <gcs/gcs.hh>
#include <gcs/innards/state.hh>
#include <util/enumerate.hh>

#include <XCSP3CoreParser.h>
#include <XCSP3Tree.h>
#include <XCSP3TreeNode.h>

#include <algorithm>
#include <atomic>
#include <chrono>
#include <condition_variable>
#include <csignal>
#include <cstdlib>
#include <iostream>
#include <map>
#include <memory>
#include <mutex>
#include <optional>
#include <set>
#include <string>
#include <thread>
#include <unordered_map>
#include <utility>
#include <vector>

#include <cxxopts.hpp>

using XCSP3Core::ExpressionObjective;
using XCSP3Core::ExpressionType;
using XCSP3Core::Node;
using XCSP3Core::NodeConstant;
using XCSP3Core::NodeVariable;
using XCSP3Core::OperandType;
using XCSP3Core::OrderType;
using XCSP3Core::RankType;
using XCSP3Core::Tree;
using XCSP3Core::XCondition;
using XCSP3Core::XCSP3CoreCallbacks;
using XCSP3Core::XCSP3CoreParser;
using XCSP3Core::XTransition;
using XCSP3Core::XVariable;

using namespace gcs;

using std::atomic;
using std::cerr;
using std::condition_variable;
using std::cout;
using std::cv_status;
using std::endl;
using std::make_optional;
using std::make_shared;
using std::map;
using std::max;
using std::min;
using std::minmax_element;
using std::mutex;
using std::nullopt;
using std::optional;
using std::set;
using std::shared_ptr;
using std::signal;
using std::stoll;
using std::string;
using std::thread;
using std::unique_lock;
using std::unordered_map;
using std::vector;

using std::chrono::duration_cast;
using std::chrono::microseconds;
using std::chrono::seconds;
using std::chrono::steady_clock;
using std::chrono::system_clock;

using namespace std::literals::string_literals;

namespace
{
    atomic<bool> abort_flag{false};
    atomic<bool> was_terminated{false};

    auto sig_int_or_term_handler(int) -> void
    {
        abort_flag.store(true);
        was_terminated.store(true);
    }

    // A variable as parsed from the XCSP3 instance. The IntegerVariableID is
    // created lazily on first use, so variables that are declared but never
    // referenced don't create unused state. `values` is set when the domain
    // is given as an explicit value list rather than a range.
    struct ManagedVariable
    {
        optional<IntegerVariableID> id;
        Integer lower;
        Integer upper;
        optional<vector<int>> values;
    };

    // The result of walking an intension expression: a variable holding the
    // expression's value, with the bounds we computed so callers can size
    // any further composition correctly.
    struct ExprResult
    {
        IntegerVariableID var;
        Integer lower;
        Integer upper;
    };

    [[noreturn]] auto report_unsupported(const string & constraint, const string & reason) -> void
    {
        throw UnimplementedException{"XCSP3 " + constraint + ": " + reason};
    }

    class XCSPCallbacks : public XCSP3CoreCallbacks
    {
    public:
        explicit XCSPCallbacks(Problem & p) :
            _problem(p)
        {
            intensionUsingString = false;
            recognizeSpecialIntensionCases = false;
            recognizeSpecialCountCases = true;
        }

        // Public so main() can read these after parsing.
        bool is_optimisation = false;
        optional<IntegerVariableID> objective_variable;

        auto variables() const -> const map<string, ManagedVariable> &
        {
            return _variables;
        }

        auto buildVariableInteger(string id, int min_value, int max_value) -> void override
        {
            _variables.emplace(id, ManagedVariable{nullopt, Integer{min_value}, Integer{max_value}, nullopt});
        }

        auto buildVariableInteger(string id, vector<int> & vals) -> void override
        {
            if (vals.empty())
                report_unsupported("variable " + id, "empty value list");
            auto [lo, hi] = minmax_element(vals.begin(), vals.end());
            _variables.emplace(id, ManagedVariable{nullopt, Integer{*lo}, Integer{*hi}, vals});
        }

        auto buildConstraintExtension(string, vector<XVariable *> x_vars, vector<vector<int>> & x_tuples,
            bool is_support, bool) -> void override
        {
            auto vars = need_variables(x_vars);
            _most_recent_tuples = make_shared<WildcardTuples>();
            for (auto & t : x_tuples) {
                vector<IntegerOrWildcard> tuple;
                for (auto & v : t)
                    if (v == STAR)
                        tuple.emplace_back(Wildcard{});
                    else
                        tuple.emplace_back(Integer{v});
                _most_recent_tuples->emplace_back(std::move(tuple));
            }
            post_table(vars, is_support);
        }

        auto buildConstraintExtensionAs(string, vector<XVariable *> x_vars, bool is_support, bool) -> void override
        {
            post_table(need_variables(x_vars), is_support);
        }

        auto buildConstraintExtension(string, XVariable * x_var, vector<int> & x_tuples,
            bool is_support, bool) -> void override
        {
            vector<IntegerVariableID> vars{need_variable(x_var->id)};
            _most_recent_tuples = make_shared<WildcardTuples>();
            for (auto & t : x_tuples) {
                vector<IntegerOrWildcard> tuple;
                if (t == STAR)
                    tuple.emplace_back(Wildcard{});
                else
                    tuple.emplace_back(Integer{t});
                _most_recent_tuples->emplace_back(std::move(tuple));
            }
            post_table(vars, is_support);
        }

        auto buildConstraintAlldifferent(string, vector<XVariable *> & x_vars) -> void override
        {
            _problem.post(AllDifferent{need_variables(x_vars)});
        }

        auto buildConstraintAlldifferentMatrix(string,
            vector<vector<XVariable *>> & matrix) -> void override
        {
            if (matrix.empty())
                return;
            // Rows: each row's vars are pairwise distinct.
            vector<vector<IntegerVariableID>> rows;
            rows.reserve(matrix.size());
            for (auto & r : matrix) {
                rows.emplace_back(need_variables(r));
                _problem.post(AllDifferent{rows.back()});
            }
            // Columns: each column's vars are pairwise distinct.
            auto ncols = matrix[0].size();
            for (size_t c = 0; c < ncols; ++c) {
                vector<IntegerVariableID> col;
                col.reserve(rows.size());
                for (auto & r : rows)
                    col.emplace_back(r[c]);
                _problem.post(AllDifferent{col});
            }
        }

        auto buildConstraintLex(string, vector<vector<XVariable *>> & lists,
            OrderType order) -> void override
        {
            if (lists.size() < 2)
                return;
            vector<vector<IntegerVariableID>> ilists;
            ilists.reserve(lists.size());
            for (auto & l : lists)
                ilists.emplace_back(need_variables(l));
            for (size_t i = 0; i + 1 < ilists.size(); ++i)
                post_lex_pair(ilists[i], ilists[i + 1], order);
        }

        auto buildConstraintLexMatrix(string, vector<vector<XVariable *>> & matrix,
            OrderType order) -> void override
        {
            if (matrix.empty())
                return;
            vector<vector<IntegerVariableID>> rows;
            rows.reserve(matrix.size());
            for (auto & r : matrix)
                rows.emplace_back(need_variables(r));
            // Each consecutive row pair lex-ordered.
            for (size_t i = 0; i + 1 < rows.size(); ++i)
                post_lex_pair(rows[i], rows[i + 1], order);
            // Each consecutive column pair lex-ordered.
            if (rows[0].empty())
                return;
            auto ncols = rows[0].size();
            for (size_t c = 0; c + 1 < ncols; ++c) {
                vector<IntegerVariableID> col1, col2;
                col1.reserve(rows.size());
                col2.reserve(rows.size());
                for (auto & r : rows) {
                    col1.emplace_back(r[c]);
                    col2.emplace_back(r[c + 1]);
                }
                post_lex_pair(col1, col2, order);
            }
        }

        auto buildConstraintAllEqual(string, vector<XVariable *> & x_vars) -> void override
        {
            _problem.post(AllEqual{need_variables(x_vars)});
        }

        auto buildConstraintOrdered(string, vector<XVariable *> & x_vars,
            OrderType order) -> void override
        {
            auto vars = need_variables(x_vars);
            switch (order) {
                using enum OrderType;
            case LE:
                _problem.post(Increasing{vars});
                break;
            case LT:
                _problem.post(StrictlyIncreasing{vars});
                break;
            case GE:
                _problem.post(Decreasing{vars});
                break;
            case GT:
                _problem.post(StrictlyDecreasing{vars});
                break;
            case EQ:
            case NE:
            case IN:
            case NOTIN:
                report_unsupported("ordered", "non-ordering order type");
            }
        }

        auto buildConstraintOrdered(string, vector<XVariable *> & x_vars,
            vector<int> & lengths, OrderType order) -> void override
        {
            auto vars = need_variables(x_vars);
            if (lengths.size() + 1 != vars.size())
                report_unsupported("ordered", "lengths size must be |vars| - 1");
            for (size_t i = 0; i + 1 < vars.size(); ++i) {
                auto len = Integer{lengths[i]};
                switch (order) {
                    using enum OrderType;
                case LE:
                    // vars[i] + len <= vars[i+1]
                    _problem.post(WeightedSum{} + 1_i * vars[i] + -1_i * vars[i + 1] <= -len);
                    break;
                case LT:
                    _problem.post(WeightedSum{} + 1_i * vars[i] + -1_i * vars[i + 1] <= -len - 1_i);
                    break;
                case GE:
                    // vars[i] + len >= vars[i+1]
                    _problem.post(WeightedSum{} + -1_i * vars[i] + 1_i * vars[i + 1] <= len);
                    break;
                case GT:
                    _problem.post(WeightedSum{} + -1_i * vars[i] + 1_i * vars[i + 1] <= len - 1_i);
                    break;
                case EQ:
                case NE:
                case IN:
                case NOTIN:
                    report_unsupported("ordered", "non-ordering order type");
                }
            }
        }

        auto buildConstraintPrecedence(string, vector<XVariable *> & x_vars, bool) -> void override
        {
            // The form without an explicit value list requires us to derive
            // the value chain from the union of vars' domains; not yet
            // implemented (issue #150 phase 2b).
            (void)x_vars;
            report_unsupported("precedence", "without explicit value list");
        }

        auto buildConstraintPrecedence(string, vector<XVariable *> & x_vars,
            vector<int> values, bool covered) -> void override
        {
            if (covered)
                report_unsupported("precedence", "covered=true");
            auto vars = need_variables(x_vars);
            vector<Integer> chain;
            chain.reserve(values.size());
            for (auto v : values)
                chain.emplace_back(Integer{v});
            _problem.post(ValuePrecede{std::move(chain), vars});
        }

        auto buildConstraintSum(string, vector<XVariable *> & x_vars, vector<int> & coeffs,
            XCondition & cond) -> void override
        {
            build_sum_common(x_vars, coeffs, cond);
        }

        auto buildConstraintSum(string, vector<XVariable *> & x_vars, XCondition & cond) -> void override
        {
            build_sum_common(x_vars, nullopt, cond);
        }

        auto buildConstraintCount(string, vector<XVariable *> & x_vars, vector<int> & values,
            XCondition & cond) -> void override
        {
            auto vars = need_variables(x_vars);
            auto how_many = _problem.create_integer_variable(0_i,
                Integer{static_cast<long long>(vars.size())}, "countresult");
            if (values.size() == 1)
                _problem.post(Count{vars, constant_variable(Integer{values[0]}), how_many});
            else {
                vector<Integer> ivals;
                ivals.reserve(values.size());
                for (auto v : values)
                    ivals.emplace_back(Integer{v});
                _problem.post(Among{vars, ivals, how_many});
            }
            apply_count_condition(how_many, cond, "count");
        }

        auto buildConstraintAmong(string, vector<XVariable *> & x_vars,
            vector<int> & values, int k) -> void override
        {
            auto vars = need_variables(x_vars);
            auto how_many = _problem.create_integer_variable(Integer{k}, Integer{k}, "amongresult");
            vector<Integer> ivals;
            ivals.reserve(values.size());
            for (auto v : values)
                ivals.emplace_back(Integer{v});
            _problem.post(Among{vars, ivals, how_many});
        }

        auto buildConstraintAtMost(string, vector<XVariable *> & x_vars,
            int value, int k) -> void override
        {
            auto vars = need_variables(x_vars);
            auto how_many = _problem.create_integer_variable(0_i, Integer{k}, "atmost");
            _problem.post(Count{vars, constant_variable(Integer{value}), how_many});
        }

        auto buildConstraintAtLeast(string, vector<XVariable *> & x_vars,
            int value, int k) -> void override
        {
            auto vars = need_variables(x_vars);
            auto how_many = _problem.create_integer_variable(Integer{k},
                Integer{static_cast<long long>(vars.size())}, "atleast");
            _problem.post(Count{vars, constant_variable(Integer{value}), how_many});
        }

        auto buildConstraintExactlyK(string, vector<XVariable *> & x_vars,
            int value, int k) -> void override
        {
            auto vars = need_variables(x_vars);
            auto how_many = _problem.create_integer_variable(Integer{k}, Integer{k}, "exactlyk");
            _problem.post(Count{vars, constant_variable(Integer{value}), how_many});
        }

        auto buildConstraintExactlyVariable(string, vector<XVariable *> & x_vars,
            int value, XVariable * x) -> void override
        {
            auto vars = need_variables(x_vars);
            _problem.post(Count{vars, constant_variable(Integer{value}), need_variable(x->id)});
        }

        auto buildConstraintNValues(string, vector<XVariable *> & x_vars,
            XCondition & cond) -> void override
        {
            auto vars = need_variables(x_vars);
            auto n_values = _problem.create_integer_variable(1_i,
                Integer{static_cast<long long>(vars.size())}, "nvalues");
            _problem.post(NValue{n_values, vars});
            apply_count_condition(n_values, cond, "nValues");
        }

        auto buildConstraintRegular(string, vector<XVariable *> & x_vars,
            string start, vector<string> & final, vector<XTransition> & transitions) -> void override
        {
            auto vars = need_variables(x_vars);

            // Map state names to integers; the start state gets 0.
            map<string, long> state_idx;
            state_idx.emplace(start, 0);
            auto get_state = [&](const string & name) -> long {
                auto it = state_idx.find(name);
                if (it != state_idx.end())
                    return it->second;
                long idx = static_cast<long>(state_idx.size());
                state_idx.emplace(name, idx);
                return idx;
            };

            vector<unordered_map<Integer, long>> trans_table;
            for (const auto & t : transitions) {
                long from_idx = get_state(t.from);
                long to_idx = get_state(t.to);
                if (static_cast<size_t>(from_idx) >= trans_table.size())
                    trans_table.resize(from_idx + 1);
                trans_table[from_idx].emplace(Integer{t.val}, to_idx);
            }

            vector<long> finals;
            finals.reserve(final.size());
            for (const auto & name : final)
                finals.emplace_back(get_state(name));

            auto num_states = static_cast<long>(state_idx.size());
            if (static_cast<long>(trans_table.size()) < num_states)
                trans_table.resize(num_states);

            _problem.post(Regular{vars, num_states, std::move(trans_table), std::move(finals)});
        }

        // Solver gaps: each XCSP3 constraint family below maps to a missing
        // gcs propagator. Override the parser's default (which throws an
        // uncaught runtime_error) with our standard report_unsupported so
        // main() emits a clean s UNSUPPORTED.

        auto buildConstraintMDD(string, vector<XVariable *> &,
            vector<XTransition> &) -> void override
        {
            report_unsupported("mdd", "no MDD propagator yet (#149)");
        }

        auto buildConstraintNoOverlap(string, vector<XVariable *> &,
            vector<int> &, bool) -> void override
        {
            report_unsupported("noOverlap", "no Disjunctive propagator yet (#146)");
        }

        auto buildConstraintNoOverlap(string, vector<XVariable *> &,
            vector<XVariable *> &, bool) -> void override
        {
            report_unsupported("noOverlap", "no Disjunctive propagator yet (#146)");
        }

        auto buildConstraintNoOverlap(string, vector<vector<XVariable *>> &,
            vector<vector<int>> &, bool) -> void override
        {
            report_unsupported("noOverlap", "no Disjunctive2D propagator yet (#146)");
        }

        auto buildConstraintNoOverlap(string, vector<vector<XVariable *>> &,
            vector<vector<XVariable *>> &, bool) -> void override
        {
            report_unsupported("noOverlap", "no Disjunctive2D propagator yet (#146)");
        }

        auto buildConstraintCumulative(string, vector<XVariable *> & origins,
            vector<int> & lengths, vector<int> & heights, XCondition & cond) -> void override
        {
            if (cond.op != OrderType::LE)
                report_unsupported("cumulative", "only `le` condition is supported in this basic case (#147)");
            if (cond.operandType != OperandType::INTEGER)
                report_unsupported("cumulative", "only integer-constant capacity is supported in this basic case (#147)");

            auto starts = need_variables(origins);
            vector<Integer> lengths_i, heights_i;
            for (auto l : lengths)
                lengths_i.push_back(Integer{l});
            for (auto h : heights)
                heights_i.push_back(Integer{h});
            _problem.post(Cumulative{starts, lengths_i, heights_i, Integer{cond.val}});
        }

        auto buildConstraintCumulative(string, vector<XVariable *> &,
            vector<int> &, vector<XVariable *> &, XCondition &) -> void override
        {
            report_unsupported("cumulative", "no Cumulative propagator yet (#147)");
        }

        auto buildConstraintCumulative(string, vector<XVariable *> &,
            vector<XVariable *> &, vector<int> &, XCondition &) -> void override
        {
            report_unsupported("cumulative", "no Cumulative propagator yet (#147)");
        }

        auto buildConstraintBinPacking(string, vector<XVariable *> &, vector<int> &,
            XCondition &) -> void override
        {
            report_unsupported("binPacking", "no BinPacking propagator yet (#148)");
        }

        auto buildConstraintBinPacking(string, vector<XVariable *> &, vector<int> &,
            vector<int> &, bool) -> void override
        {
            report_unsupported("binPacking", "no BinPacking propagator yet (#148)");
        }

        auto buildConstraintBinPacking(string, vector<XVariable *> &, vector<int> &,
            vector<XVariable *> &, bool) -> void override
        {
            report_unsupported("binPacking", "no BinPacking propagator yet (#148)");
        }

        auto buildConstraintBinPacking(string, vector<XVariable *> &, vector<int> &,
            vector<XCondition> &, int) -> void override
        {
            report_unsupported("binPacking", "no BinPacking propagator yet (#148)");
        }

        auto buildConstraintCircuit(string, vector<XVariable *> & x_vars,
            int startIndex) -> void override
        {
            if (startIndex != 0)
                report_unsupported("circuit", "non-zero startIndex");
            _problem.post(Circuit{need_variables(x_vars)});
        }

        auto buildConstraintCircuit(string, vector<XVariable *> & x_vars,
            int startIndex, int size) -> void override
        {
            (void)x_vars;
            (void)startIndex;
            (void)size;
            report_unsupported("circuit", "fixed-size sub-circuit");
        }

        auto buildConstraintCircuit(string, vector<XVariable *> & x_vars,
            int startIndex, XVariable * size) -> void override
        {
            (void)x_vars;
            (void)startIndex;
            (void)size;
            report_unsupported("circuit", "variable-size sub-circuit");
        }

        auto buildConstraintInstantiation(string, vector<XVariable *> & x_vars,
            vector<int> & values) -> void override
        {
            if (x_vars.size() != values.size())
                report_unsupported("instantiation", "vars/values size mismatch");
            for (size_t i = 0; i != x_vars.size(); ++i)
                _problem.post(Equals{need_variable(x_vars[i]->id),
                    constant_variable(Integer{values[i]})});
        }

        auto buildConstraintKnapsack(string, vector<XVariable *> & x_vars,
            vector<int> & weights, vector<int> & profits,
            XCondition weightCondition, XCondition & profitCondition) -> void override
        {
            if (x_vars.size() != weights.size() || x_vars.size() != profits.size())
                report_unsupported("knapsack", "vars/weights/profits size mismatch");
            auto vars = need_variables(x_vars);
            vector<Integer> ws, ps;
            ws.reserve(weights.size());
            ps.reserve(profits.size());
            Integer wmin = 0_i, wmax = 0_i, pmin = 0_i, pmax = 0_i;
            for (size_t i = 0; i != weights.size(); ++i) {
                ws.emplace_back(Integer{weights[i]});
                ps.emplace_back(Integer{profits[i]});
                auto & mv = find_variable(x_vars[i]->id);
                // Vars are typically 0..1 indicators; bound by var range.
                wmin += min(Integer{weights[i]} * mv.lower, Integer{weights[i]} * mv.upper);
                wmax += max(Integer{weights[i]} * mv.lower, Integer{weights[i]} * mv.upper);
                pmin += min(Integer{profits[i]} * mv.lower, Integer{profits[i]} * mv.upper);
                pmax += max(Integer{profits[i]} * mv.lower, Integer{profits[i]} * mv.upper);
            }
            auto weight_total = _problem.create_integer_variable(wmin, wmax, "knap_weight");
            auto profit_total = _problem.create_integer_variable(pmin, pmax, "knap_profit");
            _problem.post(Knapsack{std::move(ws), std::move(ps), vars, weight_total, profit_total});
            apply_count_condition(weight_total, weightCondition, "knapsack weight");
            apply_count_condition(profit_total, profitCondition, "knapsack profit");
        }

        auto buildConstraintCardinality(string, vector<XVariable *> & x_vars,
            vector<int> values, vector<int> & occurs, bool closed) -> void override
        {
            // Decomposition: one Count per (value, occurrence) pair. A
            // native GCC propagator would be a future improvement (see the
            // CPMpy globals list in #61).
            if (values.size() != occurs.size())
                report_unsupported("cardinality", "values/occurs size mismatch");
            auto vars = need_variables(x_vars);
            for (size_t i = 0; i != values.size(); ++i)
                _problem.post(Count{vars, constant_variable(Integer{values[i]}),
                    constant_variable(Integer{occurs[i]})});
            if (closed) {
                // Every var must take a value from the given list.
                vector<Integer> ivals;
                ivals.reserve(values.size());
                for (auto v : values)
                    ivals.emplace_back(Integer{v});
                vector<vector<Integer>> tuples;
                tuples.reserve(ivals.size());
                for (auto v : ivals)
                    tuples.emplace_back(vector{v});
                for (auto v : vars)
                    _problem.post(Table{vector<IntegerVariableID>{v}, tuples});
            }
        }

        auto buildConstraintIntension(string, Tree * tree) -> void override
        {
            post_intension_top_level(tree->root);
        }

        auto buildConstraintElement(string, vector<XVariable *> & x_vars,
            int startIndex, XVariable * index, RankType rank, int value) -> void override
        {
            check_element_rank(rank);
            auto idx = zero_based_index(index, startIndex);
            _problem.post(Element{constant_variable(Integer{value}), idx, allocate_element_array(x_vars)});
        }

        auto buildConstraintElement(string, vector<int> & vals,
            int startIndex, XVariable * index, RankType rank, XVariable * value) -> void override
        {
            check_element_rank(rank);
            auto idx = zero_based_index(index, startIndex);
            auto val = need_variable(value->id);
            _problem.post(Element{val, idx, allocate_element_array(vals)});
        }

        auto buildConstraintElement(string, vector<vector<XVariable *>> & matrix,
            int startRowIndex, XVariable * rowIndex, int startColIndex, XVariable * colIndex,
            XVariable * value) -> void override
        {
            auto val = need_variable(value->id);
            auto row = need_variable(rowIndex->id);
            auto col = need_variable(colIndex->id);
            _problem.post(Element2D{val,
                {row, Integer{startRowIndex}}, {col, Integer{startColIndex}},
                allocate_element_matrix(matrix)});
        }

        auto buildConstraintElement(string, vector<vector<XVariable *>> & matrix,
            int startRowIndex, XVariable * rowIndex, int startColIndex, XVariable * colIndex,
            int value) -> void override
        {
            auto row = need_variable(rowIndex->id);
            auto col = need_variable(colIndex->id);
            _problem.post(Element2D{constant_variable(Integer{value}),
                {row, Integer{startRowIndex}}, {col, Integer{startColIndex}},
                allocate_element_matrix(matrix)});
        }

        auto buildConstraintElement(string, vector<vector<int>> & matrix,
            int startRowIndex, XVariable * rowIndex, int startColIndex, XVariable * colIndex,
            XVariable * value) -> void override
        {
            auto val = need_variable(value->id);
            auto row = need_variable(rowIndex->id);
            auto col = need_variable(colIndex->id);
            _problem.post(Element2DConstantArray{val,
                {row, Integer{startRowIndex}}, {col, Integer{startColIndex}},
                allocate_element_matrix(matrix)});
        }

        auto buildConstraintMinimum(string, vector<XVariable *> & x_vars,
            XCondition & cond) -> void override
        {
            build_min_max_common(x_vars, cond, true);
        }

        auto buildConstraintMaximum(string, vector<XVariable *> & x_vars,
            XCondition & cond) -> void override
        {
            build_min_max_common(x_vars, cond, false);
        }

        auto buildConstraintChannel(string, vector<XVariable *> & x_vars,
            int startIndex) -> void override
        {
            auto vars = need_variables(x_vars);
            _problem.post(Inverse{vars, vars, Integer{startIndex}, Integer{startIndex}});
        }

        auto buildConstraintChannel(string, vector<XVariable *> & list1, int startIndex1,
            vector<XVariable *> & list2, int startIndex2) -> void override
        {
            _problem.post(Inverse{need_variables(list1), need_variables(list2),
                Integer{startIndex1}, Integer{startIndex2}});
        }

        auto buildConstraintChannel(string, vector<XVariable *> & list,
            int startIndex, XVariable * value) -> void override
        {
            // One-to-many channeling: list[i] = 1 ⇔ value = i + startIndex.
            // Not yet implemented; needs an EqualsIff chain or a custom
            // decomposition.
            (void)list;
            (void)startIndex;
            (void)value;
            report_unsupported("channel", "one-to-many form (list + value)");
        }

        auto buildObjectiveMinimize(ExpressionObjective type, vector<XVariable *> & x_vars,
            vector<int> & coeffs) -> void override
        {
            build_objective_common(type, x_vars, coeffs, false);
        }

        auto buildObjectiveMaximize(ExpressionObjective type, vector<XVariable *> & x_vars,
            vector<int> & coeffs) -> void override
        {
            build_objective_common(type, x_vars, coeffs, true);
        }

        auto buildObjectiveMinimize(ExpressionObjective type,
            vector<XVariable *> & x_vars) -> void override
        {
            vector<int> coefs(x_vars.size(), 1);
            build_objective_common(type, x_vars, coefs, false);
        }

        auto buildObjectiveMaximize(ExpressionObjective type,
            vector<XVariable *> & x_vars) -> void override
        {
            vector<int> coefs(x_vars.size(), 1);
            build_objective_common(type, x_vars, coefs, true);
        }

        auto buildObjectiveMinimizeVariable(XVariable * x) -> void override
        {
            is_optimisation = true;
            auto var = need_variable(x->id);
            objective_variable = var;
            _problem.minimise(var);
        }

        auto buildObjectiveMaximizeVariable(XVariable * x) -> void override
        {
            is_optimisation = true;
            auto var = need_variable(x->id);
            objective_variable = var;
            _problem.maximise(var);
        }

    private:
        Problem & _problem;
        map<string, ManagedVariable> _variables;
        shared_ptr<WildcardTuples> _most_recent_tuples;
        // Storage for the variable arrays passed to Element. The Element
        // constraint takes a raw pointer to the array and keeps it through
        // its clone(), so the storage must outlive the Problem. We hold it
        // in the callbacks object, which itself lives in main() alongside
        // the Problem.
        vector<std::unique_ptr<vector<IntegerVariableID>>> _element_arrays;
        vector<std::unique_ptr<vector<vector<IntegerVariableID>>>> _element_2d_var_arrays;
        vector<std::unique_ptr<vector<vector<Integer>>>> _element_2d_const_arrays;

        // Variable lookup helpers. need_variable() lazily creates the
        // IntegerVariableID on first use.

        auto need_variable(const string & name) -> IntegerVariableID
        {
            auto m = _variables.find(name);
            if (m == _variables.end())
                report_unsupported("intension", "no mapping for variable '" + name + "'");
            auto & v = m->second;
            if (! v.id) {
                if (v.values) {
                    vector<Integer> vals;
                    vals.reserve(v.values->size());
                    for (auto & x : *v.values)
                        vals.emplace_back(Integer{x});
                    v.id = _problem.create_integer_variable(vals, name);
                }
                else
                    v.id = _problem.create_integer_variable(v.lower, v.upper, name);
            }
            return *v.id;
        }

        auto find_variable(const string & name) -> ManagedVariable &
        {
            auto m = _variables.find(name);
            if (m == _variables.end())
                report_unsupported("intension", "no mapping for variable '" + name + "'");
            return m->second;
        }

        auto need_variables(const vector<XVariable *> & x_vars) -> vector<IntegerVariableID>
        {
            vector<IntegerVariableID> result;
            result.reserve(x_vars.size());
            for (auto & v : x_vars)
                result.emplace_back(need_variable(v->id));
            return result;
        }

        auto allocate_element_array(vector<XVariable *> & x_vars) -> vector<IntegerVariableID> *
        {
            auto vars = std::make_unique<vector<IntegerVariableID>>();
            vars->reserve(x_vars.size());
            for (auto & v : x_vars)
                vars->emplace_back(need_variable(v->id));
            auto * raw = vars.get();
            _element_arrays.push_back(std::move(vars));
            return raw;
        }

        auto allocate_element_array(vector<int> & vals) -> vector<IntegerVariableID> *
        {
            auto vars = std::make_unique<vector<IntegerVariableID>>();
            vars->reserve(vals.size());
            for (auto & v : vals)
                vars->emplace_back(constant_variable(Integer{v}));
            auto * raw = vars.get();
            _element_arrays.push_back(std::move(vars));
            return raw;
        }

        auto allocate_element_matrix(vector<vector<XVariable *>> & matrix) -> vector<vector<IntegerVariableID>> *
        {
            auto rows = std::make_unique<vector<vector<IntegerVariableID>>>();
            rows->reserve(matrix.size());
            for (auto & row : matrix) {
                vector<IntegerVariableID> r;
                r.reserve(row.size());
                for (auto * v : row)
                    r.emplace_back(need_variable(v->id));
                rows->emplace_back(std::move(r));
            }
            auto * raw = rows.get();
            _element_2d_var_arrays.push_back(std::move(rows));
            return raw;
        }

        auto allocate_element_matrix(vector<vector<int>> & matrix) -> vector<vector<Integer>> *
        {
            auto rows = std::make_unique<vector<vector<Integer>>>();
            rows->reserve(matrix.size());
            for (auto & row : matrix) {
                vector<Integer> r;
                r.reserve(row.size());
                for (auto & v : row)
                    r.emplace_back(Integer{v});
                rows->emplace_back(std::move(r));
            }
            auto * raw = rows.get();
            _element_2d_const_arrays.push_back(std::move(rows));
            return raw;
        }

        // Shift an index variable by -startIndex, returning a fresh
        // 0-based variable. Used by 1D Element where the Element wrapper
        // doesn't expose the start-index parameter directly.
        auto zero_based_index(XVariable * x, int startIndex) -> IntegerVariableID
        {
            auto idx = need_variable(x->id);
            if (startIndex == 0)
                return idx;
            auto & mv = find_variable(x->id);
            auto shifted = _problem.create_integer_variable(
                mv.lower - Integer{startIndex}, mv.upper - Integer{startIndex}, "idx_shifted");
            _problem.post(WeightedSum{} + 1_i * idx + -1_i * shifted == Integer{startIndex});
            return shifted;
        }

        auto post_table(const vector<IntegerVariableID> & vars, bool is_support) -> void
        {
            if (is_support)
                _problem.post(Table{vars, SharedWildcardTuples{_most_recent_tuples}});
            else
                _problem.post(NegativeTable{vars, SharedWildcardTuples{_most_recent_tuples}});
        }

        auto check_element_rank(RankType rank) -> void
        {
            if (rank != RankType::ANY)
                report_unsupported("element", "non-any rank");
        }

        auto post_lex_pair(const vector<IntegerVariableID> & a,
            const vector<IntegerVariableID> & b, OrderType order) -> void
        {
            switch (order) {
                using enum OrderType;
            case LT:
                _problem.post(LexLessThan{a, b});
                break;
            case LE:
                _problem.post(LexLessThanEqual{a, b});
                break;
            case GT:
                _problem.post(LexGreaterThan{a, b});
                break;
            case GE:
                _problem.post(LexGreaterEqual{a, b});
                break;
            case EQ:
            case NE:
            case IN:
            case NOTIN:
                report_unsupported("lex", "non-ordering order type");
            }
        }

        auto build_min_max_common(vector<XVariable *> & x_vars, XCondition & cond,
            bool is_min) -> void
        {
            optional<Integer> lower, upper;
            vector<IntegerVariableID> vars;
            vars.reserve(x_vars.size());
            for (auto * x : x_vars) {
                auto & mv = find_variable(x->id);
                vars.emplace_back(need_variable(x->id));
                lower = lower ? min(*lower, mv.lower) : mv.lower;
                upper = upper ? max(*upper, mv.upper) : mv.upper;
            }
            auto result = _problem.create_integer_variable(*lower, *upper,
                is_min ? "minresult" : "maxresult");
            if (is_min)
                _problem.post(ArrayMin{vars, result});
            else
                _problem.post(ArrayMax{vars, result});
            apply_count_condition(result, cond, is_min ? "minimum" : "maximum");
        }

        // Apply a count-style XCondition to a single result variable:
        // posts `result <op> rhs` directly, where rhs is either a variable
        // or a constant. Used by count, nValues, etc.
        auto apply_count_condition(IntegerVariableID result, XCondition & xc,
            const string & ctx) -> void
        {
            IntegerVariableID rhs = constant_variable(0_i);
            switch (xc.operandType) {
                using enum OperandType;
            case VARIABLE:
                rhs = need_variable(xc.var);
                break;
            case INTEGER:
                rhs = constant_variable(Integer{xc.val});
                break;
            case INTERVAL:
                _problem.post(WeightedSum{} + 1_i * result >= Integer{xc.min});
                _problem.post(WeightedSum{} + 1_i * result <= Integer{xc.max});
                return;
            case SET:
                report_unsupported(ctx, "set condition");
            }

            switch (xc.op) {
                using enum OrderType;
            case LE:
                _problem.post(LessThanEqual{result, rhs});
                break;
            case LT:
                _problem.post(LessThan{result, rhs});
                break;
            case EQ:
                _problem.post(Equals{result, rhs});
                break;
            case GT:
                _problem.post(GreaterThan{result, rhs});
                break;
            case GE:
                _problem.post(GreaterThanEqual{result, rhs});
                break;
            case NE:
                _problem.post(NotEquals{result, rhs});
                break;
            case IN:
            case NOTIN:
                report_unsupported(ctx, "set membership condition");
            }
        }

        auto build_sum_common(vector<XVariable *> & x_vars, const optional<vector<int>> & coeffs,
            XCondition & cond) -> void
        {
            WeightedSum cvs;
            Integer range = 0_i;
            for (const auto & [idx, x] : enumerate(x_vars)) {
                auto & mv = find_variable(x->id);
                auto var = need_variable(x->id);
                auto coeff = coeffs ? Integer{coeffs->at(idx)} : 1_i;
                cvs += coeff * var;
                range += abs(coeff) * max(abs(mv.lower), abs(mv.upper));
            }

            Integer bound = 0_i;
            switch (cond.operandType) {
                using enum OperandType;
            case VARIABLE:
                cvs += -1_i * need_variable(cond.var);
                break;
            case INTEGER:
                bound = Integer{cond.val};
                break;
            case INTERVAL:
                report_unsupported("sum", "interval condition");
            case SET:
                report_unsupported("sum", "set condition");
            }

            switch (cond.op) {
                using enum OrderType;
            case LE:
                _problem.post(std::move(cvs) <= bound);
                break;
            case LT:
                _problem.post(std::move(cvs) <= bound - 1_i);
                break;
            case EQ:
                _problem.post(std::move(cvs) == bound);
                break;
            case GT:
                _problem.post(std::move(cvs) >= bound + 1_i);
                break;
            case GE:
                _problem.post(std::move(cvs) >= bound);
                break;
            case NE: {
                auto diff = _problem.create_integer_variable(-range, range, "ne");
                cvs += 1_i * diff;
                _problem.post(std::move(cvs) == bound);
                _problem.post(NotEquals{diff, 0_c});
            } break;
            case IN:
            case NOTIN:
                report_unsupported("sum", "set membership condition");
            }
        }

        auto build_objective_common(ExpressionObjective type, vector<XVariable *> & x_vars,
            vector<int> & coeffs, bool is_max) -> void
        {
            is_optimisation = true;

            if (type == ExpressionObjective::MINIMUM_O || type == ExpressionObjective::MAXIMUM_O) {
                optional<Integer> lower, upper;
                vector<IntegerVariableID> vars;
                vars.reserve(x_vars.size());
                for (auto & x : x_vars) {
                    auto & mv = find_variable(x->id);
                    vars.emplace_back(need_variable(x->id));
                    lower = lower ? min(*lower, mv.lower) : mv.lower;
                    upper = upper ? max(*upper, mv.upper) : mv.upper;
                }

                auto obj = _problem.create_integer_variable(*lower, *upper, "objective");
                objective_variable = obj;
                if (type == ExpressionObjective::MINIMUM_O)
                    _problem.post(ArrayMin{vars, obj});
                else
                    _problem.post(ArrayMax{vars, obj});

                if (is_max)
                    _problem.maximise(obj);
                else
                    _problem.minimise(obj);
            }
            else if (type == ExpressionObjective::SUM_O) {
                Integer lower = 0_i, upper = 0_i;
                WeightedSum cvs;
                for (const auto & [idx, x] : enumerate(x_vars)) {
                    auto & mv = find_variable(x->id);
                    auto coeff = Integer{coeffs.at(idx)};
                    cvs += coeff * need_variable(x->id);
                    if (coeff < 0_i) {
                        lower += coeff * mv.upper;
                        upper += coeff * mv.lower;
                    }
                    else {
                        lower += coeff * mv.lower;
                        upper += coeff * mv.upper;
                    }
                }

                auto obj = _problem.create_integer_variable(lower, upper, "objective");
                objective_variable = obj;
                _problem.post(std::move(cvs) == 1_i * obj);
                if (is_max)
                    _problem.maximise(obj);
                else
                    _problem.minimise(obj);
            }
            else
                report_unsupported("objective", "expression form not implemented");
        }

        // -------- intension tree walking --------

        // Helper for binary relational operators inside an expression: walks
        // both children and posts the corresponding *Iff reification with
        // a fresh 0/1 control variable.
        template <typename Constraint_>
        auto reify_binary(Node * node, const string & name) -> ExprResult
        {
            auto a = walk_intension(node->parameters.at(0));
            auto b = walk_intension(node->parameters.at(1));
            auto control = _problem.create_integer_variable(0_i, 1_i, name);
            _problem.post(Constraint_{a.var, b.var, control == 1_i});
            return {control, 0_i, 1_i};
        }

        // Multiply two ExprResults via Times (or WeightedSum if either side
        // is a constant). Used by binary and n-ary OMUL, OSQR, and OPOW.
        // The constant-folding in this helper is a workaround for #153 —
        // ideally the user-facing Times constraint would do it itself and
        // also choose between the GAC and BC implementations based on
        // domain widths.
        auto post_product(ExprResult a, ExprResult b, const string & name) -> ExprResult
        {
            auto lower = min({a.lower * b.lower, a.lower * b.upper, a.upper * b.lower, a.upper * b.upper});
            auto upper = max({a.lower * b.lower, a.lower * b.upper, a.upper * b.lower, a.upper * b.upper});
            auto r = _problem.create_integer_variable(lower, upper, name);
            if (a.lower == a.upper)
                _problem.post(WeightedSum{} + a.lower * b.var == 1_i * r);
            else if (b.lower == b.upper)
                _problem.post(WeightedSum{} + b.lower * a.var == 1_i * r);
            else
                _problem.post(Times{a.var, b.var, r});
            return {r, lower, upper};
        }

        // Walk an intension subexpression and return a variable holding its
        // value plus the bounds we computed. Boolean-valued nodes (e.g. eq
        // inside an arithmetic context) are reified to a 0/1 variable here.
        auto walk_intension(Node * node) -> ExprResult
        {
            switch (node->type) {
                using enum ExpressionType;

            case ODECIMAL: {
                auto val = Integer{static_cast<NodeConstant *>(node)->val};
                return {constant_variable(val), val, val};
            }

            case OVAR: {
                auto & name = static_cast<NodeVariable *>(node)->var;
                auto & mv = find_variable(name);
                return {need_variable(name), mv.lower, mv.upper};
            }

            case OADD: {
                Integer lower = 0_i, upper = 0_i;
                WeightedSum cvs;
                for (auto * p : node->parameters) {
                    auto sub = walk_intension(p);
                    lower += sub.lower;
                    upper += sub.upper;
                    cvs += 1_i * sub.var;
                }
                auto r = _problem.create_integer_variable(lower, upper, "addresult");
                cvs += -1_i * r;
                _problem.post(std::move(cvs) == 0_i);
                return {r, lower, upper};
            }

            case OSUB: {
                auto a = walk_intension(node->parameters.at(0));
                auto b = walk_intension(node->parameters.at(1));
                auto lower = a.lower - b.upper;
                auto upper = a.upper - b.lower;
                auto r = _problem.create_integer_variable(lower, upper, "subresult");
                _problem.post(WeightedSum{} + 1_i * a.var + -1_i * b.var == 1_i * r);
                return {r, lower, upper};
            }

            case OMUL: {
                if (node->parameters.empty())
                    report_unsupported("intension", "empty mul");
                auto chain = walk_intension(node->parameters.at(0));
                for (size_t i = 1; i < node->parameters.size(); ++i)
                    chain = post_product(chain, walk_intension(node->parameters.at(i)), "mulresult");
                return chain;
            }

            case ONEG: {
                auto a = walk_intension(node->parameters.at(0));
                auto lower = -a.upper;
                auto upper = -a.lower;
                auto r = _problem.create_integer_variable(lower, upper, "negresult");
                _problem.post(WeightedSum{} + 1_i * a.var + 1_i * r == 0_i);
                return {r, lower, upper};
            }

            case OABS: {
                auto a = walk_intension(node->parameters.at(0));
                auto upper = max(abs(a.lower), abs(a.upper));
                auto lower = (a.lower >= 0_i) ? a.lower
                    : (a.upper <= 0_i)        ? -a.upper
                                              : 0_i;
                auto r = _problem.create_integer_variable(lower, upper, "absresult");
                _problem.post(Abs{a.var, r});
                return {r, lower, upper};
            }

            case OSQR: {
                auto a = walk_intension(node->parameters.at(0));
                return post_product(a, a, "sqrresult");
            }

            case ONOT: {
                auto a = walk_intension(node->parameters.at(0));
                auto r = _problem.create_integer_variable(0_i, 1_i, "notresult");
                _problem.post(WeightedSum{} + 1_i * a.var + 1_i * r == 1_i);
                return {r, 0_i, 1_i};
            }

            case OMIN:
            case OMAX: {
                vector<IntegerVariableID> vars;
                vars.reserve(node->parameters.size());
                Integer lower = 0_i, upper = 0_i;
                bool first = true;
                for (auto * p : node->parameters) {
                    auto sub = walk_intension(p);
                    vars.emplace_back(sub.var);
                    if (first) {
                        lower = sub.lower;
                        upper = sub.upper;
                        first = false;
                    }
                    else {
                        lower = (node->type == OMIN) ? min(lower, sub.lower) : max(lower, sub.lower);
                        upper = (node->type == OMIN) ? min(upper, sub.upper) : max(upper, sub.upper);
                    }
                }
                auto r = _problem.create_integer_variable(lower, upper,
                    node->type == OMIN ? "minresult" : "maxresult");
                if (node->type == OMIN)
                    _problem.post(ArrayMin{vars, r});
                else
                    _problem.post(ArrayMax{vars, r});
                return {r, lower, upper};
            }

            case OPOW: {
                // Only support a constant non-negative exponent: decompose
                // to a chain of products. x^0 = 1, x^1 = x, x^k = x * x^(k-1).
                auto base = walk_intension(node->parameters.at(0));
                auto exp = node->parameters.at(1);
                if (exp->type != ODECIMAL)
                    report_unsupported("intension", "pow with non-constant exponent");
                auto k = static_cast<NodeConstant *>(exp)->val;
                if (k < 0)
                    report_unsupported("intension", "pow with negative exponent");
                if (k == 0)
                    return {constant_variable(1_i), 1_i, 1_i};
                auto chain = base;
                for (int i = 1; i < k; ++i)
                    chain = post_product(chain, base, "powresult");
                return chain;
            }

            case OMOD: {
                auto a = walk_intension(node->parameters.at(0));
                auto b = walk_intension(node->parameters.at(1));
                auto bound = max(abs(b.lower), abs(b.upper));
                auto r = _problem.create_integer_variable(-bound, bound, "modresult");
                _problem.post(Mod{a.var, b.var, r});
                return {r, -bound, bound};
            }

            case ODIV: {
                auto a = walk_intension(node->parameters.at(0));
                auto b = walk_intension(node->parameters.at(1));
                auto bound = max(abs(a.lower), abs(a.upper));
                auto r = _problem.create_integer_variable(-bound, bound, "divresult");
                _problem.post(Div{a.var, b.var, r});
                return {r, -bound, bound};
            }

            case ODIST: {
                auto a = walk_intension(node->parameters.at(0));
                auto b = walk_intension(node->parameters.at(1));
                auto bound = max(a.upper, b.upper) - min(a.lower, b.lower);
                auto diff = _problem.create_integer_variable(-bound, bound, "dist");
                auto r = _problem.create_integer_variable(0_i, bound, "distresult");
                _problem.post(WeightedSum{} + 1_i * a.var + -1_i * b.var == 1_i * diff);
                _problem.post(Abs{diff, r});
                return {r, 0_i, bound};
            }

            case OEQ: {
                if (node->parameters.size() != 2)
                    report_unsupported("intension", "n-ary eq inside expression");
                return reify_binary<EqualsIff>(node, "eqresult");
            }

            case ONE:
                return reify_binary<NotEqualsIff>(node, "neresult");

            case OLT:
                return reify_binary<LessThanIff>(node, "ltresult");
            case OLE:
                return reify_binary<LessThanEqualIff>(node, "leresult");
            case OGT:
                return reify_binary<GreaterThanIff>(node, "gtresult");
            case OGE:
                return reify_binary<GreaterThanEqualIff>(node, "geresult");

            case OIFF: {
                // For Boolean a, b: r ⇔ (a == b). EqualsIff handles this.
                if (node->parameters.size() != 2)
                    report_unsupported("intension", "n-ary iff inside expression");
                return reify_binary<EqualsIff>(node, "iffresult");
            }

            case OIMP: {
                // a ⇒ b ≡ (¬a) ∨ b. We materialise ¬a as 1-a and reify Or.
                auto a = walk_intension(node->parameters.at(0));
                auto b = walk_intension(node->parameters.at(1));
                auto not_a = _problem.create_integer_variable(0_i, 1_i, "not_a");
                _problem.post(WeightedSum{} + 1_i * a.var + 1_i * not_a == 1_i);
                auto r = _problem.create_integer_variable(0_i, 1_i, "impresult");
                vector<IntegerVariableID> args{not_a, b.var};
                _problem.post(Or{args, r});
                return {r, 0_i, 1_i};
            }

            case OXOR: {
                // r ⇔ (odd number of args == 1). Encoded as
                // ParityOdd({args, 1-r}): if r=1 the 1-r contributes 0 so
                // args must have odd parity; if r=0 the 1-r contributes 1
                // so args must have even parity.
                vector<IntegerVariableID> vars;
                vars.reserve(node->parameters.size() + 1);
                for (auto * p : node->parameters)
                    vars.emplace_back(walk_intension(p).var);
                auto r = _problem.create_integer_variable(0_i, 1_i, "xorresult");
                auto not_r = _problem.create_integer_variable(0_i, 1_i, "not_xorresult");
                _problem.post(WeightedSum{} + 1_i * r + 1_i * not_r == 1_i);
                vars.emplace_back(not_r);
                _problem.post(ParityOdd{vars});
                return {r, 0_i, 1_i};
            }

            case OIF: {
                // if(cond, then, else): cond=1 ⇒ r=then; cond=0 ⇒ r=else.
                auto cond = walk_intension(node->parameters.at(0));
                auto t = walk_intension(node->parameters.at(1));
                auto e = walk_intension(node->parameters.at(2));
                auto lower = min(t.lower, e.lower);
                auto upper = max(t.upper, e.upper);
                auto r = _problem.create_integer_variable(lower, upper, "ifresult");
                _problem.post(EqualsIf{r, t.var, cond.var == 1_i});
                _problem.post(EqualsIf{r, e.var, cond.var == 0_i});
                return {r, lower, upper};
            }

            case OAND:
            case OOR: {
                vector<IntegerVariableID> vars;
                vars.reserve(node->parameters.size());
                for (auto * p : node->parameters)
                    vars.emplace_back(walk_intension(p).var);
                auto control = _problem.create_integer_variable(0_i, 1_i,
                    node->type == OAND ? "andresult" : "orresult");
                if (node->type == OAND)
                    _problem.post(And{vars, control});
                else
                    _problem.post(Or{vars, control});
                return {control, 0_i, 1_i};
            }

            default:
                report_unsupported("intension",
                    "operator '" + XCSP3Core::operatorToString(node->type) + "' inside expression");
            }
        }

        // Walk an intension at the top level of a constraint, posting it
        // directly (no reification) when the root is a relational operator
        // we can express natively.
        auto post_intension_top_level(Node * root) -> void
        {
            switch (root->type) {
                using enum ExpressionType;

            case OEQ: {
                if (root->parameters.size() < 2)
                    report_unsupported("intension", "eq with < 2 children");
                auto first = walk_intension(root->parameters.at(0));
                for (size_t i = 1; i < root->parameters.size(); ++i) {
                    auto rest = walk_intension(root->parameters.at(i));
                    _problem.post(Equals{first.var, rest.var});
                }
                return;
            }
            case ONE: {
                if (root->parameters.size() != 2)
                    report_unsupported("intension", "ne with != 2 children");
                auto a = walk_intension(root->parameters.at(0));
                auto b = walk_intension(root->parameters.at(1));
                _problem.post(NotEquals{a.var, b.var});
                return;
            }
            case OLE: {
                auto a = walk_intension(root->parameters.at(0));
                auto b = walk_intension(root->parameters.at(1));
                _problem.post(LessThanEqual{a.var, b.var});
                return;
            }
            case OLT: {
                auto a = walk_intension(root->parameters.at(0));
                auto b = walk_intension(root->parameters.at(1));
                _problem.post(LessThan{a.var, b.var});
                return;
            }
            case OGT: {
                auto a = walk_intension(root->parameters.at(0));
                auto b = walk_intension(root->parameters.at(1));
                _problem.post(GreaterThan{a.var, b.var});
                return;
            }
            case OGE: {
                auto a = walk_intension(root->parameters.at(0));
                auto b = walk_intension(root->parameters.at(1));
                _problem.post(GreaterThanEqual{a.var, b.var});
                return;
            }
            case OOR: {
                vector<IntegerVariableID> vars;
                vars.reserve(root->parameters.size());
                for (auto * p : root->parameters)
                    vars.emplace_back(walk_intension(p).var);
                _problem.post(Or{vars});
                return;
            }
            case OIN:
            case ONOTIN: {
                if (root->parameters.size() != 2)
                    report_unsupported("intension", "in/notin with != 2 children");
                auto a = walk_intension(root->parameters.at(0));
                auto vals = walk_set_literal(root->parameters.at(1));
                vector<IntegerVariableID> vars{a.var};
                vector<vector<Integer>> tuples;
                tuples.reserve(vals.size());
                for (auto & v : vals)
                    tuples.emplace_back(vector{Integer{v}});
                if (root->type == OIN)
                    _problem.post(Table{vars, std::move(tuples)});
                else
                    _problem.post(NegativeTable{vars, std::move(tuples)});
                return;
            }
            case OAND: {
                // Top-level conjunction: post each conjunct independently.
                for (auto * p : root->parameters)
                    post_intension_top_level(p);
                return;
            }
            case OXOR: {
                // Top-level XOR: parity of the args must be odd.
                vector<IntegerVariableID> vars;
                vars.reserve(root->parameters.size());
                for (auto * p : root->parameters)
                    vars.emplace_back(walk_intension(p).var);
                _problem.post(ParityOdd{vars});
                return;
            }
            case OIMP: {
                // a ⇒ b at top level: post Or{¬a, b}.
                auto a = walk_intension(root->parameters.at(0));
                auto b = walk_intension(root->parameters.at(1));
                auto not_a = _problem.create_integer_variable(0_i, 1_i, "not_a");
                _problem.post(WeightedSum{} + 1_i * a.var + 1_i * not_a == 1_i);
                vector<IntegerVariableID> args{not_a, b.var};
                _problem.post(Or{args});
                return;
            }
            case OIFF: {
                // a ⇔ b at top level: just post Equals.
                if (root->parameters.size() != 2)
                    report_unsupported("intension", "n-ary iff at top level");
                auto a = walk_intension(root->parameters.at(0));
                auto b = walk_intension(root->parameters.at(1));
                _problem.post(Equals{a.var, b.var});
                return;
            }
            default:
                // Anything else: reify to 0/1 and assert it's true.
                auto r = walk_intension(root);
                _problem.post(Equals{r.var, 1_c});
                return;
            }
        }

        auto walk_set_literal(Node * node) -> set<long long>
        {
            if (node->type != ExpressionType::OSET)
                report_unsupported("intension", "expected set literal");
            set<long long> result;
            for (auto * p : node->parameters) {
                if (p->type != ExpressionType::ODECIMAL)
                    report_unsupported("intension", "non-constant set element");
                result.insert(static_cast<NodeConstant *>(p)->val);
            }
            return result;
        }
    };
}

auto main(int argc, char * argv[]) -> int
{
    cxxopts::Options options("XCSP Glasgow Constraint Solver", "Get started by using option --help");

    try {
        options.add_options("Program Options")   //
            ("help", "Display help information") //
            ("prove", "Create a proof")          //
            ("all", "Find all solutions")        //
            ("timeout", "Timeout in seconds", cxxopts::value<int>());

        options.add_options()("file", "Input file in XCSP format", cxxopts::value<string>());

        options.parse_positional({"file"});
    }
    catch (const cxxopts::exceptions::exception & e) {
        cerr << "Error: " << e.what() << endl;
        cerr << "Try " << argv[0] << " --help" << endl;
        return EXIT_FAILURE;
    }

    auto options_vars = options.parse(argc, argv);

    if (options_vars.count("help")) {
        cout << "Usage: " << argv[0] << " [options] xcsp-file.xml" << endl;
        cout << endl;
        cout << options.help() << endl;
        return EXIT_SUCCESS;
    }

    auto start_time = steady_clock::now();

    Problem problem;
    XCSPCallbacks callbacks{problem};
    try {
        XCSP3Core::XCSP3CoreParser parser{&callbacks};
        parser.parse(options_vars["file"].as<string>().c_str());
    }
    catch (const UnimplementedException & e) {
        cout << "s UNSUPPORTED" << endl;
        cout << "c " << e.what() << endl;
        return EXIT_FAILURE;
    }
    catch (const std::runtime_error & e) {
        // Catch the parser's default-throw for unhandled callbacks so we
        // exit cleanly rather than terminating on an uncaught exception.
        cout << "s UNSUPPORTED" << endl;
        cout << "c " << e.what() << endl;
        return EXIT_FAILURE;
    }

    auto model_done_duration = duration_cast<microseconds>(steady_clock::now() - start_time);
    cout << "d MODEL BUILD TIME " << (model_done_duration.count() / 1'000'000.0) << "s" << endl;

    optional<CurrentState> saved_solution;

    signal(SIGINT, &sig_int_or_term_handler);
    signal(SIGTERM, &sig_int_or_term_handler);

    thread timeout_thread;
    mutex timeout_mutex;
    condition_variable timeout_cv;
    bool actually_timed_out = false;

    if (options_vars.contains("timeout")) {
        seconds limit{options_vars["timeout"].as<int>()};

        timeout_thread = thread([limit = limit, &timeout_mutex, &timeout_cv, &actually_timed_out] {
            auto abort_time = system_clock::now() + limit;
            {
                /* Sleep until either we've reached the time limit,
                 * or we've finished all the work. */
                unique_lock<mutex> guard(timeout_mutex);
                while (! abort_flag.load()) {
                    if (cv_status::timeout == timeout_cv.wait_until(guard, abort_time)) {
                        /* We've woken up, and it's due to a timeout. */
                        actually_timed_out = true;
                        break;
                    }
                }
            }
            abort_flag.store(true);
        });
    }

    auto stats = solve_with(problem,
        SolveCallbacks{
            .solution = [&](const CurrentState & s) -> bool {
                if (callbacks.is_optimisation) {
                    saved_solution.emplace(s.clone());
                    cout << "o " << s(*callbacks.objective_variable) << endl;
                    return true;
                }
                else if (options_vars.contains("all")) {
                    // Stream each solution as a compact tuple line. The
                    // test runner sorts and diffs these against the cached
                    // expected output.
                    cout << "ENUMSOL:";
                    for (const auto & [n, v] : callbacks.variables())
                        if (v.id)
                            cout << " " << n << "=" << s(*v.id);
                        else
                            cout << " " << n << "=*";
                    cout << endl;
                    return true;
                }
                else {
                    saved_solution.emplace(s.clone());
                    return false;
                }
            }},
        options_vars.contains("prove") ? make_optional<ProofOptions>("xcsp") : nullopt,
        &abort_flag);

    if (timeout_thread.joinable()) {
        {
            unique_lock<mutex> guard(timeout_mutex);
            abort_flag.store(true);
            timeout_cv.notify_all();
        }
        timeout_thread.join();
    }

    bool actually_aborted = actually_timed_out || was_terminated.load();

    if (actually_aborted) {
        if (stats.solutions > 0)
            cout << "s SATISFIABLE" << endl;
        else
            cout << "s UNKNOWN" << endl;
    }
    else if (stats.solutions == 0) {
        cout << "s UNSATISFIABLE" << endl;
    }
    else if (callbacks.is_optimisation)
        cout << "s OPTIMUM FOUND" << endl;
    else
        cout << "s SATISFIABLE" << endl;

    if (saved_solution) {
        cout << "v <instantiation>" << endl;
        cout << "v   <list>";
        for (const auto & [n, _] : callbacks.variables())
            cout << " " << n;
        cout << " </list>" << endl;
        cout << "v   <values>";
        for (const auto & [_, v] : callbacks.variables())
            if (v.id)
                cout << " " << (*saved_solution)(*v.id);
            else
                cout << " *";
        cout << " </values>" << endl;
        cout << "v </instantiation>" << endl;
    }

    cout << "d WRONG DECISIONS " << stats.failures << endl;
    cout << "d PROPAGATIONS " << stats.propagations << endl;
    cout << "d EFFECTFUL PROPAGATIONS " << stats.effectful_propagations << endl;
    cout << "d CONTRADICTING PROPAGATIONS " << stats.contradicting_propagations << endl;
    cout << "d SOLVE TIME " << (stats.solve_time.count() / 1'000'000.0) << "s" << endl;

    if (options_vars.contains("all"))
        cout << "d FOUND SOLUTIONS " << stats.solutions << endl;

    return actually_aborted ? EXIT_FAILURE : EXIT_SUCCESS;
}
