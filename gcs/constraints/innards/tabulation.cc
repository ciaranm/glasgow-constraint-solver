#include <gcs/constraints/innards/tabulation.hh>
#include <gcs/exception.hh>
#include <gcs/expression.hh>
#include <gcs/innards/proofs/names_and_ids_tracker.hh>
#include <gcs/innards/proofs/proof_logger.hh>
#include <gcs/innards/state.hh>

#include <algorithm>
#include <cstdlib>

#include <util/enumerate.hh>
#include <util/overloaded.hh>

using namespace gcs;
using namespace gcs::innards;

using std::function;
using std::get_if;
using std::move;
using std::nullopt;
using std::optional;
using std::size_t;
using std::string;
using std::vector;
using std::ranges::stable_sort;

namespace
{
    auto condition_holds_at(const IntegerVariableCondition & cond, Integer val) -> bool
    {
        switch (cond.op) {
            using enum VariableConditionOperator;
        case Equal: return val == cond.value;
        case NotEqual: return val != cond.value;
        case GreaterEqual: return val >= cond.value;
        case Less: return val < cond.value;
        case InRange: return val >= cond.value && val <= cond.upper_value;
        case NotInRange: return val < cond.value || val > cond.upper_value;
        }
        throw NonExhaustiveSwitch{};
    }
}

auto gcs::innards::build_table_in_proof(const vector<IntegerVariableID> & vars, const vector<DeterminedVariable> & determined_vars,
    const optional<TabulationReification> & reification, const function<auto(const vector<Integer> &)->bool> & accept, const string & selector_name,
    const string & comment, State & state, ProofLogger * const logger) -> optional<ExtensionalData>
{
    // a reification variable is branched on first, so that its Free values
    // can cut their whole subtree down to one wildcard tuple.
    optional<size_t> reification_pos;
    if (reification) {
        for (size_t idx = 0; idx < vars.size(); ++idx)
            if (vars[idx] == reification->var) {
                reification_pos = idx;
                break;
            }
        if (! reification_pos)
            throw UnexpectedException{"tabulation reification variable is not among the variables being enumerated"};
    }

    // the proof derivation emits a line per enumeration tree node, so branch
    // on small domains first to minimise the internal node count. If a
    // functionally determined variable is available, the largest-domained one
    // goes last instead, and its whole level of the tree is skipped: the
    // header explains why its parents' backtrack lines are still RUP.
    optional<size_t> determined_last;
    const DeterminedVariable * determined_choice = nullptr;
    for (const auto & d : determined_vars) {
        optional<size_t> pos;
        for (size_t idx = 0; idx < vars.size(); ++idx)
            if (vars[idx] == d.var) {
                pos = idx;
                break;
            }
        if (! pos)
            throw UnexpectedException{"tabulation determined variable is not among the variables being enumerated"};
        if (pos == reification_pos)
            throw UnexpectedException{"tabulation reification variable cannot be claimed as determined"};
        if ((! determined_last) || state.domain_size(vars[*pos]) > state.domain_size(vars[*determined_last])) {
            determined_last = pos;
            determined_choice = &d;
        }
    }

    vector<size_t> order;
    for (size_t idx = 0; idx < vars.size(); ++idx)
        if (idx != determined_last && idx != reification_pos)
            order.push_back(idx);
    stable_sort(order, {}, [&](size_t idx) { return state.domain_size(vars[idx]); });
    if (reification_pos)
        order.insert(order.begin(), *reification_pos);
    if (determined_last)
        order.push_back(*determined_last);

    vector<vector<IntegerOrWildcard>> permitted;
    vector<Integer> assignment(vars.size(), 0_i);
    size_t depth = 0;

    auto future_var_id = state.what_variable_id_will_be_created_next();

    WPBSum trail;
    auto record = [&](ProofLogger * const logger, size_t n_assigned) {
        vector<IntegerOrWildcard> tuple(vars.size(), Wildcard{});
        for (size_t k = 0; k < n_assigned; ++k)
            tuple[order[k]] = assignment[order[k]];
        permitted.push_back(move(tuple));

        if (logger && logger->get_assertion_level() == AssertionLevel::Off) {
            Integer sel_value(permitted.size() - 1);
            logger->names_and_ids_tracker().create_literals_for_introduced_variable_value(future_var_id, sel_value, selector_name);
            trail += 1_i * (future_var_id == sel_value);

            WPBSum forward_implication, reverse_implication;
            forward_implication += Integer(n_assigned) * (future_var_id != sel_value);
            reverse_implication += 1_i * (future_var_id == sel_value);

            for (const auto & [idx, entry] : enumerate(permitted.back()))
                if (const auto * val = get_if<Integer>(&entry)) {
                    forward_implication += 1_i * (vars[idx] == *val);
                    reverse_implication += 1_i * (vars[idx] != *val);
                }

            logger->emit_red_proof_line(
                forward_implication >= Integer(n_assigned), {{future_var_id == sel_value, FalseLiteral{}}}, ProofLevel::Current);
            logger->emit_red_proof_line(reverse_implication >= 1_i, {{future_var_id == sel_value, TrueLiteral{}}}, ProofLevel::Current);
        }
    };

    auto current_branch = TabulationBranch::Holds;
    function<void(ProofLogger * const)> search = [&](ProofLogger * const logger) {
        if (depth == vars.size()) {
            if (accept(assignment))
                record(logger, vars.size());
        }
        else if (determined_last && depth == vars.size() - 1 && TabulationBranch::Holds == current_branch) {
            // the one remaining variable is functionally determined by the
            // assigned prefix: no iteration over its domain, and no per-value
            // backtrack lines. The candidate is still checked against the
            // domain and the acceptance test, so a wrong value() cannot
            // inject a bad tuple; a wrongly missed one fails verification at
            // the parent's backtrack line.
            if (auto val = determined_choice->value(assignment); val && state.in_domain(vars[order[depth]], *val)) {
                assignment[order[depth]] = *val;
                if (accept(assignment))
                    record(logger, vars.size());
            }
        }
        else {
            for (auto val : state.each_value_mutable(vars[order[depth]])) {
                assignment[order[depth]] = val;
                if (reification && 0 == depth) {
                    auto branch = reification->branch(val);
                    if (TabulationBranch::Free == branch) {
                        // every completion of this reification value is
                        // accepted: one tuple, wildcard everywhere else,
                        // covers the whole subtree, and its reverse
                        // implication makes the enclosing backtrack line RUP
                        // without the subtree ever being visited.
                        record(logger, depth + 1);
                        continue;
                    }
                    current_branch = branch;
                }
                ++depth;
                search(logger);
                --depth;
            }
        }

        if (logger && logger->get_assertion_level() == AssertionLevel::Off) {
            WPBSum backtrack = trail;
            for (size_t idx = 0; idx < depth; ++idx)
                backtrack += 1_i * (vars[order[idx]] != assignment[order[idx]]);

            logger->emit_rup_proof_line(backtrack >= 1_i, ProofLevel::Current);
        }
    };

    if (logger && logger->get_assertion_level() == AssertionLevel::Off)
        logger->emit_proof_comment(comment);
    search(logger);

    if (permitted.empty())
        return nullopt;

    auto sel = state.allocate_integer_variable_with_state(0_i, Integer(permitted.size() - 1));
    if (sel != future_var_id)
        throw UnexpectedException{"something went horribly wrong with variable IDs"};

    return ExtensionalData{sel, vector<IntegerVariableID>{vars}, move(permitted)};
}

auto gcs::innards::reify_tabulation(const ReificationCondition & reif, TabulationVariables & enum_vars,
    function<auto(const vector<Integer> &)->bool> base_accept, vector<DeterminedVariable> base_determined) -> ReifiedTabulation
{
    return overloaded{                                                                                                    //
        [&](const reif::MustHold &) -> ReifiedTabulation { return {move(base_accept), move(base_determined), nullopt}; }, //
        [&](const reif::MustNotHold &) -> ReifiedTabulation {
            return {[base_accept = move(base_accept)](const vector<Integer> & vals) { return ! base_accept(vals); }, {}, nullopt};
        },
        [&](const reif::If & r) -> ReifiedTabulation {
            auto pcond = enum_vars.position_of(r.cond.var);
            std::erase_if(base_determined, [&](const DeterminedVariable & d) { return d.var == r.cond.var; });
            return {[base_accept = move(base_accept), cond = r.cond, pcond](
                        const vector<Integer> & vals) { return (! condition_holds_at(cond, vals[pcond])) || base_accept(vals); },
                move(base_determined),
                TabulationReification{r.cond.var,
                    [cond = r.cond](Integer val) { return condition_holds_at(cond, val) ? TabulationBranch::Holds : TabulationBranch::Free; }}};
        },
        [&](const reif::NotIf & r) -> ReifiedTabulation {
            auto pcond = enum_vars.position_of(r.cond.var);
            return {[base_accept = move(base_accept), cond = r.cond, pcond](
                        const vector<Integer> & vals) { return (! condition_holds_at(cond, vals[pcond])) || ! base_accept(vals); },
                {}, TabulationReification{r.cond.var, [cond = r.cond](Integer val) {
                                              return condition_holds_at(cond, val) ? TabulationBranch::Negated : TabulationBranch::Free;
                                          }}};
        },
        [&](const reif::Iff & r) -> ReifiedTabulation {
            auto pcond = enum_vars.position_of(r.cond.var);
            std::erase_if(base_determined, [&](const DeterminedVariable & d) { return d.var == r.cond.var; });
            return {[base_accept = move(base_accept), cond = r.cond, pcond](
                        const vector<Integer> & vals) { return condition_holds_at(cond, vals[pcond]) == base_accept(vals); },
                move(base_determined),
                TabulationReification{r.cond.var,
                    [cond = r.cond](Integer val) { return condition_holds_at(cond, val) ? TabulationBranch::Holds : TabulationBranch::Negated; }}};
        }}
        .visit(reif);
}

auto gcs::innards::default_tabulation_threshold() -> long long
{
    static const long long threshold = []() -> long long {
        if (const char * e = std::getenv("GCS_TABULATION_THRESHOLD"))
            return std::strtoll(e, nullptr, 10);
        return 100; // default: a guess, see the header
    }();
    return threshold;
}

auto gcs::innards::want_tabulation(const std::variant<consistency::Auto, consistency::BC, consistency::Tabulated> & level,
    const vector<IntegerVariableID> & enum_vars, const vector<DeterminedVariable> & determined_vars, const State & initial_state) -> bool
{
    return overloaded{                                        //
        [&](const consistency::Tabulated &) { return true; }, //
        [&](const consistency::BC &) { return false; },       //
        [&](const consistency::Auto &) {
            // build_table_in_proof skips the largest-domained determined
            // variable's level (picked the same way here, first of equal
            // maxima), so neither the enumeration nor the proof derivation
            // pays for it: leave it out of the budget.
            optional<IntegerVariableID> skip;
            for (const auto & d : determined_vars)
                if ((! skip) || initial_state.domain_size(d.var) > initial_state.domain_size(*skip))
                    skip = d.var;

            long long size = 1;
            for (const auto & v : enum_vars)
                if (v != skip && __builtin_mul_overflow(size, initial_state.domain_size(v).raw_value, &size))
                    return false;
            return size <= default_tabulation_threshold();
        }}
        .visit(level);
}
