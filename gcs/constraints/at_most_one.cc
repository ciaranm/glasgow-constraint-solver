#include <gcs/constraints/at_most_one.hh>
#include <gcs/constraints/smart_table.hh>
#include <gcs/innards/inference_tracker.hh>
#include <gcs/innards/proofs/names_and_ids_tracker.hh>
#include <gcs/innards/proofs/proof_logger.hh>
#include <gcs/innards/proofs/proof_model.hh>
#include <gcs/innards/propagators.hh>
#include <gcs/innards/state.hh>

#include <algorithm>
#include <optional>
#include <sstream>
#include <utility>

#include <version>

#if defined(__cpp_lib_print) && defined(__cpp_lib_format)
#include <print>
#else
#include <fmt/ostream.h>
#endif

using std::cmp_less;
using std::get;
using std::make_optional;
using std::move;
using std::string;
using std::stringstream;
using std::tuple;
using std::unique_ptr;
using std::vector;

using namespace gcs;
using namespace gcs::innards;

#if defined(__cpp_lib_print) && defined(__cpp_lib_format)
using std::print;
#else
using fmt::print;
#endif

// ----- Native AtMostOne -----------------------------------------------------

AtMostOne::AtMostOne(vector<IntegerVariableID> vars, IntegerVariableID val) :
    _vars(move(vars)),
    _val(val)
{
}

auto AtMostOne::clone() const -> unique_ptr<Constraint>
{
    return make_unique<AtMostOne>(_vars, _val);
}

auto AtMostOne::install(Propagators & propagators, State & initial_state, ProofModel * const optional_model) && -> void
{
    if (! prepare(propagators, initial_state, optional_model))
        return;

    if (_vars.size() < 2)
        return;

    if (optional_model)
        define_proof_model(*optional_model);

    install_propagators(propagators);
}

auto AtMostOne::define_proof_model(ProofModel & model) -> void
{
    // For each var_i: define flag_i ⇔ (var_i = _val) via a Count-style
    // gt/lt/eq triple, then post sum_i flag_i ≤ 1.
    for (auto & var : _vars) {
        auto var_minus_val_gt_0 = model.create_proof_flag_fully_reifying("am1g",
            "AtMostOne", "var greater", WPBSum{} + 1_i * var + -1_i * _val >= 1_i);

        auto var_minus_val_lt_0 = model.create_proof_flag_fully_reifying("am1l",
            "AtMostOne", "var less", WPBSum{} + 1_i * var + -1_i * _val <= -1_i);

        auto eq = model.create_proof_flag_fully_reifying("am1eq",
            "AtMostOne", "var equal val", WPBSum{} + 1_i * ! var_minus_val_gt_0 + 1_i * ! var_minus_val_lt_0 >= 2_i);

        _flags.emplace_back(eq, var_minus_val_gt_0, var_minus_val_lt_0);
    }

    WPBSum sum;
    for (auto & [flag, _gt, _lt] : _flags)
        sum += 1_i * flag;
    model.add_constraint("AtMostOne", "at most one match", sum <= 1_i);
}

auto AtMostOne::install_propagators(Propagators & propagators) -> void
{
    Triggers triggers;
    triggers.on_change.insert(triggers.on_change.end(), _vars.begin(), _vars.end());
    triggers.on_change.emplace_back(_val);

    vector<IntegerVariableID> all_vars = _vars;
    all_vars.push_back(_val);

    propagators.install(
        [vars = _vars, val = _val, all_vars = move(all_vars)](
            const State & state, auto & inference, ProofLogger * const logger) -> PropagatorState {
            // For each candidate value v of `val`: if two or more vars
            // are fixed to v, infer val ≠ v. (RUP from the encoding's
            // sum ≤ 1 plus the fixedness reasons.)
            for (auto v : state.each_value_immutable(val)) {
                int fixed_to_v = 0;
                for (auto & var : vars) {
                    if (state.optional_single_value(var) == make_optional(v)) {
                        if (++fixed_to_v == 2)
                            break;
                    }
                }
                if (fixed_to_v >= 2)
                    inference.infer(logger, val != v, JustifyUsingRUP{},
                        generic_reason(state, all_vars));
            }

            // If val is now fixed to v and exactly one var is fixed to v,
            // infer var_j ≠ v for every other var. (Same RUP argument.)
            auto val_fixed = state.optional_single_value(val);
            if (val_fixed) {
                int fixed_count = 0;
                size_t fixed_idx = 0;
                for (size_t i = 0; cmp_less(i, vars.size()); ++i) {
                    if (state.optional_single_value(vars[i]) == val_fixed) {
                        ++fixed_count;
                        fixed_idx = i;
                        if (fixed_count > 1)
                            break;
                    }
                }
                if (fixed_count == 1) {
                    for (size_t i = 0; cmp_less(i, vars.size()); ++i) {
                        if (i != fixed_idx)
                            inference.infer(logger, vars[i] != *val_fixed, JustifyUsingRUP{},
                                generic_reason(state, all_vars));
                    }
                }
            }

            return PropagatorState::Enable;
        },
        triggers);
}

auto AtMostOne::s_exprify(const string & name, const ProofModel * const model) const -> string
{
    stringstream s;
    print(s, "{} at_most_one (", name);
    for (const auto & var : _vars)
        print(s, " {}", model->names_and_ids_tracker().s_expr_name_of(var));
    print(s, ") {}", model->names_and_ids_tracker().s_expr_name_of(_val));
    return s.str();
}

// ----- AtMostOneSmartTable (kept for benchmarking) --------------------------

AtMostOneSmartTable::AtMostOneSmartTable(vector<IntegerVariableID> vars, IntegerVariableID val) :
    _vars(move(vars)),
    _val(val)
{
}

auto AtMostOneSmartTable::clone() const -> unique_ptr<Constraint>
{
    return make_unique<AtMostOneSmartTable>(_vars, _val);
}

auto AtMostOneSmartTable::install(Propagators & propagators, State & initial_state,
    ProofModel * const optional_model) && -> void
{
    // 0 or 1 vars: "at most 1 of n equals val" is vacuously true. The
    // SmartTable below would build empty tuples for n == 0, which means
    // "no row matches" i.e. UNSAT — wrong for the trivial case. Skip.
    if (_vars.size() < 2)
        return;

    SmartTuples tuples;
    for (int i = 0; cmp_less(i, _vars.size()); ++i) {
        vector<SmartEntry> tuple;
        for (int j = 0; cmp_less(j, _vars.size()); ++j) {
            if (j != i) {
                tuple.emplace_back(SmartTable::not_equals(_vars[j], _val));
            }
        }
        tuples.emplace_back(tuple);
    }

    auto all_vars = _vars;
    all_vars.emplace_back(_val);

    SmartTable smt_table{all_vars, tuples};
    move(smt_table).install(propagators, initial_state, optional_model);
}

auto AtMostOneSmartTable::s_exprify(const string & name, const ProofModel * const model) const -> string
{
    stringstream s;
    print(s, "{} at_most_one_smart_table (", name);
    for (const auto & var : _vars)
        print(s, " {}", model->names_and_ids_tracker().s_expr_name_of(var));
    print(s, ") {}", model->names_and_ids_tracker().s_expr_name_of(_val));
    return s.str();
}
