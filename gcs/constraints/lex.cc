#include <algorithm>
#include <gcs/constraints/lex.hh>
#include <gcs/constraints/smart_table.hh>
#include <gcs/innards/inference_tracker.hh>
#include <gcs/innards/proofs/names_and_ids_tracker.hh>
#include <gcs/innards/proofs/proof_logger.hh>
#include <gcs/innards/proofs/proof_model.hh>
#include <gcs/innards/proofs/reification.hh>
#include <gcs/innards/propagators.hh>
#include <gcs/innards/reason.hh>
#include <gcs/innards/state.hh>
#include <memory>
#include <sstream>
#include <utility>
#include <version>

#if defined(__cpp_lib_print) && defined(__cpp_lib_format)
#include <format>
#else
#include <fmt/core.h>
#include <fmt/ostream.h>
#endif

using std::make_shared;
using std::min;
using std::move;
using std::shared_ptr;
using std::size_t;
using std::string;
using std::stringstream;
using std::unique_ptr;
using std::vector;

#if defined(__cpp_lib_print) && defined(__cpp_lib_format)
using std::format;
using std::print;
#else
using fmt::format;
using fmt::print;
#endif

using namespace gcs;
using namespace gcs::innards;

LexSmartTable::LexSmartTable(vector<IntegerVariableID> vars_1, vector<IntegerVariableID> vars_2) :
    _vars_1(move(vars_1)),
    _vars_2(move(vars_2))
{
}

auto LexSmartTable::clone() const -> unique_ptr<Constraint>
{
    return make_unique<LexSmartTable>(_vars_1, _vars_2);
}

auto LexSmartTable::install(Propagators & propagators, State & initial_state, ProofModel * const optional_model) && -> void
{
    // Build the constraint as smart table
    // Question: Do we trust this encoding as a smart table?
    // Should we morally have a simpler PB encoding and reformulate?
    // Like an auto-smart-table proof?
    SmartTuples tuples;

    for (unsigned int i = 0; i < min(_vars_1.size(), _vars_2.size()); ++i) {
        vector<SmartEntry> tuple;
        for (unsigned int j = 0; j < i + 1; ++j) {
            if (j < i)
                tuple.emplace_back(SmartTable::equals(_vars_1[j], _vars_2[j]));
            else if (j == i)
                tuple.emplace_back(SmartTable::greater_than(_vars_1[j], _vars_2[j]));
        }
        tuples.emplace_back(tuple);
    }

    auto all_vars = _vars_1;
    all_vars.insert(all_vars.end(), _vars_2.begin(), _vars_2.end());

    auto smt_table = SmartTable{all_vars, tuples};
    move(smt_table).install(propagators, initial_state, optional_model);
}

auto LexSmartTable::s_exprify(const std::string & name, const innards::ProofModel * const model) const -> std::string
{
    stringstream s;

    print(s, "{} lex (", name);
    for (const auto & var : _vars_1)
        print(s, " {}", model->names_and_ids_tracker().s_expr_name_of(var));
    print(s, ") (");
    for (const auto & var : _vars_2)
        print(s, " {}", model->names_and_ids_tracker().s_expr_name_of(var));
    print(s, ")");

    return s.str();
}

Lex::Lex(vector<IntegerVariableID> vars_1, vector<IntegerVariableID> vars_2) :
    _vars_1(move(vars_1)),
    _vars_2(move(vars_2))
{
}

auto Lex::clone() const -> unique_ptr<Constraint>
{
    return make_unique<Lex>(_vars_1, _vars_2);
}

auto Lex::install(Propagators & propagators, State & initial_state, ProofModel * const optional_model) && -> void
{
    auto n = min(_vars_1.size(), _vars_2.size());

    // Saved proof flags shared with the propagator, so per-call explicit
    // justification functions can refer to them by name.
    auto prefix_equal_flags = make_shared<vector<ProofFlag>>();
    auto decision_at_flags = make_shared<vector<ProofFlag>>();

    if (optional_model) {
        // Flag-per-position OPB encoding. Two flags per position:
        //   prefix_equal[i] = TRUE iff vars_1[j] = vars_2[j] for all j < i
        //   decision_at[i]  = TRUE iff i is a witness deciding position
        // plus a global disjunction saying at least one decision_at must hold.
        for (size_t i = 0; i <= n; ++i)
            prefix_equal_flags->push_back(optional_model->create_proof_flag(format("lex_prefix_equal_{}", i)));
        for (size_t i = 0; i < n; ++i)
            decision_at_flags->push_back(optional_model->create_proof_flag(format("lex_decision_at_{}", i)));

        // prefix_equal[0] is unconditionally TRUE.
        optional_model->add_constraint(WPBSum{} + 1_i * prefix_equal_flags->at(0) >= 1_i);

        for (size_t i = 0; i < n; ++i) {
            // prefix_equal[i+1] -> prefix_equal[i]
            optional_model->add_constraint(
                WPBSum{} + 1_i * prefix_equal_flags->at(i) >= 1_i,
                HalfReifyOnConjunctionOf{prefix_equal_flags->at(i + 1)});

            // prefix_equal[i+1] -> vars_1[i] = vars_2[i]
            optional_model->add_constraint(
                WPBSum{} + 1_i * _vars_1[i] + -1_i * _vars_2[i] == 0_i,
                HalfReifyOnConjunctionOf{prefix_equal_flags->at(i + 1)});

            // decision_at[i] -> prefix_equal[i]
            optional_model->add_constraint(
                WPBSum{} + 1_i * prefix_equal_flags->at(i) >= 1_i,
                HalfReifyOnConjunctionOf{decision_at_flags->at(i)});

            // decision_at[i] -> vars_1[i] > vars_2[i]
            optional_model->add_constraint(
                WPBSum{} + 1_i * _vars_1[i] + -1_i * _vars_2[i] >= 1_i,
                HalfReifyOnConjunctionOf{decision_at_flags->at(i)});
        }

        // At least one decision_at[i] must hold.
        WPBSum at_least_one_decision;
        for (auto & d : *decision_at_flags)
            at_least_one_decision += 1_i * d;
        optional_model->add_constraint(move(at_least_one_decision) >= 1_i);
    }

    Triggers triggers;
    for (auto & v : _vars_1)
        triggers.on_bounds.push_back(v);
    for (auto & v : _vars_2)
        triggers.on_bounds.push_back(v);

    propagators.install([vars_1 = move(_vars_1), vars_2 = move(_vars_2),
                            prefix_equal_flags, decision_at_flags](
                            const State & state, auto & inference, ProofLogger * const logger) -> PropagatorState {
        auto n = min(vars_1.size(), vars_2.size());

        // One reason for every inference this call: bounds of every variable.
        auto all_vars = vars_1;
        all_vars.insert(all_vars.end(), vars_2.begin(), vars_2.end());
        auto reason = bounds_reason(state, all_vars);

        // Helper: emit RUP line forcing decision_at[k] = FALSE under the reason.
        // RUP succeeds when bounds make decision_at[k] -> vars_1[k] - vars_2[k] >= 1
        // unsatisfiable: either both fixed-equal (k < alpha) or strict-infeasible
        // (k >= alpha after RL pass found no beta).
        auto emit_not_d = [&](const ReasonFunction & r, size_t k) -> void {
            logger->emit_rup_proof_line_under_reason(r,
                WPBSum{} + 1_i * ! decision_at_flags->at(k) >= 1_i,
                ProofLevel::Temporary);
        };

        // Left-to-right pass: while still in the forced-equal prefix, enforce
        // vars_1[i] >= vars_2[i] and decide whether to stop.
        size_t alpha = n;
        bool strict_forced = false;

        for (size_t i = 0; i < n; ++i) {
            auto b1 = state.bounds(vars_1[i]);
            auto b2 = state.bounds(vars_2[i]);

            // Scaffolding for the LR-pass tightening at position i.
            // - For k < i (forced fixed-equal): emit ~decision_at[k].
            // - For k > i: emit the clause "(vars_1[i] >= b2.first) OR ~prefix_equal[k+1]".
            //   This is RUP-derivable because the chain prefix_equal[k+1] -> ... ->
            //   prefix_equal[i+1] -> vars_1[i] = vars_2[i], combined with the bound
            //   on vars_2[i] in the reason, forces vars_1[i] >= b2.first when
            //   prefix_equal[k+1] is true. With these clauses available, the
            //   framework's RUP for the inference can chain through
            //   ~prefix_equal[k+1] -> ~prefix_equal[k] -> ... -> ~decision_at[k].
            auto lr_proof = [&, i](const ReasonFunction & r) -> void {
                if (! logger) return;
                for (size_t k = 0; k < i; ++k)
                    emit_not_d(r, k);
                // Emit the chain clauses for prefix_equal[i+1..n], so the
                // framework's RUP for the inference can propagate
                // ~prefix_equal[k] through the chain.
                for (size_t k = i; k < n; ++k) {
                    logger->emit_rup_proof_line_under_reason(r,
                        WPBSum{} + 1_i * (vars_1[i] >= b2.first) + 1_i * ! prefix_equal_flags->at(k + 1) >= 1_i,
                        ProofLevel::Temporary);
                    logger->emit_rup_proof_line_under_reason(r,
                        WPBSum{} + 1_i * (vars_2[i] < b1.second + 1_i) + 1_i * ! prefix_equal_flags->at(k + 1) >= 1_i,
                        ProofLevel::Temporary);
                }
            };

            inference.infer_all(logger,
                {vars_1[i] >= b2.first, vars_2[i] < b1.second + 1_i},
                JustifyExplicitlyThenRUP{lr_proof}, reason);

            auto nb1 = state.bounds(vars_1[i]);
            auto nb2 = state.bounds(vars_2[i]);

            if (nb1.first > nb2.second) {
                // Strict already forced at i: constraint discharged here.
                strict_forced = true;
                break;
            }
            if (nb1.first == nb1.second && nb2.first == nb2.second && nb1.first == nb2.first) {
                // Both fixed to the same value: keep walking.
                continue;
            }

            alpha = i;
            break;
        }

        if ((! strict_forced) && alpha == n) {
            // Walked off the end with everything forced equal: strict is
            // required somewhere, so infeasible.
            auto contradiction_proof = [&, n](const ReasonFunction & r) -> void {
                if (! logger) return;
                for (size_t k = 0; k < n; ++k)
                    emit_not_d(r, k);
            };
            inference.contradiction(logger, JustifyExplicitlyThenRUP{contradiction_proof}, reason);
        }

        if (! strict_forced) {
            // Right-to-left pass: any beta > alpha where strict greater is
            // feasible? If not, strict has to happen at alpha.
            bool strict_possible_after_alpha = false;
            for (size_t i = n; i-- > alpha + 1;) {
                auto b1 = state.bounds(vars_1[i]);
                auto b2 = state.bounds(vars_2[i]);
                if (b1.second > b2.first) {
                    strict_possible_after_alpha = true;
                    break;
                }
            }

            if (! strict_possible_after_alpha) {
                auto b1_alpha = state.bounds(vars_1[alpha]);
                auto b2_alpha = state.bounds(vars_2[alpha]);

                auto explicit_proof = [&, alpha, n](const ReasonFunction & r) -> void {
                    if (! logger) return;
                    for (size_t k = 0; k < n; ++k) {
                        if (k == alpha) continue;
                        emit_not_d(r, k);
                    }
                };

                inference.infer_all(logger,
                    {vars_1[alpha] >= b2_alpha.first + 1_i,
                        vars_2[alpha] < b1_alpha.second},
                    JustifyExplicitlyThenRUP{explicit_proof}, reason);
            }
        }

        // If strict is already forced at some position, the constraint is
        // fully discharged for this branch: bounds only ever tighten further,
        // so this can never become un-discharged before backtrack.
        return strict_forced ? PropagatorState::DisableUntilBacktrack : PropagatorState::Enable;
    },
        triggers, "lex");
}

auto Lex::s_exprify(const std::string & name, const innards::ProofModel * const model) const -> std::string
{
    stringstream s;

    print(s, "{} lex (", name);
    for (const auto & var : _vars_1)
        print(s, " {}", model->names_and_ids_tracker().s_expr_name_of(var));
    print(s, ") (");
    for (const auto & var : _vars_2)
        print(s, " {}", model->names_and_ids_tracker().s_expr_name_of(var));
    print(s, ")");

    return s.str();
}
