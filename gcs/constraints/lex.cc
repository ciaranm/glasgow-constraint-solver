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

using std::any_cast;
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

namespace
{
    struct LexState
    {
        size_t alpha = 0;
    };
}

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

    auto state_handle = initial_state.add_constraint_state(LexState{});

    propagators.install([vars_1 = move(_vars_1), vars_2 = move(_vars_2),
                            prefix_equal_flags, decision_at_flags, state_handle](
                            const State & state, auto & inference, ProofLogger * const logger) -> PropagatorState {
        auto n = min(vars_1.size(), vars_2.size());

        auto & lex_state = any_cast<LexState &>(state.get_constraint_state(state_handle));
        auto alpha = lex_state.alpha;

        // Advance alpha through any newly-forced-equal positions. No inferences
        // happen here: those positions had vars_1[k] = vars_2[k] forced by a
        // prior call (or by branching), so the bounds in the reason already
        // imply ~decision_at[k] for all k < alpha.
        while (alpha < n) {
            auto b1 = state.bounds(vars_1[alpha]);
            auto b2 = state.bounds(vars_2[alpha]);
            if (b1.first == b1.second && b2.first == b2.second && b1.first == b2.first)
                ++alpha;
            else
                break;
        }

        // One reason for every inference this call: bounds of every variable.
        auto all_vars = vars_1;
        all_vars.insert(all_vars.end(), vars_2.begin(), vars_2.end());
        auto reason = bounds_reason(state, all_vars);

        // Helper: emit RUP line forcing decision_at[k] = FALSE under the reason.
        // RUP succeeds when bounds make decision_at[k] -> vars_1[k] - vars_2[k] >= 1
        // unsatisfiable: either both fixed-equal (k < alpha) or strict-infeasible
        // (k >= alpha and bounds say vars_1[k].hi <= vars_2[k].lo). For k beyond
        // a prefix-blocking position, RUP chains via ~prefix_equal[blocking+1]
        // (itself derivable from bounds + half-reif) and prefix_equal[k] ->
        // prefix_equal[blocking+1].
        auto emit_not_d = [&](const ReasonFunction & r, size_t k) -> void {
            logger->emit_rup_proof_line_under_reason(r,
                WPBSum{} + 1_i * ! decision_at_flags->at(k) >= 1_i,
                ProofLevel::Temporary);
        };

        bool strict_forced = false;

        if (alpha == n) {
            // Walked off the end with everything forced equal: strict is
            // required somewhere, so infeasible.
            auto contradiction_proof = [&, n](const ReasonFunction & r) -> void {
                if (! logger) return;
                for (size_t k = 0; k < n; ++k)
                    emit_not_d(r, k);
            };
            inference.contradiction(logger, JustifyExplicitlyThenRUP{contradiction_proof}, reason);
        }

        // Tighten at alpha (the >= part of the constraint): vars_1[alpha] must
        // be at least vars_2[alpha].lo, and vars_2[alpha] at most vars_1[alpha].hi.
        auto b1_alpha = state.bounds(vars_1[alpha]);
        auto b2_alpha = state.bounds(vars_2[alpha]);

        // Scaffolding for the tightening at position alpha:
        // - For k < alpha (forced fixed-equal): emit ~decision_at[k].
        // - For k >= alpha: emit "(vars_1[alpha] >= b2.first) OR ~prefix_equal[k+1]".
        //   Under the assumption ~(vars_1[alpha] >= b2.first), the framework's
        //   RUP can then chain ~prefix_equal[k+1] -> ~prefix_equal[k] -> ... ->
        //   ~decision_at[k] for k >= alpha, plus ~decision_at[alpha] from the
        //   bound assumption directly. Symmetric clauses for vars_2[alpha].
        auto tighten_proof = [&, alpha](const ReasonFunction & r) -> void {
            if (! logger) return;
            for (size_t k = 0; k < alpha; ++k)
                emit_not_d(r, k);
            for (size_t k = alpha; k < n; ++k) {
                logger->emit_rup_proof_line_under_reason(r,
                    WPBSum{} + 1_i * (vars_1[alpha] >= b2_alpha.first) + 1_i * ! prefix_equal_flags->at(k + 1) >= 1_i,
                    ProofLevel::Temporary);
                logger->emit_rup_proof_line_under_reason(r,
                    WPBSum{} + 1_i * (vars_2[alpha] < b1_alpha.second + 1_i) + 1_i * ! prefix_equal_flags->at(k + 1) >= 1_i,
                    ProofLevel::Temporary);
            }
        };

        inference.infer_all(logger,
            {vars_1[alpha] >= b2_alpha.first, vars_2[alpha] < b1_alpha.second + 1_i},
            JustifyExplicitlyThenRUP{tighten_proof}, reason);

        auto nb1_alpha = state.bounds(vars_1[alpha]);
        auto nb2_alpha = state.bounds(vars_2[alpha]);

        if (nb1_alpha.first > nb2_alpha.second) {
            strict_forced = true;
        }
        else {
            // Stateful gamma scan: walk from alpha+1 looking for the first
            // position where strict-greater becomes feasible (a candidate beta)
            // or where the equal-prefix breaks (no later witness is reachable).
            bool found_beta = false;
            for (size_t k = alpha + 1; k < n; ++k) {
                auto bk1 = state.bounds(vars_1[k]);
                auto bk2 = state.bounds(vars_2[k]);
                if (bk1.second > bk2.first) {
                    found_beta = true;
                    break;
                }
                if (bk1.second < bk2.first) {
                    // Prefix-blocked: no k' > k can be the witness either,
                    // because vars_1[k] = vars_2[k] is infeasible.
                    break;
                }
                // bk1.second == bk2.first: strict infeasible here, but the
                // prefix can still be equal at this position.
            }

            if (! found_beta) {
                bool alpha_candidate = (nb1_alpha.second > nb2_alpha.first);

                if (! alpha_candidate) {
                    // No witness anywhere: contradiction.
                    auto contradiction_proof = [&, n](const ReasonFunction & r) -> void {
                        if (! logger) return;
                        for (size_t k = 0; k < n; ++k)
                            emit_not_d(r, k);
                    };
                    inference.contradiction(logger, JustifyExplicitlyThenRUP{contradiction_proof}, reason);
                }

                // alpha is the only possible witness: force strict-greater there.
                auto force_strict_proof = [&, alpha, n](const ReasonFunction & r) -> void {
                    if (! logger) return;
                    for (size_t k = 0; k < n; ++k) {
                        if (k == alpha) continue;
                        emit_not_d(r, k);
                    }
                };

                inference.infer_all(logger,
                    {vars_1[alpha] >= nb2_alpha.first + 1_i,
                        vars_2[alpha] < nb1_alpha.second},
                    JustifyExplicitlyThenRUP{force_strict_proof}, reason);

                auto fb1 = state.bounds(vars_1[alpha]);
                auto fb2 = state.bounds(vars_2[alpha]);
                if (fb1.first > fb2.second)
                    strict_forced = true;
            }
        }

        lex_state.alpha = alpha;

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
