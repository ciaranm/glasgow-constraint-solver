#include <gcs/constraints/comparison.hh>
#include <gcs/constraints/innards/reified_dispatcher.hh>
#include <gcs/constraints/innards/reified_state.hh>
#include <gcs/exception.hh>
#include <gcs/innards/inference_tracker.hh>
#include <gcs/innards/proofs/names_and_ids_tracker.hh>
#include <gcs/innards/proofs/proof_logger.hh>
#include <gcs/innards/proofs/proof_model.hh>
#include <gcs/innards/propagators.hh>
#include <gcs/innards/s_expr.hh>
#include <gcs/innards/state.hh>

#include <util/overloaded.hh>

#include <version>

#if defined(__cpp_lib_print) && defined(__cpp_lib_format)
#include <format>
#include <print>
#else
#include <fmt/core.h>
#include <fmt/ostream.h>
#endif

#include <sstream>
#include <string>

using namespace gcs;
using namespace gcs::innards;

using std::nullopt;
using std::optional;
using std::string;
using std::unique_ptr;
using std::vector;

#if defined(__cpp_lib_print) && defined(__cpp_lib_format)
using std::format;
using std::print;
#else
using fmt::format;
using fmt::print;
#endif

ReifiedCompareLessThanOrMaybeEqual::ReifiedCompareLessThanOrMaybeEqual(const IntegerVariableID v1, const IntegerVariableID v2, ReificationCondition cond, bool or_equal, bool vars_swapped) :
    _v1(v1),
    _v2(v2),
    _reif_cond(cond),
    _or_equal(or_equal),
    _vars_swapped(vars_swapped)
{
}

LessThan::LessThan(const IntegerVariableID v1, const IntegerVariableID v2) :
    ReifiedCompareLessThanOrMaybeEqual(v1, v2, reif::MustHold{}, false)
{
    // Two constants that happen to be equal is a valid (if trivially
    // infeasible) model; only reject true variable aliasing.
    if (v1 == v2 && ! is_constant_variable(v1))
        throw InvalidProblemDefinitionException{"LessThan: both operands are the same variable handle"};
}

GreaterThan::GreaterThan(const IntegerVariableID v1, const IntegerVariableID v2) :
    ReifiedCompareLessThanOrMaybeEqual(v2, v1, reif::MustHold{}, false, true)
{
    if (v1 == v2 && ! is_constant_variable(v1))
        throw InvalidProblemDefinitionException{"GreaterThan: both operands are the same variable handle"};
}

auto ReifiedCompareLessThanOrMaybeEqual::clone() const -> unique_ptr<Constraint>
{
    return make_unique<ReifiedCompareLessThanOrMaybeEqual>(_v1, _v2, _reif_cond, _or_equal, _vars_swapped);
}

auto ReifiedCompareLessThanOrMaybeEqual::install(Propagators & propagators, State & initial_state, ProofModel * const optional_model) && -> void
{
    if (! prepare(propagators, initial_state, optional_model))
        return;

    if (optional_model)
        define_proof_model(*optional_model);

    install_propagators(propagators);
}

auto ReifiedCompareLessThanOrMaybeEqual::prepare(Propagators &, State & initial_state, ProofModel * const) -> bool
{
    _v1_is_constant = initial_state.optional_single_value(_v1);
    _v2_is_constant = initial_state.optional_single_value(_v2);
    _evaluated_cond = test_reification_condition(initial_state, _reif_cond);
    return true;
}

auto ReifiedCompareLessThanOrMaybeEqual::define_proof_model(ProofModel & model) -> void
{
    // `role` is the cake_pb_cp @c label role, or "" for the lines cake leaves
    // unlabelled (an unconditional comparison is a single bare inequality).
    auto do_less = [&](IntegerVariableID v1, IntegerVariableID v2, optional<HalfReifyOnConjunctionOf> cond, bool or_equal, const string & role, const StringLiteral & rule) {
        auto ineq = WPBSum{} + 1_i * v1 + -1_i * v2 <= (or_equal ? 0_i : -1_i);
        if (role.empty())
            model.add_constraint("ReifiedCompareLessThanOrMaybeEqual", rule, ineq, cond);
        else
            model.add_labelled_constraint(as_string(_constraint_id), role, "ReifiedCompareLessThanOrMaybeEqual", rule, ineq, cond);
    };

    overloaded{
        [&](const reif::MustHold &) {
            do_less(_v1, _v2, nullopt, _or_equal, "", "condition true");
        },
        [&](const reif::MustNotHold &) {
            do_less(_v2, _v1, nullopt, ! _or_equal, "", "condition false");
        },
        [&](const reif::If & cond) {
            do_less(_v1, _v2, HalfReifyOnConjunctionOf{{cond.cond}}, _or_equal, "", "if condition");
        },
        [&](const reif::NotIf & cond) {
            do_less(_v2, _v1, HalfReifyOnConjunctionOf{{cond.cond}}, ! _or_equal, "", "if condition");
        },
        [&](const reif::Iff & cond) {
            // cake_pb_cp labels the !cond half [f] and the cond half [r].
            do_less(_v1, _v2, HalfReifyOnConjunctionOf{{cond.cond}}, _or_equal, "r", "if condition");
            do_less(_v2, _v1, HalfReifyOnConjunctionOf{{! cond.cond}}, ! _or_equal, "f", "if not condition");
        }}
        .visit(_reif_cond);
}

auto ReifiedCompareLessThanOrMaybeEqual::install_propagators(Propagators & propagators) -> void
{
    if (_v1_is_constant && _v2_is_constant) {
        /* special case: both values are constant, so we're potentially forcing
         * the reification condition, or just giving contradiction, but will never
         * propagate beyond that. */
        bool holds = (_or_equal ? *_v1_is_constant <= *_v2_is_constant : *_v1_is_constant < *_v2_is_constant);
        overloaded{
            [&](const evaluated_reif::MustHold & reif) {
                if (! holds)
                    propagators.install_initialiser([v1 = _v1, v2 = _v2, v1_is_constant = _v1_is_constant, v2_is_constant = _v2_is_constant, cond = reif.cond](
                                                        const State &, auto & inference, ProofLogger * const logger) -> void {
                        inference.infer(logger, ! cond, JustifyUsingRUP{}, ExplicitReason{ReasonLiterals{{cond, v1 == *v1_is_constant, v2 == *v2_is_constant}}});
                    });
            },
            [&](const evaluated_reif::MustNotHold & reif) {
                if (holds)
                    propagators.install_initialiser([v1 = _v1, v2 = _v2, v1_is_constant = _v1_is_constant, v2_is_constant = _v2_is_constant, cond = reif.cond](
                                                        const State &, auto & inference, ProofLogger * const logger) -> void {
                        inference.infer(logger, ! cond, JustifyUsingRUP{}, ExplicitReason{ReasonLiterals{{cond, v1 == *v1_is_constant, v2 == *v2_is_constant}}});
                    });
            },
            [&](const evaluated_reif::Undecided & reif) {
                auto lit = holds
                    ? reif.cond_to_infer_if_constraint_must_hold()
                    : reif.cond_to_infer_if_constraint_must_not_hold();
                if (lit)
                    propagators.install_initialiser([v1 = _v1, v2 = _v2, v1_is_constant = _v1_is_constant, v2_is_constant = _v2_is_constant, lit = *lit](
                                                        const State &, auto & inference, ProofLogger * const logger) -> void {
                        inference.infer(logger, lit, JustifyUsingRUP{}, ExplicitReason{ReasonLiterals{{v1 == *v1_is_constant, v2 == *v2_is_constant}}});
                    });
            },
            [](const evaluated_reif::Deactivated &) {
            }}
            .visit(_evaluated_cond);
    }
    else {
        auto enforce_constraint_must_hold = [v1 = _v1, v2 = _v2, or_equal = _or_equal](
                                                const State & state, auto & inference, ProofLogger * const logger,
                                                const Literal & cond) -> PropagatorState {
            auto v1_bounds = state.bounds(v1), v2_bounds = state.bounds(v2);
            inference.infer_less_than(logger, v1, v2_bounds.second + (or_equal ? 1_i : 0_i), JustifyUsingRUP{},
                ExplicitReason{ReasonLiterals{{cond, v2 <= v2_bounds.second}}});
            inference.infer_greater_than_or_equal(logger, v2, v1_bounds.first + (or_equal ? 0_i : 1_i), JustifyUsingRUP{},
                ExplicitReason{ReasonLiterals{{cond, v1 >= v1_bounds.first}}});
            return v1_bounds.second < (v2_bounds.first + (or_equal ? 1_i : 0_i))
                ? PropagatorState::DisableUntilBacktrack
                : PropagatorState::Enable;
        };

        auto enforce_constraint_must_not_hold = [v1 = _v1, v2 = _v2, or_equal = _or_equal](
                                                    const State & state, auto & inference, ProofLogger * const logger,
                                                    const Literal & cond) -> PropagatorState {
            auto v1_bounds = state.bounds(v1), v2_bounds = state.bounds(v2);
            inference.infer_less_than(logger, v2, v1_bounds.second + (! or_equal ? 1_i : 0_i), JustifyUsingRUP{},
                ExplicitReason{ReasonLiterals{{cond, v1 <= v1_bounds.second}}});
            inference.infer_greater_than_or_equal(logger, v1, v2_bounds.first + (! or_equal ? 0_i : 1_i), JustifyUsingRUP{},
                ExplicitReason{ReasonLiterals{{cond, v2 >= v2_bounds.first}}});
            return v2_bounds.second < (v1_bounds.first + (! or_equal ? 1_i : 0_i))
                ? PropagatorState::DisableUntilBacktrack
                : PropagatorState::Enable;
        };

        auto infer_cond_when_undecided = [v1 = _v1, v2 = _v2, or_equal = _or_equal](
                                             const State & state, auto &, ProofLogger * const,
                                             const IntegerVariableCondition &) -> ReificationVerdict {
            // Aliased non-constant operands: v1<v2 never (when strict),
            // v1≤v2 always. Returning the resolved verdict here lets the
            // dispatcher pin cond at root instead of relying on bounds
            // shrinking to expose the contradiction.
            if (v1 == v2 && ! is_constant_variable(v1)) {
                if (or_equal)
                    return reification_verdict::MustHold{
                        .justification = JustifyUsingRUP{},
                        .reason = NoReason{}};
                else
                    return reification_verdict::MustNotHold{
                        .justification = JustifyUsingRUP{},
                        .reason = NoReason{}};
            }
            auto v1_bounds = state.bounds(v1), v2_bounds = state.bounds(v2);
            if (or_equal ? (v1_bounds.second <= v2_bounds.first) : (v1_bounds.second < v2_bounds.first)) {
                // v1 has to be less than (or equal): constraint must hold.
                return reification_verdict::MustHold{
                    .justification = JustifyUsingRUP{},
                    .reason = ExplicitReason{ReasonLiterals{{v1 <= v1_bounds.second, v2 >= v2_bounds.first}}}};
            }
            else if (or_equal ? (v1_bounds.first > v2_bounds.second) : (v1_bounds.first >= v2_bounds.second)) {
                // v1 has to be greater than (or equal): constraint cannot hold.
                return reification_verdict::MustNotHold{
                    .justification = JustifyUsingRUP{},
                    .reason = ExplicitReason{ReasonLiterals{{v1 >= v1_bounds.first, v2 <= v2_bounds.second}}}};
            }
            else
                return reification_verdict::StillUndecided{};
        };

        Triggers triggers{.on_bounds = {_v1, _v2}};
        install_reified_dispatcher(propagators, constraint_id(), _evaluated_cond, _reif_cond, triggers,
            std::move(enforce_constraint_must_hold),
            std::move(enforce_constraint_must_not_hold),
            std::move(infer_cond_when_undecided));
    }
}

auto ReifiedCompareLessThanOrMaybeEqual::s_expr(const ProofModel * const model) const -> SExpr
{
    auto & tracker = model->names_and_ids_tracker();

    auto reif_suffix = overloaded{
        [&](const reif::MustHold &) -> string { return ""; },
        [&](const reif::If &) -> string { return "_if"; },
        [&](const reif::Iff &) -> string { return "_iff"; },
        [&](const auto &) -> string { throw UnexpectedException{"Unexpected reification type in s_expr"}; }}
                           .visit(_reif_cond);

    // cake_pb_cp's names: less_than / less_equal / greater_than / greater_equal.
    string cmp = format("{}_{}{}",
        _vars_swapped ? "greater" : "less",
        _or_equal ? "equal" : "than",
        reif_suffix);

    vector<SExpr> terms{SExpr::atom(as_string(_constraint_id)), SExpr::atom(cmp)};
    if (auto cond = tracker.s_expr_term_of(_reif_cond))
        terms.push_back(std::move(*cond));
    // The constraint enforces _v1 <op> _v2. cake reads "less A B" as A<=B but
    // "greater A B" as A>=B, so for the greater form the operands are reversed:
    // "greater _v2 _v1" reads as _v2 >= _v1, i.e. _v1 <= _v2.
    terms.push_back(tracker.s_expr_term_of(_vars_swapped ? _v2 : _v1));
    terms.push_back(tracker.s_expr_term_of(_vars_swapped ? _v1 : _v2));

    return SExpr::list(std::move(terms));
}
