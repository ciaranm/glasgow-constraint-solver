#include <gcs/constraints/extensional_utils.hh>
#include <gcs/constraints/innards/reified_state.hh>
#include <gcs/constraints/innards/tabulation.hh>
#include <gcs/constraints/innards/triggers.hh>
#include <gcs/constraints/linear/hints.hh>
#include <gcs/constraints/linear/linear_equality.hh>
#include <gcs/constraints/linear/propagate.hh>
#include <gcs/constraints/linear/utils.hh>
#include <gcs/exception.hh>
#include <gcs/innards/inference_tracker.hh>
#include <gcs/innards/proofs/names_and_ids_tracker.hh>
#include <gcs/innards/proofs/proof_logger.hh>
#include <gcs/innards/proofs/proof_model.hh>
#include <gcs/innards/propagators.hh>
#include <gcs/innards/s_expr.hh>

#include <gcs/proof.hh>
#include <util/enumerate.hh>
#include <util/overloaded.hh>

#include <version>

#if defined(__cpp_lib_print) && defined(__cpp_lib_format)
#include <print>
#else
#include <fmt/ostream.h>
#endif

#include <cstddef>
#include <functional>
#include <memory>
#include <optional>
#include <sstream>
#include <type_traits>
#include <variant>
#include <vector>

using namespace gcs;
using namespace gcs::innards;

using std::decay_t;
using std::function;
using std::get;
using std::is_same_v;
using std::make_pair;
using std::make_shared;
using std::move;
using std::nullopt;
using std::optional;
using std::pair;
using std::string;
using std::stringstream;
using std::unique_ptr;
using std::vector;

#if defined(__cpp_lib_print) && defined(__cpp_lib_format)
using std::print;
#else
using fmt::print;
#endif

namespace
{
    // The "undecided" reification branch of ReifiedLinearEquality::install installs a
    // propagator whose body is a 4-way overloaded{}.visit nested inside a generic
    // (auto & inference) lambda that is itself inside a generic (auto & sanitised_cv)
    // visit lambda. That depth of nested generic lambdas triggers an MSVC internal
    // compiler error (C1001), so the visitor is hoisted here into a named function
    // template -- same behaviour, one fewer level of lambda nesting. The capture types
    // are deduced, so they need not be spelled out at the call site.
    template <typename SanitisedCV_, typename Cond_, typename ProofLine_, typename AllVars_, typename Owner_, typename IncMustHold_,
        typename Inference_>
    auto propagate_reified_linear_equality_when_undecided(const SanitisedCV_ & sanitised_cv, Integer value, const Cond_ & cond,
        const ProofLine_ & proof_line, const AllVars_ & all_vars, const Owner_ & owner, const IncMustHold_ & inc_must_hold, const State & state,
        Inference_ & inference, ProofLogger * const logger) -> PropagatorState
    {
        return overloaded{
            [&](const evaluated_reif::MustHold & reif) {
                // we now know the condition definitely holds, so it's a linear equality
                if (inc_must_hold)
                    return propagate_linear_incremental(sanitised_cv, value, state, inference, logger, true, proof_line, reif.cond,
                        *inc_must_hold->first, inc_must_hold->second, hints::LinearEquality{owner});
                return propagate_linear(sanitised_cv, value, state, inference, logger, true, proof_line, reif.cond, hints::LinearEquality{owner});
            }, //
            [&](const evaluated_reif::MustNotHold &) {
                // we now know the condition definitely doesn't hold, so it's a linear not-equals
                return propagate_linear_not_equals(sanitised_cv, value, state, inference, logger, all_vars, hints::LinearNotEquals{owner});
            },                                                                                          //
            [](const evaluated_reif::Deactivated &) { return PropagatorState::DisableUntilBacktrack; }, //
            [&](const evaluated_reif::Undecided & reif) {
                // we still don't know whether the condition holds. if we're down to a single unassigned
                // variable, we might have some information.
                auto single_unset = sanitised_cv.terms.end();
                Integer accum = 0_i;
                for (auto i = sanitised_cv.terms.begin(), i_end = sanitised_cv.terms.end(); i != i_end; ++i) {
                    auto val = state.optional_single_value(get_var(*i));
                    if (val)
                        accum += get_coeff(*i) * *val;
                    else {
                        if (single_unset != sanitised_cv.terms.end()) {
                            // at least two unset variables, do nothing for now
                            return PropagatorState::Enable;
                        }
                        else
                            single_unset = i;
                    }
                }

                if (single_unset == sanitised_cv.terms.end()) {
                    // every variable is assigned, so we know what the condition must be (if we're fully
                    // reified)
                    if (accum == value) {
                        if (auto lit = reif.cond_to_infer_if_constraint_must_hold())
                            inference.infer(logger, *lit, JustifyUsingRUP{hints::LinearEquality{owner}}, generic_reason(all_vars));
                        return PropagatorState::DisableUntilBacktrack;
                    }
                    else {
                        if (auto lit = reif.cond_to_infer_if_constraint_must_not_hold())
                            inference.infer(logger, *lit, JustifyUsingRUP{hints::LinearEquality{owner}}, generic_reason(all_vars));
                        return PropagatorState::DisableUntilBacktrack;
                    }
                }
                else {
                    // exactly one thing remaining. perhaps the value that would make the equality
                    // work doesn't occur in its domain?
                    Integer residual = value - accum;
                    if (0_i == residual % get_coeff(*single_unset)) {
                        Integer would_make_equal = residual / get_coeff(*single_unset);
                        if (! state.in_domain(get_var(*single_unset), would_make_equal)) {
                            // no way for the remaining variable to take that value, so the condition
                            // has to be false
                            if (auto lit = reif.cond_to_infer_if_constraint_must_not_hold())
                                inference.infer(logger, *lit, JustifyUsingRUP{hints::LinearEquality{owner}}, generic_reason(all_vars));
                            return PropagatorState::DisableUntilBacktrack;
                        }
                        else {
                            // could go either way, but this might change as more values are lost
                            return PropagatorState::Enable;
                        }
                    }
                    else {
                        // the value that would make the equality work isn't an integer, so the condition
                        // has to be false
                        if (auto lit = reif.cond_to_infer_if_constraint_must_not_hold())
                            inference.infer(logger, *lit, JustifyUsingRUP{hints::LinearEquality{owner}}, generic_reason(all_vars));
                        return PropagatorState::DisableUntilBacktrack;
                    }
                }
            } //
        }
            .visit(test_reification_condition(state, cond));
    }
}

ReifiedLinearEquality::ReifiedLinearEquality(WeightedSum coeff_vars, Integer value, ReificationCondition cond, bool flipped_cond) :
    _coeff_vars(move(coeff_vars)), _value(value), _reif_cond(cond), _flipped_cond(flipped_cond)
{
}

auto ReifiedLinearEquality::with_consistency(LinearEqualityConsistency level) -> ReifiedLinearEquality &
{
    _level = level;
    return *this;
}

auto ReifiedLinearEquality::with_incremental_threshold(std::optional<std::size_t> threshold) -> ReifiedLinearEquality &
{
    _incremental_threshold = threshold;
    return *this;
}

auto ReifiedLinearEquality::install(Propagators & propagators, State & initial_state, ProofModel * const optional_model) && -> void
{
    if (! prepare(propagators, initial_state, optional_model))
        return;

    if (optional_model)
        define_proof_model(*optional_model);

    install_propagators(propagators, initial_state);
}

auto ReifiedLinearEquality::prepare(Propagators &, State & initial_state, ProofModel * const) -> bool
{
    _evaluated_cond = test_reification_condition(initial_state, _reif_cond);
    return true;
}

auto ReifiedLinearEquality::define_proof_model(ProofModel & model) -> void
{
    WPBSum terms;
    for (auto & [c, v] : _coeff_vars.terms)
        terms += c * v;

    overloaded{
        [&](const reif::MustHold &) {
            // condition is definitely true, it's just an inequality -- cake_pb_cp
            // labels the equality halves le (sum <= value) / ge (sum >= value).
            _proof_line = model.add_labelled_constraint(_constraint_id, "le", "ge", terms == _value, nullopt);
        }, //
        [&](const reif::MustNotHold &) {
            // condition is definitely false, the flag implies either greater or
            // less -- cake_pb_cp labels them gt (sum > value) / lt (sum < value),
            // on a single per-constraint selector b[id][ne] (cake's `nev`).
            auto neflag = model.create_proof_flag(_constraint_id, "ne");
            model.add_labelled_constraint(_constraint_id, "gt", terms >= _value + 1_i, HalfReifyOnConjunctionOf{{neflag}});
            model.add_labelled_constraint(_constraint_id, "lt", terms <= _value - 1_i, HalfReifyOnConjunctionOf{{! neflag}});
        }, //
        [&](const reif::If & cond) {
            // The reified (if/iff) linear equalities are not chain-verified, so an
            // invented @c[id][le/ge] label is fine.
            _proof_line = model.add_labelled_constraint(constraint_id(), "le", "ge", terms == _value, HalfReifyOnConjunctionOf{{cond.cond}});
        }, //
        [&](const reif::NotIf & cond) {
            // condition is definitely false, the flag implies either greater or less
            auto neflag = model.create_proof_flag("linne");
            model.add_constraint(terms >= _value + 1_i, HalfReifyOnConjunctionOf{{cond.cond, neflag}});
            model.add_constraint(terms <= _value - 1_i, HalfReifyOnConjunctionOf{{cond.cond, ! neflag}});
        }, //
        [&](const reif::Iff & cond) {
            // condition unknown, the condition implies it is neither greater nor less
            _proof_line = model.add_labelled_constraint(constraint_id(), "le", "ge", terms == _value, HalfReifyOnConjunctionOf{{cond.cond}});

            auto gtflag = model.create_proof_flag("lineqgt");
            model.add_constraint(terms >= _value + 1_i, HalfReifyOnConjunctionOf{{gtflag}});
            auto ltflag = model.create_proof_flag("lineqlt");
            model.add_constraint(terms <= _value - 1_i, HalfReifyOnConjunctionOf{{ltflag}});

            // lt + eq + gt >= 1
            model.add_constraint(WPBSum{} + 1_i * ltflag + 1_i * gtflag + 1_i * cond.cond >= 1_i);
        } //
    }
        .visit(_reif_cond);
}

auto ReifiedLinearEquality::install_propagators(Propagators & propagators, State & initial_state) -> void
{
    auto [sanitised_cv, modifier] = tidy_up_linear(_coeff_vars);

    vector<IntegerVariableID> all_vars;
    visit(
        [&](const auto & sanitised_cv) {
            for (const auto & cv : sanitised_cv.terms)
                all_vars.push_back(get_var(cv));
        },
        sanitised_cv);
    overloaded{
        [&](const reif::MustHold &) {},                                       //
        [&](const reif::MustNotHold &) {},                                    //
        [&](const reif::If & cond) { all_vars.push_back(cond.cond.var); },    //
        [&](const reif::NotIf & cond) { all_vars.push_back(cond.cond.var); }, //
        [&](const reif::Iff & cond) { all_vars.push_back(cond.cond.var); }    //
    }
        .visit(_reif_cond);

    if (std::holds_alternative<consistency::Tabulated>(_level)) {
        visit(
            [&, modifier = modifier](auto & sanitised_cv) {
                TabulationVariables enum_vars;
                for (auto & cv : sanitised_cv.terms)
                    enum_vars.position_of(get_var(cv));

                // the enumeration, in-proof selector introduction, and
                // extensional wiring live in install_tabulation, and the
                // reification handling in reify_tabulation; all that is ours
                // is the base acceptance test over the term positions, and
                // solving the equality for each term as the determined values.
                auto base_accept = [coeff_vars = sanitised_cv, value = _value + modifier](const vector<Integer> & current) -> bool {
                    Integer actual_value{0_i};
                    for (const auto & [idx, cv] : enumerate(coeff_vars.terms))
                        actual_value += get_coeff(cv) * current[idx];
                    return actual_value == value;
                };

                // every term variable is a function of the others when the
                // equality is enforced (the sanitised terms have distinct
                // variables and nonzero coefficients), pinned by unit
                // propagation on the possibly half-reified equality;
                // reify_tabulation drops the claims when no branch enforces
                // it.
                vector<DeterminedVariable> determined;
                for (const auto & [idx, cv] : enumerate(sanitised_cv.terms))
                    determined.push_back({get_var(cv),
                        [coeff_vars = sanitised_cv, value = _value + modifier, idx = idx](const vector<Integer> & current) -> optional<Integer> {
                            Integer other{0_i};
                            for (const auto & [jdx, cw] : enumerate(coeff_vars.terms))
                                if (jdx != idx)
                                    other += get_coeff(cw) * current[jdx];
                            auto coeff = get_coeff(coeff_vars.terms[idx]);
                            if ((value - other) % coeff != 0_i)
                                return nullopt;
                            return (value - other) / coeff;
                        }});

                auto reified = reify_tabulation(_reif_cond, enum_vars, base_accept, move(determined));

                install_tabulation<hints::LinearEquality>(propagators, constraint_id(), enum_vars.vars(), move(reified.determined),
                    move(reified.reification), move(reified.accept), "lineq", "building GAC table for linear equality");
            },
            sanitised_cv);
    }
    else {
        overloaded{
            [&](const evaluated_reif::MustHold & reif) {
                // condition is definitely true; with no variable terms left the sum is just
                // the (folded-out) constant part, so the equality holds iff _value + modifier == 0
                if (visit([](const auto & s) { return s.terms.empty(); }, sanitised_cv) && modifier != -_value) {
                    propagators.install_initialiser(
                        [reason_from_cond = reif.cond, owner = constraint_id()](const State &, auto & inference, ProofLogger * const logger) {
                            inference.infer(logger, FalseLiteral{}, JustifyUsingRUP{hints::LinearEquality{owner}},
                                ExplicitReason{ReasonLiterals{{reason_from_cond}}});
                        });
                }

                // easy case: we're doing bounds consistency, and the condition is fixed
                Triggers triggers;
                for (auto & [_, v] : _coeff_vars.terms)
                    triggers.on_bounds.push_back(v);

                visit(
                    [&, modifier = modifier](const auto & lin) {
                        // Wide enough? Use the incremental propagator (folds instantiated terms
                        // out), which needs backtrackable constraint state set up here. Otherwise
                        // the cheaper stateless path, where folding bookkeeping does not pay off.
                        if (lin.terms.size() >= _incremental_threshold.value_or(default_linear_incremental_threshold())) {
                            auto active = make_shared<vector<std::size_t>>(lin.terms.size());
                            for (std::size_t i = 0; i != lin.terms.size(); ++i)
                                (*active)[i] = i;
                            auto handle = initial_state.add_constraint_state(LinearIncrementalState{lin.terms.size(), 0_i});
                            propagators.install(
                                constraint_id(),
                                [modifier = modifier, lin = lin, value = _value, proof_line = _proof_line, reason_from_cond = reif.cond,
                                    owner = constraint_id(), active = active,
                                    handle = handle](const State & state, auto & inference, ProofLogger * const logger) {
                                    return propagate_linear_incremental(lin, value + modifier, state, inference, logger, true, proof_line,
                                        reason_from_cond, *active, handle, hints::LinearEquality{owner});
                                },
                                triggers);
                        }
                        else {
                            propagators.install(
                                constraint_id(),
                                [modifier = modifier, lin = lin, value = _value, proof_line = _proof_line, reason_from_cond = reif.cond,
                                    owner = constraint_id()](const State & state, auto & inference, ProofLogger * const logger) {
                                    return propagate_linear(lin, value + modifier, state, inference, logger, true, proof_line, reason_from_cond,
                                        hints::LinearEquality{owner});
                                },
                                triggers);
                        }
                    },
                    sanitised_cv);
            }, //
            [&](const evaluated_reif::MustNotHold & reif) {
                // condition is definitely false on a full reification; with no variable terms left
                // the equality _value + modifier == 0 must NOT hold, so it is violated iff it does
                if (visit([](const auto & s) { return s.terms.empty(); }, sanitised_cv) && modifier == -_value) {
                    propagators.install_initialiser(
                        [reason_from_cond = reif.cond, owner = constraint_id()](const State &, auto & inference, ProofLogger * const logger) {
                            inference.infer(logger, FalseLiteral{}, JustifyUsingRUP{hints::LinearEquality{owner}},
                                ExplicitReason{ReasonLiterals{{reason_from_cond}}});
                        });
                }

                // strictly speaking, we care when we're down to only one variable left unassigned, and then there's one
                // value it potentially mustn't have
                Triggers triggers;
                for (auto & [_, v] : _coeff_vars.terms)
                    triggers.on_change.push_back(v);

                visit(
                    [&, modifier = modifier](const auto & sanitised_cv) {
                        propagators.install(
                            constraint_id(),
                            [sanitised_cv = sanitised_cv, value = _value + modifier, all_vars = move(all_vars), owner = constraint_id()](
                                const State & state, auto & inference, ProofLogger * const logger) -> PropagatorState {
                                return propagate_linear_not_equals(
                                    sanitised_cv, value, state, inference, logger, all_vars, hints::LinearNotEquals{owner});
                            },
                            triggers);
                    },
                    sanitised_cv);
            }, //
            [&](const evaluated_reif::Deactivated &) {
                // condition is definitely false, but on a half reification, so we do nothing
            }, //
            [&](const evaluated_reif::Undecided & reif) {
                // we care when the condition changes, or once we're down to a single unassigned variable
                // because that might force the condition one way or (possibly) another.
                Triggers triggers;
                for (auto & [_, v] : _coeff_vars.terms)
                    triggers.on_change.push_back(v);
                add_trigger_for(triggers, reif.cond);

                visit(
                    [&, modifier = modifier](const auto & sanitised_cv) {
                        // Only the must-hold branch below is a bounds-sum linear equality that can
                        // fold incrementally; the must-not-hold branch is a different (not-equals)
                        // algorithm and the undecided branch only inspects a single residual var, so
                        // neither uses the fold state. The must-hold state runs (repeatedly) only
                        // while the condition is decided true in a subtree, backtracks on its own
                        // handle, and re-folds any terms instantiated while another branch was active.
                        std::optional<std::pair<std::shared_ptr<vector<std::size_t>>, ConstraintStateHandle>> inc_must_hold;
                        if (sanitised_cv.terms.size() >= _incremental_threshold.value_or(default_linear_incremental_threshold())) {
                            auto active = make_shared<vector<std::size_t>>(sanitised_cv.terms.size());
                            for (std::size_t i = 0; i != sanitised_cv.terms.size(); ++i)
                                (*active)[i] = i;
                            auto handle = initial_state.add_constraint_state(LinearIncrementalState{sanitised_cv.terms.size(), 0_i});
                            inc_must_hold = std::pair{active, handle};
                        }

                        propagators.install(
                            constraint_id(),
                            [sanitised_cv = sanitised_cv, value = _value + modifier, cond = _reif_cond, proof_line = _proof_line,
                                all_vars = move(all_vars), owner = constraint_id(),
                                inc_must_hold = inc_must_hold](const State & state, auto & inference,
                                ProofLogger * const logger) -> PropagatorState { // This comment is needed to stop clang-format exploding
                                return propagate_reified_linear_equality_when_undecided(
                                    sanitised_cv, value, cond, proof_line, all_vars, owner, inc_must_hold, state, inference, logger);
                            },
                            triggers);
                    },
                    sanitised_cv);
            } //
        }
            .visit(_evaluated_cond);
    }
}

auto ReifiedLinearEquality::constraint_type() const -> std::string
{
    return overloaded{
        [](const reif::MustHold &) -> string { return "lin_equals"; },                                //
        [](const reif::If &) -> string { return "lin_equals"; },                                      //
        [&](const reif::Iff &) -> string { return _flipped_cond ? "lin_not_equals" : "lin_equals"; }, //
        [](const reif::MustNotHold &) -> string { return "lin_not_equals"; },                         //
        [](const reif::NotIf &) -> string { return "lin_not_equals"; }                                //
    }
        .visit(_reif_cond);
}

auto ReifiedLinearEquality::s_expr(const ProofModel * const model) const -> SExpr
{
    auto & tracker = model->names_and_ids_tracker();

    auto [rei, suffix] = overloaded{
        [&](const reif::MustHold &) { return make_pair(false, ""); },    //
        [&](const reif::If &) { return make_pair(true, "_if"); },        //
        [&](const reif::Iff &) { return make_pair(true, "_iff"); },      //
        [&](const reif::MustNotHold &) { return make_pair(false, ""); }, //
        [&](const reif::NotIf &) { return make_pair(true, "_if"); }      //
    }
                             .visit(_reif_cond);

    vector<SExpr> terms{SExpr::atom(as_string(_constraint_id)), SExpr::atom(constraint_type() + suffix)};
    if (rei) {
        // A flipped iff stores the negated condition (the equality holds iff NOT
        // the user's condition), but the not_equals_iff keyword already carries
        // the negation: cake reads (r lin_not_equals_iff (cond) ...) as cond <=>
        // sum != value. Emit the user's original condition, not the stored one,
        // or the two negations cancel into the opposite constraint.
        auto cond_to_write = _flipped_cond ? ReificationCondition{reif::Iff{! get<reif::Iff>(_reif_cond).cond}} : _reif_cond;
        terms.push_back(*tracker.s_expr_term_of(cond_to_write));
    }

    vector<SExpr> coeff_vars;
    for (const auto & [c, v] : _coeff_vars.terms) {
        coeff_vars.push_back(SExpr::atom(c.to_string()));
        coeff_vars.push_back(tracker.s_expr_term_of(v));
    }
    terms.push_back(SExpr::list(std::move(coeff_vars)));
    terms.push_back(SExpr::atom(_value.to_string()));

    return SExpr::list(std::move(terms));
}

auto ReifiedLinearEquality::clone() const -> unique_ptr<Constraint>
{
    auto cloned = make_unique<ReifiedLinearEquality>(WeightedSum{_coeff_vars}, _value, _reif_cond, _flipped_cond);
    cloned->with_consistency(_level).with_incremental_threshold(_incremental_threshold);
    return cloned;
}

LinearEquality::LinearEquality(WeightedSum coeff_vars, Integer value) : ReifiedLinearEquality(move(coeff_vars), value, reif::MustHold{})
{
}

namespace
{
    template <typename T_>
    auto literal_to_reif(const Literal & cond) -> ReificationCondition
    {
        return overloaded{
            [&](const TrueLiteral &) -> ReificationCondition { return reif::MustHold{}; },          //
            [&](const FalseLiteral &) -> ReificationCondition { return reif::MustNotHold{}; },      //
            [&](const IntegerVariableCondition & cond) -> ReificationCondition { return T_{cond}; } //
        }
            .visit(cond);
    }
}

LinearEqualityIf::LinearEqualityIf(WeightedSum coeff_vars, Integer value, Literal cond) :
    ReifiedLinearEquality(move(coeff_vars), value, literal_to_reif<reif::If>(cond))
{
}

LinearEqualityIff::LinearEqualityIff(WeightedSum coeff_vars, Integer value, Literal cond) :
    ReifiedLinearEquality(move(coeff_vars), value, literal_to_reif<reif::Iff>(cond))
{
}

LinearNotEquals::LinearNotEquals(WeightedSum coeff_vars, Integer value) : ReifiedLinearEquality(move(coeff_vars), value, reif::MustNotHold{})
{
}

LinearNotEqualsIf::LinearNotEqualsIf(WeightedSum coeff_vars, Integer value, Literal cond) :
    ReifiedLinearEquality(move(coeff_vars), value, literal_to_reif<reif::NotIf>(cond))
{
}

LinearNotEqualsIff::LinearNotEqualsIff(WeightedSum coeff_vars, Integer value, Literal cond) :
    ReifiedLinearEquality(move(coeff_vars), value, literal_to_reif<reif::Iff>(! cond), true)
{
}
