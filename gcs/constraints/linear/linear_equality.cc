#include <gcs/constraints/extensional_utils.hh>
#include <gcs/constraints/innards/reified_state.hh>
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
using std::is_same_v;
using std::make_pair;
using std::make_shared;
using std::move;
using std::nullopt;
using std::optional;
using std::pair;
using std::stringstream;
using std::unique_ptr;
using std::vector;

#if defined(__cpp_lib_print) && defined(__cpp_lib_format)
using std::print;
#else
using fmt::print;
#endif

ReifiedLinearEquality::ReifiedLinearEquality(WeightedSum coeff_vars, Integer value, ReificationCondition cond, LinearEqualityConsistency level,
    bool flipped_cond, std::optional<std::size_t> incremental_threshold) :
    _coeff_vars(move(coeff_vars)), _value(value), _reif_cond(cond), _level(level), _flipped_cond(flipped_cond),
    _incremental_threshold(incremental_threshold)
{
}

namespace
{

    template <typename CV_>
    auto build_table(const CV_ & coeff_vars, Integer value, ReificationCondition cond, State & state, ProofLogger * const logger)
        -> optional<ExtensionalData>
    {
        vector<vector<IntegerOrWildcard>> permitted;
        vector<Integer> current;

        vector<IntegerVariableID> vars;
        for (auto & cv : coeff_vars.terms) {
            auto var = get_var(cv);
            vars.push_back(var);
        }

        auto future_var_id = state.what_variable_id_will_be_created_next();

        WPBSum trail;
        function<void(ProofLogger * const)> search = [&](ProofLogger * const logger) {
            if (current.size() == coeff_vars.terms.size()) {
                Integer actual_value{0_i};
                for (const auto & [idx, cv] : enumerate(coeff_vars.terms)) {
                    actual_value += get_coeff(cv) * current[idx];
                }

                bool match = overloaded{
                    [&](const reif::MustHold &) { return actual_value == value; },      //
                    [&](const reif::MustNotHold &) { return actual_value != value; },   //
                    [&](const reif::If) -> bool { throw UnimplementedException{}; },    //
                    [&](const reif::NotIf) -> bool { throw UnimplementedException{}; }, //
                    [&](const reif::Iff) -> bool { throw UnimplementedException{}; }    //
                }
                                 .visit(cond);

                if (match) {
                    permitted.emplace_back(current.begin(), current.end());
                    if (logger && logger->get_assertion_level() == AssertionLevel::Off) {
                        Integer sel_value(permitted.size() - 1);
                        logger->names_and_ids_tracker().create_literals_for_introduced_variable_value(future_var_id, sel_value, "lineq");
                        trail += 1_i * (future_var_id == sel_value);

                        WPBSum forward_implication, reverse_implication;
                        forward_implication += Integer(coeff_vars.terms.size()) * (future_var_id != sel_value);
                        reverse_implication += 1_i * (future_var_id == sel_value);

                        for (const auto & [idx, cv] : enumerate(coeff_vars.terms)) {
                            forward_implication += 1_i * (get_var(cv) == current[idx]);
                            reverse_implication += 1_i * (get_var(cv) != current[idx]);
                        }

                        logger->emit_red_proof_line(forward_implication >= Integer(coeff_vars.terms.size()),
                            {{future_var_id == sel_value, FalseLiteral{}}}, ProofLevel::Current);
                        logger->emit_red_proof_line(reverse_implication >= 1_i, {{future_var_id == sel_value, TrueLiteral{}}}, ProofLevel::Current);
                    }
                }
            }
            else {
                const auto & var = get_var(coeff_vars.terms[current.size()]);
                for (auto val : state.each_value_mutable(var)) {
                    current.push_back(val);
                    search(logger);
                    current.pop_back();
                }
            }

            if (logger && logger->get_assertion_level() == AssertionLevel::Off) {
                WPBSum backtrack = trail;
                for (const auto & [idx, val] : enumerate(current))
                    backtrack += 1_i * (get_var(coeff_vars.terms[idx]) != val);

                logger->emit_rup_proof_line(backtrack >= 1_i, ProofLevel::Current);
            }
        };

        if (logger && logger->get_assertion_level() == AssertionLevel::Off)
            logger->emit_proof_comment("building GAC table for linear equality");
        search(logger);

        if (permitted.empty())
            return nullopt;

        auto sel = state.allocate_integer_variable_with_state(0_i, Integer(permitted.size() - 1));
        if (sel != future_var_id)
            throw UnexpectedException{"something went horribly wrong with variable IDs"};

        return ExtensionalData{sel, move(vars), move(permitted)};
    }
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
            _proof_line = model.add_labelled_constraint(
                as_string(_constraint_id), "le", "ge", "ReifiedLinearEquality", "unconditional sum", terms == _value, nullopt);
        }, //
        [&](const reif::MustNotHold &) {
            // condition is definitely false, the flag implies either greater or
            // less -- cake_pb_cp labels them gt (sum > value) / lt (sum < value),
            // on a single per-constraint selector b[id][ne] (cake's `nev`).
            auto neflag = model.create_proof_flag(_constraint_id, "ne");
            model.add_labelled_constraint(as_string(_constraint_id), "gt", "ReifiedLinearEquality", "not equals: greater half", terms >= _value + 1_i,
                HalfReifyOnConjunctionOf{{neflag}});
            model.add_labelled_constraint(as_string(_constraint_id), "lt", "ReifiedLinearEquality", "not equals: less half", terms <= _value - 1_i,
                HalfReifyOnConjunctionOf{{! neflag}});
        }, //
        [&](const reif::If & cond) {
            // The reified (if/iff) linear equalities are not chain-verified, so an
            // invented @c[id][le/ge] label is fine.
            _proof_line = model.add_labelled_constraint(as_string(constraint_id()), "le", "ge", "ReifiedLinearEquality", "unconditional sum",
                terms == _value, HalfReifyOnConjunctionOf{{cond.cond}});
        }, //
        [&](const reif::NotIf & cond) {
            // condition is definitely false, the flag implies either greater or less
            auto neflag = model.create_proof_flag("linne");
            model.add_constraint("ReifiedLinearEquality", "greater option", terms >= _value + 1_i, HalfReifyOnConjunctionOf{{cond.cond, neflag}});
            model.add_constraint("ReifiedLinearEquality", "less than option", terms <= _value - 1_i, HalfReifyOnConjunctionOf{{cond.cond, ! neflag}});
        }, //
        [&](const reif::Iff & cond) {
            // condition unknown, the condition implies it is neither greater nor less
            _proof_line = model.add_labelled_constraint(as_string(constraint_id()), "le", "ge", "ReifiedLinearEquality", "equals option",
                terms == _value, HalfReifyOnConjunctionOf{{cond.cond}});

            auto gtflag = model.create_proof_flag("lineqgt");
            model.add_constraint("ReifiedLinearEquality", "greater option", terms >= _value + 1_i, HalfReifyOnConjunctionOf{{gtflag}});
            auto ltflag = model.create_proof_flag("lineqlt");
            model.add_constraint("ReifiedLinearEquality", "less than option", terms <= _value - 1_i, HalfReifyOnConjunctionOf{{ltflag}});

            // lt + eq + gt >= 1
            model.add_constraint(
                "ReifiedLinearEquality", "one of less than, equals, greater than", WPBSum{} + 1_i * ltflag + 1_i * gtflag + 1_i * cond.cond >= 1_i);
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

    if (std::holds_alternative<consistency::GAC>(_level)) {
        visit(
            [&, modifier = modifier](auto & sanitised_cv) {
                // we're watching everything
                Triggers triggers;
                for (auto & cv : sanitised_cv.terms)
                    triggers.on_change.push_back(get_var(cv));

                auto data = make_shared<optional<ExtensionalData>>(nullopt);
                propagators.install_initialiser(
                    [data = data, coeff_vars = sanitised_cv, value = _value + modifier, cond = _reif_cond, owner = constraint_id()](
                        State & state, auto & inference, ProofLogger * const logger) {
                        *data = build_table(coeff_vars, value, cond, state, logger);
                        if (! data->has_value())
                            inference.infer(logger, FalseLiteral{}, JustifyUsingRUP{hints::LinearEquality{owner}}, ExplicitReason{ReasonLiterals{}});
                    },
                    InitialiserPriority::Expensive);

                propagators.install(
                    constraint_id(),
                    [data = data, owner = constraint_id()](const State & state, auto & inference, ProofLogger * const logger) -> PropagatorState {
                        if (data->has_value())
                            return propagate_extensional(data.get()->value(), state, inference, logger, hints::LinearEquality{owner});
                        else
                            return PropagatorState::DisableUntilBacktrack;
                    },
                    triggers);
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
                                return overloaded{
                                    [&](const evaluated_reif::MustHold & reif) {
                                        // we now know the condition definitely holds, so it's a linear equality
                                        if (inc_must_hold)
                                            return propagate_linear_incremental(sanitised_cv, value, state, inference, logger, true, proof_line,
                                                reif.cond, *inc_must_hold->first, inc_must_hold->second, hints::LinearEquality{owner});
                                        return propagate_linear(
                                            sanitised_cv, value, state, inference, logger, true, proof_line, reif.cond, hints::LinearEquality{owner});
                                    }, //
                                    [&](const evaluated_reif::MustNotHold &) {
                                        // we now know the condition definitely doesn't hold, so it's a linear not-equals
                                        return propagate_linear_not_equals(
                                            sanitised_cv, value, state, inference, logger, all_vars, hints::LinearNotEquals{owner});
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
                                                    inference.infer(
                                                        logger, *lit, JustifyUsingRUP{hints::LinearEquality{owner}}, generic_reason(all_vars));
                                                return PropagatorState::DisableUntilBacktrack;
                                            }
                                            else {
                                                if (auto lit = reif.cond_to_infer_if_constraint_must_not_hold())
                                                    inference.infer(
                                                        logger, *lit, JustifyUsingRUP{hints::LinearEquality{owner}}, generic_reason(all_vars));
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
                                                        inference.infer(
                                                            logger, *lit, JustifyUsingRUP{hints::LinearEquality{owner}}, generic_reason(all_vars));
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
                                                    inference.infer(
                                                        logger, *lit, JustifyUsingRUP{hints::LinearEquality{owner}}, generic_reason(all_vars));
                                                return PropagatorState::DisableUntilBacktrack;
                                            }
                                        }
                                    } //
                                }
                                    .visit(test_reification_condition(state, cond));
                            },
                            triggers);
                    },
                    sanitised_cv);
            } //
        }
            .visit(_evaluated_cond);
    }
}

auto ReifiedLinearEquality::s_expr(const ProofModel * const model) const -> SExpr
{
    auto & tracker = model->names_and_ids_tracker();

    auto [rei, cons] = overloaded{
        [&](const reif::MustHold &) { return make_pair(false, "lin_equals"); },                                      //
        [&](const reif::If &) { return make_pair(true, "lin_equals_if"); },                                          //
        [&](const reif::Iff &) { return make_pair(true, _flipped_cond ? "lin_not_equals_iff" : "lin_equals_iff"); }, //
        [&](const reif::MustNotHold &) { return make_pair(false, "lin_not_equals"); },                               //
        [&](const reif::NotIf &) { return make_pair(true, "lin_not_equals_if"); }                                    //
    }
                           .visit(_reif_cond);

    vector<SExpr> terms{SExpr::atom(as_string(_constraint_id)), SExpr::atom(cons)};
    if (rei)
        terms.push_back(*tracker.s_expr_term_of(_reif_cond));

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
    return make_unique<ReifiedLinearEquality>(WeightedSum{_coeff_vars}, _value, _reif_cond, _level, _flipped_cond, _incremental_threshold);
}

LinearEquality::LinearEquality(
    WeightedSum coeff_vars, Integer value, LinearEqualityConsistency level, std::optional<std::size_t> incremental_threshold) :
    ReifiedLinearEquality(coeff_vars, value, reif::MustHold{}, level, false, incremental_threshold)
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

LinearEqualityIf::LinearEqualityIf(WeightedSum coeff_vars, Integer value, Literal cond, LinearEqualityConsistency level) :
    ReifiedLinearEquality(move(coeff_vars), value, literal_to_reif<reif::If>(cond), level)
{
}

LinearEqualityIff::LinearEqualityIff(WeightedSum coeff_vars, Integer value, Literal cond, LinearEqualityConsistency level) :
    ReifiedLinearEquality(move(coeff_vars), value, literal_to_reif<reif::Iff>(cond), level)
{
}

LinearNotEquals::LinearNotEquals(WeightedSum coeff_vars, Integer value, LinearEqualityConsistency level) :
    ReifiedLinearEquality(move(coeff_vars), value, reif::MustNotHold{}, level)
{
}

LinearNotEqualsIf::LinearNotEqualsIf(WeightedSum coeff_vars, Integer value, Literal cond, LinearEqualityConsistency level) :
    ReifiedLinearEquality(move(coeff_vars), value, literal_to_reif<reif::NotIf>(cond), level)
{
}

LinearNotEqualsIff::LinearNotEqualsIff(WeightedSum coeff_vars, Integer value, Literal cond, LinearEqualityConsistency level) :
    ReifiedLinearEquality(move(coeff_vars), value, literal_to_reif<reif::Iff>(! cond), level, true)
{
}
