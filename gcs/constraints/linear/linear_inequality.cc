#include <gcs/constraints/linear/linear_inequality.hh>
#include <gcs/constraints/linear/propagate.hh>
#include <gcs/constraints/linear/utils.hh>
#include <gcs/innards/inference_tracker.hh>
#include <gcs/innards/proofs/proof_logger.hh>
#include <gcs/innards/proofs/proof_model.hh>
#include <gcs/innards/proofs/variable_constraints_tracker.hh>
#include <gcs/innards/propagators.hh>
#include <gcs/innards/state.hh>

#include <sstream>

using namespace gcs;
using namespace gcs::innards;

using std::nullopt;
using std::optional;
using std::pair;
using std::string;
using std::stringstream;
using std::unique_ptr;
using std::variant;
using std::vector;

LinearInequalityIff::LinearInequalityIff(WeightedSum coeff_vars, Integer value, Literal cond) :
    _coeff_vars(move(coeff_vars)),
    _value(value),
    _cond(cond)
{
}

auto LinearInequalityIff::clone() const -> unique_ptr<Constraint>
{
    return make_unique<LinearInequalityIff>(WeightedSum{_coeff_vars}, _value, _cond);
}

namespace
{
    auto get_var(const PositiveOrNegative<SimpleIntegerVariableID> & cv) -> SimpleIntegerVariableID
    {
        return cv.variable;
    }

    auto get_var(const Weighted<SimpleIntegerVariableID> & cv) -> SimpleIntegerVariableID
    {
        return cv.variable;
    }

    auto get_var(const SimpleIntegerVariableID & cv) -> SimpleIntegerVariableID
    {
        return cv;
    }

    auto get_coeff(const PositiveOrNegative<SimpleIntegerVariableID> & cv) -> Integer
    {
        return cv.positive ? 1_i : -1_i;
    }

    auto get_coeff(const Weighted<SimpleIntegerVariableID> & cv) -> Integer
    {
        return cv.coefficient;
    }

    auto get_coeff(const SimpleIntegerVariableID &) -> Integer
    {
        return 1_i;
    }

    auto justify_cond(const State & state, const auto & coeff_vars, ProofLogger & logger,
        const ProofLine & proof_line) -> void
    {
        vector<pair<Integer, variant<ProofLine, string>>> terms_to_sum;
        terms_to_sum.emplace_back(1_i, proof_line);

        for (const auto & cv : coeff_vars.terms) {
            // the following line of logic is definitely correct until you inevitably
            // discover otherwise
            bool upper = (get_coeff(cv) < 0_i);

            auto literal_defining_proof_line = logger.variable_constraints_tracker().need_pol_item_defining_literal(
                upper ? get_var(cv) < state.upper_bound(get_var(cv) + 1_i) : get_var(cv) >= state.lower_bound(get_var(cv)));

            terms_to_sum.emplace_back(abs(get_coeff(cv)), literal_defining_proof_line);
        }

        stringstream step;
        step << "p";
        bool first = true;
        for (auto & c_and_l : terms_to_sum) {
            visit([&](const auto & l) {
                if (c_and_l.first == 1_i)
                    step << " " << l;
                else
                    step << " " << l << " " << c_and_l.first << " *";
            },
                c_and_l.second);
            if (! first)
                step << " +";
            first = false;
        }
        logger.emit_proof_line(step.str(), ProofLevel::Temporary);
    }
}

auto LinearInequalityIff::install(Propagators & propagators, State & state, ProofModel * const optional_model) && -> void
{
    optional<ProofLine> proof_line;
    if (optional_model) {
        WeightedPseudoBooleanSum terms;
        for (auto & [c, v] : _coeff_vars.terms)
            terms += c * v;
        overloaded{
            [&](const TrueLiteral &) {
                proof_line = optional_model->add_constraint(terms <= _value, nullopt);
            },
            [&](const FalseLiteral &) {
                proof_line = optional_model->add_constraint(terms >= _value + 1_i, nullopt);
            },
            [&](const IntegerVariableCondition & cond) {
                proof_line = optional_model->add_constraint(terms <= _value, HalfReifyOnConjunctionOf{cond});
                optional_model->add_constraint(terms >= _value + 1_i, HalfReifyOnConjunctionOf{! cond});
            }}
            .visit(_cond);
    }

    auto [sanitised_cv, modifier] = tidy_up_linear(_coeff_vars);

    // empty sum? we know what the condition must be.
    if (visit([](const auto & s) { return s.terms.empty(); }, sanitised_cv)) {
        propagators.install_initialiser([modifier = modifier, value = _value, cond = _cond](
                                            const State &, InferenceTracker & inference, ProofLogger * const logger) -> void {
            inference.infer(logger, 0_i <= value + modifier ? cond : ! cond, JustifyUsingRUP{}, Reason{});
        });
    }

    // we care when bounds change, and when the condition changes.
    Triggers triggers;
    for (auto & [_, v] : _coeff_vars.terms)
        triggers.on_bounds.push_back(v);

    overloaded{
        [&](const TrueLiteral &) {},
        [&](const FalseLiteral &) {},
        [&](const IntegerVariableCondition & cond) { triggers.on_change.push_back(cond.var); }}
        .visit(_cond);

    // do we know upfront what the condition is?
    switch (state.test_literal(_cond)) {
    case LiteralIs::DefinitelyTrue: {
        // definitely true, it's a less-than-or-equal
        visit(
            [&, modifier = modifier](const auto & lin) {
                propagators.install([modifier = modifier, lin = lin, value = _value, cond = _cond, proof_line = proof_line](
                                        const State & state, InferenceTracker & inference, ProofLogger * const logger) {
                    return propagate_linear(lin, value + modifier, state, inference, logger, false, proof_line, cond);
                },
                    triggers, "linear inequality");
            },
            sanitised_cv);
    } break;

    case LiteralIs::DefinitelyFalse: {
        // definitely false, it's a greater-than
        auto neg_coeff_vars = _coeff_vars;
        for (auto & v : neg_coeff_vars.terms)
            v.coefficient = -v.coefficient;
        auto [sanitised_neg_cv, neg_modifier] = tidy_up_linear(neg_coeff_vars);
        visit(
            [&, neg_modifier = neg_modifier](const auto & lin) {
                propagators.install([neg_modifier = neg_modifier, lin = lin, value = -_value - 1_i, cond = _cond, proof_line = proof_line](
                                        const State & state, InferenceTracker & inference, ProofLogger * const logger) {
                    return propagate_linear(lin, value + neg_modifier, state, inference, logger, false, *proof_line + 1, ! cond);
                },
                    triggers, "linear inequality");
            },
            sanitised_neg_cv);
    } break;

    case LiteralIs::Undecided: {
        // condition wasn't known at compile time. keep both the satisfiable and unsatisfiable
        // forms of the inequality around, and then see if the condition is known or can be
        // inferred.
        auto neg_coeff_vars = _coeff_vars;
        for (auto & v : neg_coeff_vars.terms)
            v.coefficient = -v.coefficient;
        auto [sanitised_neg_cv, neg_modifier] = tidy_up_linear(neg_coeff_vars);

        vector<IntegerVariableID> vars;
        visit([&](const auto & sanitised_cv) {
            for (const auto & cv : sanitised_cv.terms)
                vars.push_back(get_var(cv));
        },
            sanitised_cv);

        visit([&, modifier = modifier, neg_modifier = neg_modifier](const auto & sanitised_cv, const auto & sanitised_neg_cv) -> void {
            propagators.install([cond = _cond, sanitised_cv = sanitised_cv, sanitised_neg_cv = sanitised_neg_cv,
                                    value = _value, modifier = modifier, neg_modifier = neg_modifier, proof_line = proof_line,
                                    vars = vars](
                                    const State & state, InferenceTracker & inference, ProofLogger * const logger) {
                switch (state.test_literal(cond)) {
                case LiteralIs::DefinitelyTrue: {
                    return propagate_linear(sanitised_cv, value + modifier, state, inference, logger, false, proof_line, cond);
                } break;
                case LiteralIs::DefinitelyFalse: {
                    return propagate_linear(sanitised_neg_cv, -value + neg_modifier - 1_i, state, inference, logger, false,
                        *proof_line + 1, ! cond);
                } break;
                case LiteralIs::Undecided: {
                    // still don't know. see whether the condition is forced either way.
                    Integer min_possible = 0_i, max_possible = 0_i;
                    for (const auto & cv : sanitised_cv.terms) {
                        auto bounds = state.bounds(get_var(cv));
                        if (get_coeff(cv) >= 0_i) {
                            min_possible += get_coeff(cv) * bounds.first;
                            max_possible += get_coeff(cv) * bounds.second;
                        }
                        else {
                            min_possible += get_coeff(cv) * bounds.second;
                            max_possible += get_coeff(cv) * bounds.first;
                        }
                    }

                    if (min_possible > value + modifier) {
                        auto just = [&](const Reason &) { return justify_cond(state, sanitised_cv, *logger, *proof_line); };
                        inference.infer(logger, ! cond, JustifyExplicitly{just}, generic_reason(state, vars));
                        return PropagatorState::Enable;
                    }
                    else if (max_possible <= value + modifier) {
                        auto just = [&](const Reason &) { return justify_cond(state, sanitised_neg_cv, *logger, *proof_line + 1); };
                        inference.infer(logger, cond, JustifyExplicitly{just}, generic_reason(state, vars));
                        return PropagatorState::Enable;
                    }
                    else
                        return PropagatorState::Enable;
                } break;
                }
                throw NonExhaustiveSwitch{};
            },
                triggers, "linear inequality");
        },
            sanitised_cv, sanitised_neg_cv);
    } break;
    }
}

auto LinearInequalityIff::describe_for_proof() -> std::string
{
    return "linear inequality";
}
