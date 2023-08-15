#include <gcs/constraints/linear_equality.hh>
#include <gcs/exception.hh>
#include <gcs/innards/extensional_utils.hh>
#include <gcs/innards/linear_utils.hh>
#include <gcs/innards/proof.hh>
#include <gcs/innards/propagators.hh>

#include <util/enumerate.hh>
#include <util/overloaded.hh>

#include <functional>
#include <memory>
#include <sstream>
#include <vector>

using namespace gcs;
using namespace gcs::innards;

using std::function;
using std::make_shared;
using std::move;
using std::nullopt;
using std::optional;
using std::pair;
using std::stringstream;
using std::unique_ptr;
using std::vector;

LinearEquality::LinearEquality(WeightedSum coeff_vars, Integer value, bool gac) :
    _coeff_vars(move(coeff_vars)),
    _value(value),
    _gac(gac)
{
}

auto LinearEquality::clone() const -> unique_ptr<Constraint>
{
    return make_unique<LinearEquality>(WeightedSum{_coeff_vars}, _value, _gac);
}

namespace
{
    auto to_coeff(bool v)
    {
        return v ? 1_i : -1_i;
    }

    auto to_coeff(Integer v)
    {
        return v;
    }

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

    auto get_coeff(const PositiveOrNegative<SimpleIntegerVariableID> & cv) -> bool
    {
        return cv.positive;
    }

    auto get_coeff(const Weighted<SimpleIntegerVariableID> & cv) -> Integer
    {
        return cv.coefficient;
    }

    auto get_coeff(const SimpleIntegerVariableID &) -> Integer
    {
        return 1_i;
    }

    template <typename CV_>
    auto build_table(const CV_ & coeff_vars, Integer value, State & state) -> ExtensionalData
    {
        vector<vector<Integer>> permitted;
        vector<Integer> current;

        vector<IntegerVariableID> vars;
        for (auto & cv : coeff_vars.terms) {
            auto var = get_var(cv);
            vars.push_back(var);
        }

        auto future_var_id = state.what_variable_id_will_be_created_next();

        WeightedPseudoBooleanSum trail;
        function<void(Proof *, vector<ProofLine> *)> search = [&](Proof * maybe_proof, vector<ProofLine> * to_delete) {
            if (current.size() == coeff_vars.terms.size()) {
                Integer actual_value{0_i};
                for (const auto & [idx, cv] : enumerate(coeff_vars.terms)) {
                    auto coeff = get_coeff(cv);
                    actual_value += to_coeff(coeff) * current[idx];
                }
                if (actual_value == value) {
                    permitted.push_back(current);
                    if (maybe_proof) {
                        Integer sel_value(permitted.size() - 1);
                        maybe_proof->create_literals_for_introduced_variable_value(future_var_id, sel_value, "lineq");
                        trail += 1_i * (future_var_id == sel_value);

                        WeightedPseudoBooleanSum forward_implication, reverse_implication;
                        forward_implication += Integer(coeff_vars.terms.size()) * (future_var_id != sel_value);
                        reverse_implication += 1_i * (future_var_id == sel_value);

                        for (const auto & [idx, cv] : enumerate(coeff_vars.terms)) {
                            forward_implication += 1_i * (get_var(cv) == current[idx]);
                            reverse_implication += 1_i * (get_var(cv) != current[idx]);
                        }

                        maybe_proof->emit_red_proof_line(forward_implication >= Integer(coeff_vars.terms.size()),
                            {{future_var_id == sel_value, FalseLiteral{}}});
                        maybe_proof->emit_red_proof_line(reverse_implication >= 1_i,
                            {{future_var_id == sel_value, TrueLiteral{}}});
                    }
                }
            }
            else {
                const auto & var = get_var(coeff_vars.terms[current.size()]);
                state.for_each_value(var, [&](Integer val) {
                    current.push_back(val);
                    search(maybe_proof, to_delete);
                    current.pop_back();
                });
            }

            if (maybe_proof) {
                WeightedPseudoBooleanSum backtrack = trail;
                for (const auto & [idx, val] : enumerate(current))
                    backtrack += 1_i * (get_var(coeff_vars.terms[idx]) != val);

                auto line = maybe_proof->emit_rup_proof_line(backtrack >= 1_i);
                if (! current.empty())
                    to_delete->push_back(line);
            }
        };

        if (state.maybe_proof()) {
            state.infer_true(JustifyExplicitly{[&](Proof & proof, vector<ProofLine> & to_delete) {
                proof.emit_proof_comment("building GAC table for linear equality");
                search(&proof, &to_delete);
            }});
        }
        else
            search(nullptr, nullptr);

        auto sel = state.allocate_integer_variable_with_state(0_i, Integer(permitted.size() - 1));
        if (sel != future_var_id)
            throw UnexpectedException{"something went horribly wrong with variable IDs"};

        return ExtensionalData{sel, move(vars), move(permitted)};
    }
}

auto LinearEquality::install(Propagators & propagators, State & initial_state) && -> void
{
    optional<ProofLine> proof_line;
    if (propagators.want_definitions()) {
        WeightedPseudoBooleanSum terms;
        for (auto & [c, v] : _coeff_vars.terms)
            terms += c * v;
        proof_line = propagators.define(initial_state, terms == _value, nullopt).first.value();
    }

    auto [sanitised_cv, modifier] = tidy_up_linear(_coeff_vars);

    if (visit([](const auto & s) { return s.terms.empty(); }, sanitised_cv) && modifier != _value) {
        propagators.install([](State & state) -> pair<Inference, PropagatorState> {
            return pair{state.infer(FalseLiteral{}, JustifyUsingRUP{}), PropagatorState::Enable};
        },
            Triggers{}, "empty linear equality");
    }

    Triggers triggers;
    for (auto & [_, v] : _coeff_vars.terms)
        triggers.on_bounds.push_back(v);

    overloaded{
        [&, &modifier = modifier](const SumOf<Weighted<SimpleIntegerVariableID>> & lin) {
            propagators.install([modifier = modifier, lin = lin, value = _value, proof_line = proof_line](State & state) {
                return propagate_linear(lin, value + modifier, state, true, proof_line);
            },
                triggers, "linear equality");
        },
        [&, &modifier = modifier](const SumOf<PositiveOrNegative<SimpleIntegerVariableID>> & sum) {
            propagators.install([modifier = modifier, sum = sum, value = _value, proof_line = proof_line](State & state) {
                return propagate_sum(sum, value + modifier, state, true, proof_line);
            },
                triggers, "linear equality");
        },
        [&, &modifier = modifier](const SumOf<SimpleIntegerVariableID> & sum) {
            propagators.install([modifier = modifier, sum = sum, value = _value, proof_line = proof_line](State & state) mutable {
                return propagate_sum_all_positive(sum, value + modifier, state, true, proof_line);
            },
                triggers, "linear equality");
        }}
        .visit(sanitised_cv);

    if (_gac) {
        visit([&, modifier = modifier](auto & sanitised_cv) {
            Triggers triggers;
            for (auto & cv : sanitised_cv.terms)
                triggers.on_change.push_back(get_var(cv));

            auto data = make_shared<optional<ExtensionalData>>(nullopt);
            propagators.install_initialiser([data = data, coeff_vars = sanitised_cv, value = _value + modifier](State & state) -> void {
                *data = build_table(coeff_vars, value, state);
            });
            propagators.install([data = data](State & state) -> pair<Inference, PropagatorState> {
                return propagate_extensional(data.get()->value(), state);
            },
                triggers, "lin_eq_gac");
        },
            sanitised_cv);
    }
}

auto LinearEquality::describe_for_proof() -> std::string
{
    return "linear equality";
}

LinearInequality::LinearInequality(WeightedSum coeff_vars, Integer value) :
    _coeff_vars(move(coeff_vars)),
    _value(value)
{
}

auto LinearInequality::clone() const -> unique_ptr<Constraint>
{
    return make_unique<LinearInequality>(WeightedSum{_coeff_vars}, _value);
}

auto LinearInequality::install(Propagators & propagators, State & initial_state) && -> void
{
    optional<ProofLine> proof_line;
    if (propagators.want_definitions()) {
        WeightedPseudoBooleanSum terms;
        for (auto & [c, v] : _coeff_vars.terms)
            terms += c * v;
        proof_line = propagators.define(initial_state, terms <= _value, nullopt);
    }

    auto [sanitised_cv, modifier] = tidy_up_linear(_coeff_vars);

    if (visit([](const auto & s) { return s.terms.empty(); }, sanitised_cv) && modifier > _value) {
        propagators.install([](State & state) -> pair<Inference, PropagatorState> {
            return pair{state.infer(FalseLiteral{}, JustifyUsingRUP{}), PropagatorState::Enable};
        },
            Triggers{}, "empty linear equality");
    }

    Triggers triggers;
    for (auto & [_, v] : _coeff_vars.terms)
        triggers.on_bounds.push_back(v);

    overloaded{
        [&, &modifier = modifier](const SumOf<Weighted<SimpleIntegerVariableID>> & lin) {
            propagators.install([modifier = modifier, lin = lin, value = _value, proof_line = proof_line](State & state) {
                return propagate_linear(lin, value + modifier, state, false, proof_line);
            },
                triggers, "linear inequality");
        },
        [&, &modifier = modifier](const SumOf<PositiveOrNegative<SimpleIntegerVariableID>> & sum) {
            propagators.install([modifier = modifier, sum = sum, value = _value, proof_line = proof_line](State & state) {
                return propagate_sum(sum, value + modifier, state, false, proof_line);
            },
                triggers, "linear inequality");
        },
        [&, &modifier = modifier](const SumOf<SimpleIntegerVariableID> & sum) {
            propagators.install([modifier = modifier, sum = sum, value = _value, proof_line = proof_line](State & state) mutable {
                return propagate_sum_all_positive(sum, value + modifier, state, false, proof_line);
            },
                triggers, "linear inequality");
        }}
        .visit(sanitised_cv);
}

auto LinearInequality::describe_for_proof() -> std::string
{
    return "linear inequality";
}

LinearLessEqual::LinearLessEqual(WeightedSum coeff_vars, Integer value) :
    LinearInequality(move(coeff_vars), value)
{
}

namespace
{
    auto negate(WeightedSum & coeff_vars) -> WeightedSum &
    {
        for (auto & [c, _] : coeff_vars.terms)
            c = -c;
        return coeff_vars;
    }
}

LinearGreaterThanEqual::LinearGreaterThanEqual(WeightedSum coeff_vars, Integer value) :
    LinearInequality(move(negate(coeff_vars)), -value)
{
}
