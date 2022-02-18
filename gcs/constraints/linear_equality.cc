/* vim: set sw=4 sts=4 et foldmethod=syntax : */

#include <gcs/constraints/linear_equality.hh>
#include <gcs/detail/extensional.hh>
#include <gcs/detail/linear_utils.hh>
#include <gcs/detail/proof.hh>
#include <gcs/detail/propagators.hh>
#include <gcs/exception.hh>

#include <util/for_each.hh>
#include <util/overloaded.hh>

#include <functional>
#include <sstream>
#include <vector>

using namespace gcs;

using std::function;
using std::move;
using std::nullopt;
using std::optional;
using std::pair;
using std::stringstream;
using std::vector;

LinearEquality::LinearEquality(Linear && coeff_vars, Integer value, bool gac) :
    _coeff_vars(move(coeff_vars)),
    _value(value),
    _gac(gac)
{
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

    auto get_var(const pair<bool, SimpleIntegerVariableID> & cv) -> SimpleIntegerVariableID
    {
        return cv.second;
    }

    auto get_var(const pair<Integer, SimpleIntegerVariableID> & cv) -> SimpleIntegerVariableID
    {
        return cv.second;
    }

    auto get_var(const SimpleIntegerVariableID & cv) -> SimpleIntegerVariableID
    {
        return cv;
    }

    auto get_coeff(const pair<bool, SimpleIntegerVariableID> & cv) -> bool
    {
        return cv.first;
    }

    auto get_coeff(const pair<Integer, SimpleIntegerVariableID> & cv) -> Integer
    {
        return cv.first;
    }

    auto get_coeff(const SimpleIntegerVariableID &) -> Integer
    {
        return 1_i;
    }
}

auto LinearEquality::install(Propagators & propagators, const State & initial_state) && -> void
{
    auto [sanitised_cv, modifier] = sanitise_linear(_coeff_vars);

    optional<ProofLine> proof_line;
    if (propagators.want_definitions())
        proof_line = propagators.define_linear_eq(initial_state, _coeff_vars, _value + modifier, nullopt);

    Triggers triggers;
    for (auto & [_, v] : _coeff_vars)
        triggers.on_bounds.push_back(v);

    overloaded{
        [&, &modifier = modifier](const SimpleLinear & lin) {
            propagators.install(
                initial_state, [modifier = modifier, lin = lin, value = _value, proof_line = proof_line](State & state) {
                    return propagate_linear(lin, value + modifier, state, true, proof_line);
                },
                triggers, "linear equality");
        },
        [&, &modifier = modifier](const SimpleSum & sum) {
            propagators.install(
                initial_state, [modifier = modifier, sum = sum, value = _value, proof_line = proof_line](State & state) {
                    return propagate_sum(sum, value + modifier, state, true, proof_line);
                },
                triggers, "linear equality");
        },
        [&, &modifier = modifier](const SimpleIntegerVariableIDs & sum) {
            propagators.install(
                initial_state, [modifier = modifier, sum = sum, value = _value, proof_line = proof_line](State & state) {
                    return propagate_sum_all_positive(sum, value + modifier, state, true, proof_line);
                },
                triggers, "linear equality");
        }}
        .visit(sanitised_cv);

    if (_gac) {
        visit([&](auto & sanitised_cv) {
            Triggers triggers;
            for (auto & cv : sanitised_cv)
                triggers.on_change.push_back(get_var(cv));

            optional<ExtensionalData> data;
            propagators.install(
                initial_state, [data = move(data), coeff_vars = sanitised_cv, value = _value](State & state) mutable -> pair<Inference, PropagatorState> {
                    if (! data) {
                        vector<vector<Integer>> permitted;
                        vector<Integer> current;
                        function<void()> search = [&]() {
                            if (current.size() == coeff_vars.size()) {
                                Integer actual_value{0_i};
                                for_each_with_index(coeff_vars, [&](auto & cv, auto idx) {
                                    auto coeff = get_coeff(cv);
                                    actual_value += to_coeff(coeff) * current[idx];
                                });
                                if (actual_value == value)
                                    permitted.push_back(current);
                            }
                            else {
                                const auto & var = get_var(coeff_vars[current.size()]);
                                state.for_each_value(var, [&](Integer val) {
                                    current.push_back(val);
                                    search();
                                    current.pop_back();
                                });
                            }
                        };
                        search();

                        auto sel = state.create_pseudovariable(0_i, Integer(permitted.size() - 1), "lineq");
                        vector<IntegerVariableID> vars;
                        for (auto & cv : coeff_vars)
                            vars.push_back(get_var(cv));

                        state.add_proof_steps(JustifyExplicitly{[&](Proof & proof, vector<ProofLine> & to_delete) {
                            proof.emit_proof_comment("building GAC table for linear equality");

                            for (auto & var : vars) {
                                state.for_each_value(var, [&](Integer val) {
                                    proof.need_proof_variable(var == val);
                                });
                            }

                            for_each_with_index(permitted, [&](const vector<Integer> & vals, auto idx) {
                                stringstream line;
                                line << "red " << coeff_vars.size() << " ~" << proof.proof_variable(sel == Integer(idx));
                                for_each_with_index(vals, [&](const Integer & val, auto val_idx) {
                                    line << " 1 " << proof.proof_variable(get_var(coeff_vars[val_idx]) == Integer(val));
                                });
                                line << " >= " << coeff_vars.size() << " ; " << proof.proof_variable(sel == Integer(idx)) << " 0";
                                proof.emit_proof_line(line.str());

                                line = stringstream{};
                                line << "red 1 " << proof.proof_variable(sel == Integer(idx));
                                for_each_with_index(vals, [&](const Integer & val, auto val_idx) {
                                    line << " 1 ~" << proof.proof_variable(get_var(coeff_vars[val_idx]) == Integer(val));
                                });
                                line << " >= 1 ; " << proof.proof_variable(sel == Integer(idx)) << " 1";
                                proof.emit_proof_line(line.str());
                            });

                            stringstream line1, line2;
                            line1 << "red 1 ~tmptrail ";
                            line2 << "red " << permitted.size() << " tmptrail ";

                            stringstream trail;
                            for_each_with_index(permitted, [&](const vector<Integer> &, auto idx) {
                                trail << " 1 " << proof.proof_variable(sel == Integer(idx));
                                line1 << " 1 " << proof.proof_variable(sel == Integer(idx));
                                line2 << " 1 " << proof.proof_variable(sel != Integer(idx));
                            });

                            line1 << " >= 1 ; tmptrail 0";
                            line2 << " >= " << permitted.size() << " ; tmptrail 1";
                            to_delete.emplace_back(proof.emit_proof_line(line1.str()));
                            to_delete.emplace_back(proof.emit_proof_line(line2.str()));

                            vector<Integer> current;
                            function<void()> search = [&]() {
                                if (current.size() != coeff_vars.size()) {
                                    const auto & var = get_var(coeff_vars[current.size()]);
                                    state.for_each_value(var, [&](Integer val) {
                                        current.push_back(val);
                                        search();
                                        current.pop_back();
                                    });
                                }
                                stringstream line;
                                line << "u 1 tmptrail";
                                for_each_with_index(current, [&](Integer val, auto val_idx) {
                                    line << " 1 ~" << proof.proof_variable(get_var(coeff_vars[val_idx]) == val);
                                });
                                line << " >= 1 ;";
                                to_delete.emplace_back(proof.emit_proof_line(line.str()));
                            };
                            search();

                            proof.emit_proof_line("u" + trail.str() + " >= 1 ;");
                        }});

                        data = ExtensionalData{sel, move(vars), move(permitted)};
                    }

                    return propagate_extensional(*data, state);
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

LinearLessEqual::LinearLessEqual(Linear && coeff_vars, Integer value) :
    _coeff_vars(move(coeff_vars)),
    _value(value)
{
}

auto LinearLessEqual::install(Propagators & propagators, const State & initial_state) && -> void
{
    auto [sanitised_cv, modifier] = sanitise_linear(_coeff_vars);

    optional<ProofLine> proof_line;
    if (propagators.want_definitions())
        proof_line = propagators.define_linear_le(initial_state, _coeff_vars, _value + modifier, nullopt);

    Triggers triggers;
    for (auto & [_, v] : _coeff_vars)
        triggers.on_bounds.push_back(v);

    overloaded{
        [&, &modifier = modifier](const SimpleLinear & lin) {
            propagators.install(
                initial_state, [modifier = modifier, lin = lin, value = _value, proof_line = proof_line](State & state) {
                    return propagate_linear(lin, value + modifier, state, false, proof_line);
                },
                triggers, "linear inequality");
        },
        [&, &modifier = modifier](const SimpleSum & sum) {
            propagators.install(
                initial_state, [modifier = modifier, sum = sum, value = _value, proof_line = proof_line](State & state) {
                    return propagate_sum(sum, value + modifier, state, false, proof_line);
                },
                triggers, "linear inequality");
        },
        [&, &modifier = modifier](const SimpleIntegerVariableIDs & sum) {
            propagators.install(
                initial_state, [modifier = modifier, sum = sum, value = _value, proof_line = proof_line](State & state) {
                    return propagate_sum_all_positive(sum, value + modifier, state, false, proof_line);
                },
                triggers, "linear inequality");
        }}
        .visit(sanitised_cv);
}

auto LinearLessEqual::describe_for_proof() -> std::string
{
    return "linear less or equal";
}
