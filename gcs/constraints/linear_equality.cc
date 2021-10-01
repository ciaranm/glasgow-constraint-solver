/* vim: set sw=4 sts=4 et foldmethod=syntax : */

#include <gcs/constraints/linear_equality.hh>
#include <gcs/low_level_constraint_store.hh>
#include <gcs/linear.hh>
#include <gcs/extensional.hh>

#include <util/for_each.hh>

#include <functional>
#include <sstream>
#include <vector>

using namespace gcs;

using std::function;
using std::move;
using std::optional;
using std::stringstream;
using std::vector;

LinearEquality::LinearEquality(Linear && coeff_vars, Integer value, bool gac) :
    _coeff_vars(move(coeff_vars)),
    _value(value),
    _gac(gac)
{
}

auto LinearEquality::convert_to_low_level(LowLevelConstraintStore & constraints, const State & initial_state) && -> void
{
    sanitise_linear(_coeff_vars);

    // Use input as < constraint, create >= constraint to get equality
    Linear inv_coeff_vars;
    inv_coeff_vars.reserve(_coeff_vars.size());
    for (auto & [ c, v ] : _coeff_vars)
        inv_coeff_vars.emplace_back(-c, v);

    if (_gac) {
        vector<VariableID> trigger_vars;
        for (auto & [ _, v ] : _coeff_vars)
            trigger_vars.push_back(v);

        optional<ExtensionalData> data;
        constraints.propagator(initial_state, [data = move(data), coeff_vars = _coeff_vars, value = _value] (State & state) mutable -> Inference {
                if (! data) {
                    vector<vector<Integer> > permitted;
                    vector<Integer> current;
                    function<void ()> search = [&] () {
                        if (current.size() == coeff_vars.size()) {
                            Integer actual_value{ 0_i };
                            for_each_with_index(coeff_vars, [&] (auto & cv, auto idx) {
                                    auto [ c, _ ] = cv;
                                    actual_value += c * current[idx];
                                    });
                            if (actual_value == value)
                                permitted.push_back(current);
                        }
                        else {
                            auto & [ _, var ] = coeff_vars[current.size()];
                            state.for_each_value(var, [&] (Integer val) {
                                    current.push_back(val);
                                    search();
                                    current.pop_back();
                                    });
                        }
                    };
                    search();

                    auto sel = state.create_pseudovariable(0_i, Integer(permitted.size() - 1), "lineq");
                    vector<IntegerVariableID> vars;
                    for (auto & [ _, v ] : coeff_vars)
                        vars.push_back(v);

                    state.add_proof_steps(JustifyExplicitly{ [&] (Proof & proof) {
                            for_each_with_index(permitted, [&] (const vector<Integer> & vals, auto idx) {
                                    stringstream line;
                                    line << "red " << coeff_vars.size() << " ~" << proof.proof_variable(sel == Integer(idx));
                                    for_each_with_index(vals, [&] (const Integer & val, auto val_idx) {
                                            line << " 1 " << proof.proof_variable(coeff_vars[val_idx].second == Integer(val));
                                            });
                                    line << " >= " << coeff_vars.size() << " ; " << proof.proof_variable(sel == Integer(idx)) << " 0";
                                    proof.emit_proof_line(line.str());

                                    line = stringstream{ };
                                    line << "red 1 " << proof.proof_variable(sel == Integer(idx));
                                    for_each_with_index(vals, [&] (const Integer & val, auto val_idx) {
                                            line << " 1 ~" << proof.proof_variable(coeff_vars[val_idx].second == Integer(val));
                                            });
                                    line << " >= 1 ; " << proof.proof_variable(sel == Integer(idx)) << " 1";
                                    proof.emit_proof_line(line.str());
                                    });

                            stringstream trail;
                            for_each_with_index(permitted, [&] (const vector<Integer> &, auto idx) {
                                    trail << " 1 " << proof.proof_variable(sel == Integer(idx));
                                    });

                            vector<Integer> current;
                            function<void ()> search = [&] () {
                                if (current.size() != coeff_vars.size()) {
                                    auto & [ _, var ] = coeff_vars[current.size()];
                                    state.for_each_value(var, [&] (Integer val) {
                                            current.push_back(val);
                                            search();
                                            current.pop_back();
                                            });
                                }
                                stringstream line;
                                line << "u" << trail.str();
                                for_each_with_index(current, [&] (Integer val, auto val_idx) {
                                        line << " 1 ~" << proof.proof_variable(coeff_vars[val_idx].second == val);
                                        });
                                line << " >= 1 ;";
                                proof.emit_proof_line(line.str());
                            };
                            search();

                            } });

                    data = ExtensionalData{ sel, move(vars), move(permitted) };
                }

                return propagate_extensional(*data, state);
                }, trigger_vars, "lin_eq_gac");
    }

    constraints.integer_linear_le(initial_state, move(inv_coeff_vars), -_value);
    constraints.integer_linear_le(initial_state, move(_coeff_vars), _value);
}

auto LinearEquality::describe_for_proof() -> std::string
{
    return "linear equality";
}

