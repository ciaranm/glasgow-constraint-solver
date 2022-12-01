/* vim: set sw=4 sts=4 et foldmethod=syntax : */

#include <gcs/constraints/abs.hh>
#include <gcs/innards/propagators.hh>
#include <gcs/innards/state.hh>

#include <algorithm>
#include <optional>
#include <sstream>

using namespace gcs;
using namespace gcs::innards;

using std::max;
using std::optional;
using std::pair;
using std::stringstream;
using std::unique_ptr;
using std::vector;

Abs::Abs(const IntegerVariableID v1, const IntegerVariableID v2) :
    _v1(v1),
    _v2(v2)
{
}

auto Abs::clone() const -> unique_ptr<Constraint>
{
    return make_unique<Abs>(_v1, _v2);
}

auto Abs::install(Propagators & propagators, const State & initial_state) && -> void
{
    // _v2 >= 0
    propagators.trim_lower_bound(initial_state, _v2, 0_i, "Abs");

    // _v1 <= upper_bound(_v2)
    propagators.trim_upper_bound(initial_state, _v1, initial_state.upper_bound(_v2), "Abs");

    // _v1 >= -upper_bound(_v2)
    propagators.trim_lower_bound(initial_state, _v1, -initial_state.upper_bound(_v2), "Abs");

    // _v2 <= max(upper_bound(_v1), -lower_bound(_v1))
    auto v2u = max(initial_state.upper_bound(_v1), -initial_state.lower_bound(_v1));
    propagators.trim_upper_bound(initial_state, _v2, v2u, "Abs");

    optional<ProofFlag> selector;
    if (propagators.want_definitions())
        selector = propagators.create_proof_flag("abs");

    // _v2 = abs(_v1)
    Triggers triggers{.on_change = {_v1, _v2}};
    propagators.install(
        initial_state, [v1 = _v1, v2 = _v2, selector = selector](State & state) -> pair<Inference, PropagatorState> {
            // v2 = abs(v1)
            Inference result = Inference::NoChange;
            state.for_each_value_while(v1, [&](Integer val) {
                if (! state.in_domain(v2, abs(val)))
                    increase_inference_to(result, state.infer_not_equal(v1, val, JustifyUsingRUP{}));
                return result != Inference::Contradiction;
            });

            state.for_each_value_while(v2, [&](Integer val) {
                if (! state.in_domain(v1, val) && ! state.in_domain(v1, -val) && state.in_domain(v2, val))
                    increase_inference_to(result, state.infer_not_equal(v2, val, JustifyExplicitly{[&](Proof & proof, vector<ProofLine> & del) {
                        proof.need_proof_variable(v2 == val);
                        proof.need_proof_variable(v1 == val);
                        proof.need_proof_variable(v1 == -val);

                        stringstream step;

                        step << "u" << proof.trail_variables(state, 1_i) << " 1 " << proof.proof_variable(v1 != val) << " >= 1 ;";
                        del.push_back(proof.emit_proof_line(step.str()));

                        step = stringstream{};
                        step << "u" << proof.trail_variables(state, 1_i) << " 1 " << proof.proof_variable(v1 != -val) << " >= 1 ;";
                        del.push_back(proof.emit_proof_line(step.str()));

                        step = stringstream{};
                        step << "u" << proof.trail_variables(state, 1_i) << " 1 " << proof.proof_variable(*selector)
                             << " 1 " << proof.proof_variable(v2 != val) << " >= 1 ;";
                        del.push_back(proof.emit_proof_line(step.str()));

                        step = stringstream{};
                        step << "u" << proof.trail_variables(state, 1_i) << " 1 " << proof.proof_variable(! *selector)
                             << " 1 " << proof.proof_variable(v2 != val) << " >= 1 ;";
                        del.push_back(proof.emit_proof_line(step.str()));
                    }}));
                return result != Inference::Contradiction;
            });

            return pair{result, PropagatorState::Enable};
        },
        triggers, "abs");

    if (propagators.want_definitions()) {
        auto cv1 = Linear{{1_i, _v2}, {-1_i, _v1}};
        propagators.define_linear_eq(initial_state, cv1, 0_i, *selector);

        auto cv2 = Linear{{1_i, _v1}, {1_i, _v2}};
        propagators.define_linear_eq(initial_state, cv2, 0_i, ! *selector);

        auto cv3 = Linear{{1_i, _v1}};
        propagators.define_linear_le(initial_state, cv3, -1_i, ! *selector);

        auto cv4 = Linear{{-1_i, _v1}};
        propagators.define_linear_le(initial_state, cv4, 0_i, *selector);
    }
}

auto Abs::describe_for_proof() -> std::string
{
    return "abs";
}
