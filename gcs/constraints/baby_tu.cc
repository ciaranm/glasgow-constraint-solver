#include <gcs/constraints/baby_tu.hh>
#include <gcs/innards/inference_tracker.hh>
#include <gcs/innards/proofs/lp_justifier.hh>
#include <gcs/innards/proofs/proof_model.hh>
#include <gcs/innards/propagators.hh>
#include <iostream>

using namespace gcs;
using namespace gcs::innards;

using std::cout;
using std::endl;

using std::make_shared;
using std::shared_ptr;
using std::unique_ptr;

BabyTU::BabyTU(const IntegerVariableID x, const IntegerVariableID y) :
    _x(x),
    _y(y)
{
}

auto BabyTU::clone() const -> unique_ptr<Constraint>
{
    return make_unique<BabyTU>(_x, _y);
}

auto BabyTU::install(Propagators & propagators, State & initial_state,
    ProofModel * const optional_model) && -> void
{
    shared_ptr<LPJustifier> lp_justifier = make_shared<LPJustifier>(LPJustificationOptions{});

    lp_justifier->initialise_with_vars(initial_state, {}, {_x, _y});
    if (optional_model) {
        auto con1 = WeightedPseudoBooleanSum{} + 1_i * _x + -1_i * _y >= 0_i;
        auto line1 = optional_model->add_constraint("Baby TU", "less than", con1);
        lp_justifier->add_pb_constraint(con1, *line1);

        auto con2 = WeightedPseudoBooleanSum{} + 1_i * _y + -1_i * _x >= 0_i;
        auto line2 = optional_model->add_constraint("Baby TU", "less than", con2);
        lp_justifier->add_pb_constraint(con1, *line2);
    }

    Triggers triggers{};
    triggers.on_change = {_x, _y};

    propagators.install(
        [x = _x, y = _y, lp_justifier_ptr = move(lp_justifier)](const State & state, auto & inference, ProofLogger * const logger) -> PropagatorState {
            LPJustifier * lp_justifier = lp_justifier_ptr.get();
            // std::cout << "Triggered" << std::endl;
            auto y_lower = state.lower_bound(y);
            auto justf1 = lp_justifier->compute_justification(state, *logger, WeightedPseudoBooleanSum{} + 1_i * x >= y_lower);
            inference.infer(logger, x >= y_lower, JustifyExplicitlyOnly{justf1}, {});
            auto x_upper = state.upper_bound(x);
            auto justf2 = lp_justifier->compute_justification(state, *logger, WeightedPseudoBooleanSum{} + 1_i * y <= x_upper);
            inference.infer(logger, y < x_upper + 1_i, JustifyExplicitlyOnly{justf2}, {});

            auto y_upper = state.lower_bound(y);
            auto justf3 = lp_justifier->compute_justification(state, *logger, WeightedPseudoBooleanSum{} + 1_i * x <= y_upper);
            inference.infer(logger, x < y_upper + 1_i, JustifyExplicitlyOnly{justf3}, {});

            auto x_lower = state.upper_bound(x);
            auto justf4 = lp_justifier->compute_justification(state, *logger, WeightedPseudoBooleanSum{} + 1_i * y >= x_lower);
            inference.infer(logger, y >= x_lower, JustifyExplicitlyOnly{justf4}, {});
            return PropagatorState::Enable;
        },
        triggers, "baby_tu");
}
