
#include <algorithm>
#include <cmath>
#include <gcs/constraints/mult_bc.hh>
#include <gcs/innards/proofs/proof_logger.hh>
#include <gcs/innards/proofs/proof_model.hh>
#include <gcs/innards/proofs/variable_constraints_tracker.hh>
#include <gcs/innards/propagators.hh>

using namespace gcs;
using namespace gcs::innards;

using std::make_unique;
using std::max;
using std::min;
using std::nullopt;
using std::pair;
using std::string;
using std::stringstream;
using std::unique_ptr;
using std::vector;

namespace
{ // Find the bounds for [x_min ... x_max] * [y_min ... y_max]
    // (accounting for the fact x and y can have negative bounds)
    auto get_product_bounds(Integer x_min, Integer x_max, Integer y_min, Integer y_max) -> pair<Integer, Integer>
    {
        auto x1y1 = x_min * y_min;
        auto x2y1 = x_max * y_min;
        auto x1y2 = x_min * y_max;
        auto x2y2 = x_max * y_max;

        auto smallest_possible_product = min(
            min(x1y1, x1y2),
            min(x2y1, x2y2));

        auto largest_possible_product = max(
            max(x1y1, x1y2),
            max(x2y1, x2y2));

        return {smallest_possible_product, largest_possible_product};
    }

    // Filter variable q where q * y = x based on bounds of x and y
    auto filter_quotient(IntegerVariableID q_var, Integer x_min, Integer x_max, Integer y_min, Integer y_max, const vector<IntegerVariableID> & all_vars, State & state, ProofLogger * const logger) -> Inference
    {
        // This is based on the case breakdown in JaCoP
        // https://github.com/radsz/jacop/blob/develop/src/main/java/org/jacop/core/IntDomain.java#L1377
        if (x_min <= 0_i && x_max >= 0_i && y_min <= 0_i && y_max >= 0_i) {
            // 0 is in the bounds of both x and y so no filtering possible
            return Inference::NoChange;
        }
        else if (y_min == 0_i && y_max == 0_i) {
            // y == 0 and 0 not in bounds of x => no possible values for q
            // No justification needed?
            return Inference::Contradiction;
        }
        else if (y_min < 0_i && y_max > 0_i && (x_min > 0_i || x_max < 0_i)) {
            // y contains -1, 0, 1 and x has either all positive or all negative values
            auto largest_possible_quotient = max(abs(x_min), abs(x_max));
            auto smallest_possible_quotient = -largest_possible_quotient;
            auto inf = state.infer(logger, q_var < largest_possible_quotient + 1_i, AssertRatherThanJustifying{}, generic_reason(state, all_vars));
            increase_inference_to(inf, state.infer(logger, q_var >= smallest_possible_quotient, AssertRatherThanJustifying{}, generic_reason(state, all_vars)));
            return inf;
        }
        else if (y_min == 0_i && y_max != 0_i && (x_min > 0_i || x_max < 0_i)) {
            // y is either 0 or strictly positive and x has either all positive or all negative values
            return filter_quotient(q_var, x_min, x_max, 1_i, y_max, all_vars, state, logger);
        }
        else if (y_min != 0_i && y_max == 0_i && (x_min > 0_i || x_max < 0_i)) {
            // y is either 0 or strictly negative x has either all positive or all negative values
            return filter_quotient(q_var, x_min, x_max, y_min, -1_i, all_vars, state, logger);
        }
        else if ((y_min > 0_i || y_max < 0_i) && y_min <= y_max) {
            auto x1y1 = (double)x_min.raw_value / (double)y_min.raw_value;
            auto x1y2 = (double)x_min.raw_value / (double)y_max.raw_value;
            auto x2y1 = (double)x_max.raw_value / (double)y_min.raw_value;
            auto x2y2 = (double)x_max.raw_value / (double)y_max.raw_value;

            double smallest_real_quotient = min(min(x1y1, x1y2), min(x2y1, x2y2));
            double largest_real_quotient = max(max(x1y1, x1y2), max(x2y1, x2y2));
            auto smallest_possible_quotient = Integer{(long long)ceil(smallest_real_quotient)};
            auto largest_possible_quotient = Integer{(long long)floor(largest_real_quotient)};
            if (smallest_possible_quotient > largest_possible_quotient) {
                logger->infer(state, true, FalseLiteral{}, AssertRatherThanJustifying{}, generic_reason(state, all_vars));
                return Inference::Contradiction;
            }
            auto inf = state.infer(logger, q_var < largest_possible_quotient + 1_i, AssertRatherThanJustifying{}, generic_reason(state, all_vars));
            increase_inference_to(inf, state.infer(logger, q_var >= smallest_possible_quotient, AssertRatherThanJustifying{}, generic_reason(state, all_vars)));
            return inf;
        }
        else {
            throw UnexpectedException{
                "Bad interval passed to filter_quotient."};
        }
    }

}

MultBC::MultBC(const IntegerVariableID v1, const IntegerVariableID v2, const IntegerVariableID v3) :
    _v1(v1),
    _v2(v2),
    _v3(v3)
{
}

auto MultBC::clone() const -> unique_ptr<Constraint>
{
    return make_unique<MultBC>(_v1, _v2, _v3);
}

auto MultBC::install(Propagators & propagators, State & initial_state, ProofModel * const optional_model) && -> void
{
    Triggers triggers;
    triggers.on_bounds.push_back(_v1);
    triggers.on_bounds.push_back(_v2);
    triggers.on_bounds.push_back(_v3);

    if (optional_model) {
        // PB Encoding
    }

    propagators.install([v1 = _v1, v2 = _v2, v3 = _v3](State & state, ProofLogger * const logger) -> pair<Inference, PropagatorState> {
        vector<IntegerVariableID> all_vars = {v1, v2, v3};
        auto overall_result = Inference::NoChange;
        auto inf = Inference::NoChange;
        do {
            inf = Inference::NoChange;
            auto bounds1 = state.bounds(v1), bounds2 = state.bounds(v2);
            auto [smallest_product, largest_product] = get_product_bounds(bounds1.first, bounds1.second, bounds2.first, bounds2.second);

            increase_inference_to(inf, state.infer(logger, v3 < largest_product + 1_i, AssertRatherThanJustifying{}, generic_reason(state, all_vars)));

            if (Inference::Contradiction == inf)
                return pair{inf, PropagatorState::Enable};

            increase_inference_to(inf, state.infer(logger, v3 >= smallest_product, AssertRatherThanJustifying{}, generic_reason(state, all_vars)));

            if (Inference::Contradiction == inf)
                return pair{inf, PropagatorState::Enable};

            auto bounds3 = state.bounds(v3);
            increase_inference_to(inf, filter_quotient(v1, bounds3.first, bounds3.second, bounds2.first, bounds2.second, all_vars, state, logger));

            if (Inference::Contradiction == inf)
                return pair{inf, PropagatorState::Enable};

            bounds1 = state.bounds(v1);
            increase_inference_to(inf, filter_quotient(v2, bounds3.first, bounds3.second, bounds1.first, bounds1.second, all_vars, state, logger));

            if (Inference::Contradiction == inf)
                return pair{inf, PropagatorState::Enable};

            increase_inference_to(overall_result, inf);
        } while (inf != Inference::NoChange);

        return {overall_result, PropagatorState::Enable};
    },
        triggers, "mult");
}

auto MultBC::describe_for_proof() -> string
{
    return "mult";
}
