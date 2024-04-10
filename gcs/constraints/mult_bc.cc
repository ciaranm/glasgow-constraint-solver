
#include <algorithm>
#include <cmath>
#include <gcs/constraints/mult_bc.hh>
#include <gcs/innards/proofs/proof_logger.hh>
#include <gcs/innards/proofs/proof_model.hh>
#include <gcs/innards/proofs/variable_constraints_tracker.hh>
#include <gcs/innards/propagators.hh>

using namespace gcs;
using namespace gcs::innards;

using std::make_pair;
using std::make_unique;
using std::max;
using std::min;
using std::nullopt;
using std::pair;
using std::string;
using std::stringstream;
using std::to_string;
using std::unique_ptr;
using std::vector;

namespace
{
    struct ProofFlagData
    {
        ProofFlag flag;
        ProofLine forwards_reif;
        ProofLine reverse_reif;
    };

    auto prove_product_lower_bounds(ProofLogger & logger, State & state, SimpleIntegerVariableID x, SimpleIntegerVariableID y, SimpleIntegerVariableID z)
    {
        logger.emit_proof_comment("Lower bounds on product:");
    }
    // Find the bounds for [x_min ... x_max] * [y_min ... y_max]
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
    auto filter_quotient(SimpleIntegerVariableID q_var, Integer x_min, Integer x_max, Integer y_min, Integer y_max, const vector<IntegerVariableID> & all_vars, State & state, ProofLogger * const logger) -> Inference
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
                state.infer(logger, FalseLiteral{}, AssertRatherThanJustifying{}, generic_reason(state, all_vars));
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

MultBC::MultBC(const SimpleIntegerVariableID v1, const SimpleIntegerVariableID v2, const SimpleIntegerVariableID v3) :
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
    triggers.on_bounds.emplace_back(_v1);
    triggers.on_bounds.emplace_back(_v2);
    triggers.on_bounds.emplace_back(_v3);

    vector<vector<ProofFlagData>> bit_products{};
    if (optional_model) {
        // PB Encoding
        auto make_magnitude_term = [&](SimpleIntegerVariableID v, const string & name) -> pair<SimpleOrProofOnlyIntegerVariableID, ProofFlag> {
            auto sign_bit = optional_model->create_proof_flag(name + "sign");
            optional_model->add_constraint(WeightedPseudoBooleanSum{} + 1_i * v >= 0_i, HalfReifyOnConjunctionOf{! sign_bit});
            optional_model->add_constraint(WeightedPseudoBooleanSum{} + -1_i * v >= 1_i, HalfReifyOnConjunctionOf{sign_bit});
            if (initial_state.lower_bound(v) < 0_i) {
                auto largest_magnitude = max({abs(initial_state.lower_bound(v)), initial_state.upper_bound(v)});
                auto v_magnitude = optional_model->create_proof_only_integer_variable(0_i, largest_magnitude, name + "'", IntegerVariableProofRepresentation::Bits);

                auto bit_sum_without_neg = WeightedPseudoBooleanSum{};
                auto num_bits = optional_model->variable_constraints_tracker().num_bits(v);
                // Skip the neg bit
                for (unsigned int pos = 0; pos < num_bits - 1; pos++)
                    bit_sum_without_neg += Integer{1 << pos} * ProofBitVariable{v, pos + 1};
                optional_model->add_constraint(bit_sum_without_neg + (-1_i * v_magnitude) == 0_i, HalfReifyOnConjunctionOf{! sign_bit});
                optional_model->add_constraint(bit_sum_without_neg + (1_i * v_magnitude) == Integer{1 << (num_bits - 1)}, HalfReifyOnConjunctionOf{sign_bit});
                return make_pair(v_magnitude, sign_bit);
            }
            else {
                return make_pair(v, sign_bit);
            }
        };
        auto [v1_mag, v1_sign] = make_magnitude_term(_v1, "x");
        auto [v2_mag, v2_sign] = make_magnitude_term(_v2, "y");
        auto [v3_mag, v3_sign] = make_magnitude_term(_v3, "z");

        auto v1_num_bits = optional_model->variable_constraints_tracker().num_bits(v1_mag);
        auto v2_num_bits = optional_model->variable_constraints_tracker().num_bits(v2_mag);

        auto bit_product_sum = WeightedPseudoBooleanSum{};
        for (unsigned int i = 0; i < v1_num_bits; i++) {
            bit_products.emplace_back();
            for (unsigned int j = 0; j < v2_num_bits; j++) {
                auto flag = optional_model->create_proof_flag("xy[" + to_string(i) + "," + to_string(j) + "]");

                auto forwards = optional_model->add_constraint(
                    WeightedPseudoBooleanSum{} + 1_i * ProofBitVariable{v1_mag, i} + 1_i * ProofBitVariable{v2_mag, j} >= 2_i, HalfReifyOnConjunctionOf{flag});

                auto backwards = optional_model->add_constraint(
                    WeightedPseudoBooleanSum{} + -1_i * ProofBitVariable{v1_mag, i} + -1_i * ProofBitVariable{v2_mag, j} >= -1_i, HalfReifyOnConjunctionOf{! flag});

                bit_products[i].emplace_back(ProofFlagData{flag, *forwards, *backwards});
                bit_product_sum += Integer{1 << (i + j)} * flag;
            }
        }

        // Seems like there ought to be a better way to do this...
        overloaded{
            [&](SimpleIntegerVariableID v3) {
                optional_model->add_constraint(bit_product_sum + (-1_i * v3) == 0_i);
            },
            [&](ProofOnlySimpleIntegerVariableID v3) {
                optional_model->add_constraint(bit_product_sum + (-1_i * v3) == 0_i);
            }}
            .visit(v3_mag);
        auto xyss = optional_model->create_proof_flag("xy[s,s]");
        optional_model->add_constraint(WeightedPseudoBooleanSum{} + 1_i * ! xyss >= 1_i, HalfReifyOnConjunctionOf{v1_sign, v2_sign});
        optional_model->add_constraint(WeightedPseudoBooleanSum{} + 1_i * xyss >= 1_i, HalfReifyOnConjunctionOf{! v1_sign, v2_sign});
        optional_model->add_constraint(WeightedPseudoBooleanSum{} + 1_i * xyss >= 1_i, HalfReifyOnConjunctionOf{v1_sign, ! v2_sign});
        optional_model->add_constraint(WeightedPseudoBooleanSum{} + 1_i * ! xyss >= 1_i, HalfReifyOnConjunctionOf{! v1_sign, ! v2_sign});

        optional_model->add_constraint(WeightedPseudoBooleanSum{} + 1_i * xyss + 1_i * (_v1 != 0_i) + 1_i * (_v2 != 0_i) >= 3_i, HalfReifyOnConjunctionOf{v3_sign});
        optional_model->add_constraint(WeightedPseudoBooleanSum{} + 1_i * ! xyss + 1_i * (_v1 == 0_i) + 1_i * (_v2 == 0_i) >= 1_i, HalfReifyOnConjunctionOf{! v3_sign});
    }

    propagators.install([v1 = _v1, v2 = _v2, v3 = _v3](State & state, ProofLogger * const logger) -> pair<Inference, PropagatorState> {
        vector<IntegerVariableID> all_vars = {v1, v2, v3};
        auto overall_result = Inference::NoChange;
        auto inf = Inference::NoChange;
        do {
            inf = Inference::NoChange;
            auto bounds1 = state.bounds(v1), bounds2 = state.bounds(v2);
            auto [smallest_product, largest_product] = get_product_bounds(bounds1.first, bounds1.second, bounds2.first, bounds2.second);

            auto justf = [&, largest_product = largest_product](const Reason & reason) {
                prove_product_lower_bounds(*logger, state, v1, v2, v3);
                logger->emit_rup_proof_line_under_reason(state, reason, WeightedPseudoBooleanSum{} + 1_i * (v3 < largest_product + 1_i) >= 1_i, ProofLevel::Current);
            };

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
