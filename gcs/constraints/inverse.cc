#include <gcs/constraints/all_different/gac_all_different.hh>
#include <gcs/constraints/inverse.hh>
#include <gcs/exception.hh>
#include <gcs/innards/inference_tracker.hh>
#include <gcs/innards/proofs/proof_logger.hh>
#include <gcs/innards/proofs/proof_model.hh>
#include <gcs/innards/proofs/variable_constraints_tracker.hh>
#include <gcs/innards/propagators.hh>
#include <gcs/innards/state.hh>
#include <gcs/integer.hh>

#include <util/enumerate.hh>

#include <algorithm>
#include <optional>
#include <set>
#include <sstream>
#include <utility>
#include <vector>

using namespace gcs;
using namespace gcs::innards;

using std::make_shared;
using std::map;
using std::max;
using std::min;
using std::optional;
using std::pair;
using std::shared_ptr;
using std::stringstream;
using std::unique_ptr;
using std::vector;
using std::visit;

Inverse::Inverse(vector<IntegerVariableID> x, vector<IntegerVariableID> y, Integer x_start, Integer y_start) :
    _x(move(x)),
    _y(move(y)),
    _x_start(x_start),
    _y_start(y_start)

{
}

auto Inverse::clone() const -> unique_ptr<Constraint>
{
    return make_unique<Inverse>(_x, _y, _x_start, _y_start);
}

auto Inverse::install(Propagators & propagators, State & initial_state, ProofModel * const optional_model) && -> void
{
    if (_x.size() != _y.size()) {
        propagators.model_contradiction(initial_state, optional_model, "Inverse constraint on different sized arrays");
        return;
    }

    for (const auto & [idx, v] : enumerate(_x)) {
        propagators.trim_lower_bound(initial_state, optional_model, v, 0_i + _y_start, "Inverse");
        propagators.trim_upper_bound(initial_state, optional_model, v, Integer(_y.size()) + _y_start - 1_i, "Inverse");
    }

    for (const auto & [idx, v] : enumerate(_y)) {
        propagators.trim_lower_bound(initial_state, optional_model, v, 0_i + _y_start, "Inverse");
        propagators.trim_upper_bound(initial_state, optional_model, v, Integer(_y.size()) + _y_start - 1_i, "Inverse");
    }

    if (optional_model) {
        for (const auto & [i, x_i] : enumerate(_x))
            for (const auto & [j, y_j] : enumerate(_y)) {
                // x[i] = j -> y[j] = i
                optional_model->add_constraint(WeightedPseudoBooleanSum{} +
                        1_i * (x_i != Integer(j) + _y_start) + 1_i * (y_j == Integer(i) + _x_start) >=
                    1_i);
                // y[j] = i -> x[i] = j
                optional_model->add_constraint(WeightedPseudoBooleanSum{} +
                        1_i * (y_j != Integer(i) + _x_start) + 1_i * (x_i == Integer(j) + _y_start) >=
                    1_i);
            }
    }

    Triggers triggers;
    triggers.on_change.insert(triggers.on_change.end(), _x.begin(), _x.end());
    triggers.on_change.insert(triggers.on_change.end(), _y.begin(), _y.end());

    shared_ptr<map<Integer, ProofLine>> x_value_am1s;
    if (optional_model) {
        auto build_am1s = [](const vector<IntegerVariableID> & x, Integer x_start, const State &,
                              InferenceTracker &, ProofLogger * const logger, const auto & map) {
            for (Integer v = x_start; v < x_start + Integer(x.size()); ++v) {
                // make an am1 for x[i] = v
                auto temporary_proof_level = logger->temporary_proof_level();
                stringstream am1;
                for (unsigned i1 = 0; i1 < x.size(); ++i1) {
                    vector<ProofLine> lines;
                    for (unsigned i2 = i1 + 1; i2 < x.size(); ++i2)
                        lines.push_back(logger->emit_rup_proof_line(
                            WeightedPseudoBooleanSum{} + 1_i * (x[i1] != v) + 1_i * (x[i2] != v) >= 1_i,
                            ProofLevel::Temporary));

                    if (i1 == 0)
                        am1 << "p";
                    else
                        am1 << " " << (i1 + 1) << " *";

                    for (const auto & [n, line] : enumerate(lines)) {
                        am1 << " " << line;
                        if (n != 0 || i1 != 0)
                            am1 << " +";
                    }

                    am1 << " " << (i1 + 2) << " d";
                }
                map->emplace(v, logger->emit_proof_line(am1.str(), ProofLevel::Top));
                logger->forget_proof_level(temporary_proof_level);
            }
        };

        x_value_am1s = make_shared<map<Integer, ProofLine>>();
        propagators.install_initialiser([x = _x, x_start = _x_start, x_value_am1s = x_value_am1s, build_am1s = build_am1s](
                                            const State & state, InferenceTracker & inference, ProofLogger * const logger) -> void {
            build_am1s(x, x_start, state, inference, logger, x_value_am1s);
        });
    }

    vector<Integer> x_values;
    for (const auto & [i, _] : enumerate(_x))
        x_values.push_back(Integer(i) + _x_start);

    propagators.install([x = _x, y = _y, x_start = _x_start, y_start = _y_start,
                            x_values = move(x_values), x_value_am1s = x_value_am1s](
                            const State & state, InferenceTracker & inf, ProofLogger * const logger) -> PropagatorState {
        for (const auto & [i, x_i] : enumerate(x)) {
            for (auto x_i_value : state.each_value_mutable(x_i))
                if (! state.in_domain(y.at((x_i_value - y_start).raw_value), Integer(i) + x_start))
                    inf.infer(logger, x_i != x_i_value,
                        JustifyUsingRUP{},
                        [&]() { return Literals{y.at((x_i_value - y_start).raw_value) != Integer(i) + x_start}; });
        }

        for (const auto & [i, y_i] : enumerate(y)) {
            for (auto y_i_value : state.each_value_mutable(y_i))
                if (! state.in_domain(x.at((y_i_value - x_start).raw_value), Integer(i) + y_start))
                    inf.infer(logger, y_i != y_i_value,
                        JustifyUsingRUP{},
                        [&]() { return Literals{x.at((y_i_value - x_start).raw_value) != Integer(i) + y_start}; });
        }

        propagate_gac_all_different(x, x_values, *x_value_am1s, state, inf, logger);

        return PropagatorState::Enable;
    },
        triggers, "inverse");
}

auto Inverse::describe_for_proof() -> std::string
{
    return "inverse";
}
