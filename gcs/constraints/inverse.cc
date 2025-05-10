#include <gcs/constraints/all_different/gac_all_different.hh>
#include <gcs/constraints/inverse.hh>
#include <gcs/exception.hh>
#include <gcs/innards/inference_tracker.hh>
#include <gcs/innards/proofs/names_and_ids_tracker.hh>
#include <gcs/innards/proofs/proof_logger.hh>
#include <gcs/innards/proofs/proof_model.hh>
#include <gcs/innards/proofs/recover_am1.hh>
#include <gcs/innards/propagators.hh>
#include <gcs/innards/state.hh>
#include <gcs/integer.hh>

#include <util/enumerate.hh>

#include <algorithm>
#include <optional>
#include <ranges>
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
                optional_model->add_constraint("Inverse", "x_i = j -> y[j] = i", WeightedPseudoBooleanSum{} + 1_i * (x_i != Integer(j) + _y_start) + 1_i * (y_j == Integer(i) + _x_start) >= 1_i);
                // y[j] = i -> x[i] = j
                optional_model->add_constraint("Inverse", "y_j = i -> x[i] = j", WeightedPseudoBooleanSum{} + 1_i * (y_j != Integer(i) + _x_start) + 1_i * (x_i == Integer(j) + _y_start) >= 1_i);
            }
    }

    Triggers triggers;
    triggers.on_change.insert(triggers.on_change.end(), _x.begin(), _x.end());
    triggers.on_change.insert(triggers.on_change.end(), _y.begin(), _y.end());

    shared_ptr<map<Integer, ProofLine>> x_value_am1s;
    if (optional_model) {
        auto build_am1s = [](const vector<IntegerVariableID> & x, Integer x_start, const State &,
                              auto &, ProofLogger * const logger, const auto & map) {
            for (Integer v = x_start; v < x_start + Integer(x.size()); ++v) {
                // make an am1 for x[i] = v
                vector<IntegerVariableCondition> xieqvs;
                for (const auto & var : x)
                    xieqvs.push_back(var != v);
                map->emplace(v, recover_am1<IntegerVariableCondition>(*logger, ProofLevel::Top, xieqvs, [&](const IntegerVariableCondition & c1, const IntegerVariableCondition & c2) -> ProofLine {
                    return logger->emit(RUPProofRule{}, WeightedPseudoBooleanSum{} + 1_i * c1 + 1_i * c2 >= 1_i, ProofLevel::Temporary);
                }));
            }
        };

        x_value_am1s = make_shared<map<Integer, ProofLine>>();
        propagators.install_initialiser([x = _x, x_start = _x_start, x_value_am1s = x_value_am1s, build_am1s = build_am1s](
                                            const State & state, auto & inference, ProofLogger * const logger) -> void {
            build_am1s(x, x_start, state, inference, logger, x_value_am1s);
        });
    }

    vector<Integer> x_values;
    for (const auto & [i, _] : enumerate(_x))
        x_values.push_back(Integer(i) + _x_start);

    propagators.install([x = _x, y = _y, x_start = _x_start, y_start = _y_start,
                            x_values = move(x_values), x_value_am1s = x_value_am1s](
                            const State & state, auto & inf, ProofLogger * const logger) -> PropagatorState {
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

        propagate_gac_all_different(x, x_values, *x_value_am1s.get(), state, inf, logger);

        return PropagatorState::Enable;
    },
        triggers, "inverse");
}
