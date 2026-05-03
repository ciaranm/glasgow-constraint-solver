#include <gcs/constraints/all_different/gac_all_different.hh>
#include <gcs/constraints/innards/recover_am1.hh>
#include <gcs/constraints/inverse.hh>
#include <gcs/exception.hh>
#include <gcs/innards/inference_tracker.hh>
#include <gcs/innards/proofs/names_and_ids_tracker.hh>
#include <gcs/innards/proofs/proof_logger.hh>
#include <gcs/innards/proofs/proof_model.hh>
#include <gcs/innards/propagators.hh>
#include <gcs/innards/state.hh>
#include <gcs/integer.hh>

#include <util/enumerate.hh>

#include <version>

#if defined(__cpp_lib_print) && defined(__cpp_lib_format)
#include <print>
#else
#include <fmt/ostream.h>
#endif

#include <sstream>
#include <string>
#include <utility>
#include <vector>

using namespace gcs;
using namespace gcs::innards;

using std::make_shared;
using std::map;
using std::shared_ptr;
using std::string;
using std::stringstream;
using std::unique_ptr;
using std::vector;

#if defined(__cpp_lib_print) && defined(__cpp_lib_format)
using std::print;
#else
using fmt::print;
#endif

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
    if (! prepare(propagators, initial_state, optional_model))
        return;

    if (optional_model)
        define_proof_model(*optional_model);

    install_propagators(propagators);
}

auto Inverse::prepare(Propagators & propagators, State & initial_state, ProofModel * const optional_model) -> bool
{
    if (_x.size() != _y.size()) {
        propagators.model_contradiction(initial_state, optional_model, "Inverse constraint on different sized arrays");
        return false;
    }

    for (const auto & [idx, v] : enumerate(_x)) {
        propagators.trim_lower_bound(initial_state, optional_model, v, 0_i + _y_start, "Inverse");
        propagators.trim_upper_bound(initial_state, optional_model, v, Integer(_y.size()) + _y_start - 1_i, "Inverse");
    }

    for (const auto & [idx, v] : enumerate(_y)) {
        propagators.trim_lower_bound(initial_state, optional_model, v, 0_i + _x_start, "Inverse");
        propagators.trim_upper_bound(initial_state, optional_model, v, Integer(_x.size()) + _x_start - 1_i, "Inverse");
    }

    return true;
}

auto Inverse::define_proof_model(ProofModel & model) -> void
{
    for (const auto & [i, x_i] : enumerate(_x))
        for (const auto & [j, y_j] : enumerate(_y)) {
            // x[i] = j -> y[j] = i
            model.add_constraint("Inverse", "x_i = j -> y[j] = i", WPBSum{} + 1_i * (x_i != Integer(j) + _y_start) + 1_i * (y_j == Integer(i) + _x_start) >= 1_i);
            // y[j] = i -> x[i] = j
            model.add_constraint("Inverse", "y_j = i -> x[i] = j", WPBSum{} + 1_i * (y_j != Integer(i) + _x_start) + 1_i * (x_i == Integer(j) + _y_start) >= 1_i);
        }

    // Set up the AM1 map only when proof logging is on; the propagator captures it
    // by value, so it must always be non-null but stays empty when define_proof_model
    // wasn't called.
    _x_value_am1s = make_shared<map<Integer, ProofLine>>();
}

auto Inverse::install_propagators(Propagators & propagators) -> void
{
    Triggers triggers;
    triggers.on_change.insert(triggers.on_change.end(), _x.begin(), _x.end());
    triggers.on_change.insert(triggers.on_change.end(), _y.begin(), _y.end());

    if (_x_value_am1s) {
        auto build_am1s = [](const vector<IntegerVariableID> & x, Integer x_start, const State &,
                              auto &, ProofLogger * const logger, const auto & map) {
            for (Integer v = x_start; v < x_start + Integer(x.size()); ++v) {
                // make an am1 for x[i] = v
                vector<IntegerVariableCondition> xieqvs;
                for (const auto & var : x)
                    xieqvs.push_back(var != v);
                map->emplace(v, recover_am1<IntegerVariableCondition>(*logger, ProofLevel::Top, xieqvs, [&](const IntegerVariableCondition & c1, const IntegerVariableCondition & c2) -> ProofLine {
                    return logger->emit(RUPProofRule{}, WPBSum{} + 1_i * c1 + 1_i * c2 >= 1_i, ProofLevel::Temporary);
                }));
            }
        };

        propagators.install_initialiser([x = _x, x_start = _x_start, x_value_am1s = _x_value_am1s, build_am1s = build_am1s](
                                            const State & state, auto & inference, ProofLogger * const logger) -> void {
            build_am1s(x, x_start, state, inference, logger, x_value_am1s);
        });
    }
    else {
        // No proof model: propagator still captures this map (must be non-null), but it stays empty.
        _x_value_am1s = make_shared<map<Integer, ProofLine>>();
    }

    vector<Integer> x_values;
    for (const auto & [i, _] : enumerate(_x))
        x_values.push_back(Integer(i) + _x_start);

    propagators.install([x = _x, y = _y, x_start = _x_start, y_start = _y_start,
                            x_values = move(x_values), x_value_am1s = _x_value_am1s](
                            const State & state, auto & inf, ProofLogger * const logger) -> PropagatorState {
        for (const auto & [i, x_i] : enumerate(x)) {
            for (auto x_i_value : state.each_value_mutable(x_i))
                if (! state.in_domain(y.at((x_i_value - y_start).raw_value), Integer(i) + x_start))
                    inf.infer(logger, x_i != x_i_value,
                        JustifyUsingRUP{},
                        [&]() { return Reason{y.at((x_i_value - y_start).raw_value) != Integer(i) + x_start}; });
        }

        for (const auto & [i, y_i] : enumerate(y)) {
            for (auto y_i_value : state.each_value_mutable(y_i))
                if (! state.in_domain(x.at((y_i_value - x_start).raw_value), Integer(i) + y_start))
                    inf.infer(logger, y_i != y_i_value,
                        JustifyUsingRUP{},
                        [&]() { return Reason{x.at((y_i_value - x_start).raw_value) != Integer(i) + y_start}; });
        }

        propagate_gac_all_different(x, x_values, *x_value_am1s.get(), state, inf, logger);

        return PropagatorState::Enable;
    },
        triggers, "inverse");
}

auto Inverse::s_exprify(const std::string & name, const innards::ProofModel * const model) const -> std::string
{
    stringstream s;

    print(s, "{} inverse\n          (", name);
    for (const auto & x : _x) {
        print(s, " {}", model->names_and_ids_tracker().s_expr_name_of(x));
    }
    print(s, ")\n          (");
    for (const auto & y : _y) {
        print(s, " {}", model->names_and_ids_tracker().s_expr_name_of(y));
    }
    print(s, ")\n          {} {})", _x_start, _y_start);

    return s.str();
}
