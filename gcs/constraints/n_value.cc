#include <gcs/constraints/n_value.hh>
#include <gcs/innards/proofs/proof_logger.hh>
#include <gcs/innards/proofs/proof_model.hh>
#include <gcs/innards/propagators.hh>
#include <gcs/innards/state.hh>

#include <list>
#include <map>
#include <set>

using namespace gcs;
using namespace gcs::innards;

using std::list;
using std::map;
using std::max;
using std::optional;
using std::pair;
using std::set;
using std::unique_ptr;
using std::vector;

NValue::NValue(const IntegerVariableID & n, std::vector<IntegerVariableID> vars) :
    _n_values(n),
    _vars(move(vars))
{
}

auto NValue::clone() const -> unique_ptr<Constraint>
{
    return make_unique<NValue>(_n_values, _vars);
}

auto NValue::install(Propagators & propagators, State & initial_state, ProofModel * const optional_model) && -> void
{
    Triggers triggers;
    triggers.on_bounds.emplace_back(_n_values);
    triggers.on_change.insert(triggers.on_change.end(), _vars.begin(), _vars.end());

    propagators.install([n_values = _n_values, vars = _vars](State & state, ProofLogger * const logger) -> pair<Inference, PropagatorState> {
        set<Integer> all_possible_values;
        for (const auto & var : vars) {
            state.for_each_value_while_immutable(var, [&](Integer v) -> bool {
                all_possible_values.insert(v);
                return true;
            });
        }

        auto inf = state.infer(logger, n_values < Integer(all_possible_values.size()) + 1_i, JustifyUsingRUP{});
        if (Inference::Contradiction == inf)
            return pair{inf, PropagatorState::Enable};

        set<Integer> all_definite_values;
        for (const auto & var : vars) {
            auto val = state.optional_single_value(var);
            if (val)
                all_definite_values.insert(*val);
        }

        increase_inference_to(inf, state.infer(logger, n_values >= max(1_i, Integer(all_definite_values.size())), JustifyUsingRUP{}));
        if (Inference::Contradiction == inf)
            return pair{inf, PropagatorState::Enable};

        return pair{inf, PropagatorState::Enable};
    },
        triggers, "nvalue");

    if (optional_model) {
        map<Integer, list<IntegerVariableID>> all_possible_values;
        for (const auto & var : _vars) {
            initial_state.for_each_value_while_immutable(var, [&](Integer v) -> bool {
                all_possible_values.emplace(v, list<IntegerVariableID>{}).first->second.push_back(var);
                return true;
            });
        }

        list<ProofFlag> flags;
        for (auto [v, vars] : all_possible_values) {
            auto flag = optional_model->create_proof_flag("nvalue");
            WeightedPseudoBooleanSum forward;
            for (auto & var : vars)
                forward += 1_i * (var == v);
            forward += 1_i * ! flag;
            optional_model->add_constraint(forward >= 1_i);

            WeightedPseudoBooleanSum reverse;
            for (auto & var : vars)
                reverse += 1_i * (var != v);
            reverse += Integer(vars.size()) * flag;
            optional_model->add_constraint(reverse >= Integer(vars.size()));

            flags.push_back(flag);
        }

        WeightedPseudoBooleanSum forward, reverse;
        for (auto & flag : flags) {
            forward += 1_i * flag;
            reverse += -1_i * flag;
        }
        forward += -1_i * _n_values;
        reverse += 1_i * _n_values;
        optional_model->add_constraint(forward >= 0_i);
        optional_model->add_constraint(reverse >= 0_i);
    }
}

auto NValue::describe_for_proof() -> std::string
{
    return "nvalue";
}
