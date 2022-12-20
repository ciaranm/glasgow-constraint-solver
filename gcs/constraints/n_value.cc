/* vim: set sw=4 sts=4 et foldmethod=syntax : */

#include <gcs/constraints/n_value.hh>
#include <gcs/innards/propagators.hh>
#include <gcs/innards/state.hh>

#include <list>
#include <map>
#include <set>

using namespace gcs;
using namespace gcs::innards;

using std::list;
using std::map;
using std::pair;
using std::set;
using std::unique_ptr;
using std::vector;

NValue::NValue(const IntegerVariableID & n, const std::vector<IntegerVariableID> & vars) :
    _n_values(n),
    _vars(vars)
{
}

auto NValue::clone() const -> unique_ptr<Constraint>
{
    return make_unique<NValue>(_n_values, _vars);
}

auto NValue::install(Propagators & propagators, State & initial_state) && -> void
{
    Triggers triggers;
    triggers.on_bounds.emplace_back(_n_values);
    triggers.on_change.insert(triggers.on_change.end(), _vars.begin(), _vars.end());

    propagators.install(
        initial_state, [n_values = _n_values, vars = _vars](State & state) -> pair<Inference, PropagatorState> {
            set<Integer> all_possible_values;
            for (const auto & var : vars) {
                state.for_each_value_while_immutable(var, [&](Integer v) -> bool {
                    all_possible_values.insert(v);
                    return true;
                });
            }

            auto inf = state.infer(n_values < Integer(all_possible_values.size()) + 1_i, JustifyUsingRUP{});
            if (Inference::Contradiction == inf)
                return pair{inf, PropagatorState::Enable};

            set<Integer> all_definite_values;
            for (const auto & var : vars) {
                auto val = state.optional_single_value(var);
                if (val)
                    all_definite_values.insert(*val);
            }

            increase_inference_to(inf, state.infer(n_values >= Integer(all_definite_values.size()), JustifyUsingRUP{}));
            if (Inference::Contradiction == inf)
                return pair{inf, PropagatorState::Enable};

            return pair{inf, PropagatorState::Enable};
        },
        triggers, "nvalue");

    if (propagators.want_definitions()) {
        map<Integer, list<IntegerVariableID>> all_possible_values;
        for (const auto & var : _vars) {
            initial_state.for_each_value_while_immutable(var, [&](Integer v) -> bool {
                all_possible_values.emplace(v, list<IntegerVariableID>{}).first->second.push_back(var);
                return true;
            });
        }

        list<ProofFlag> flags;
        for (auto [v, vars] : all_possible_values) {
            auto flag = propagators.create_proof_flag("nvalue");
            WeightedPseudoBooleanTerms forward;
            for (auto & var : vars)
                forward.emplace_back(1_i, var == v);
            forward.emplace_back(1_i, ! flag);
            Integer forward_g = 1_i;
            if (sanitise_pseudoboolean_terms(forward, forward_g))
                propagators.define_pseudoboolean_ge(initial_state, move(forward), forward_g);

            WeightedPseudoBooleanTerms reverse;
            for (auto & var : vars)
                reverse.emplace_back(1_i, var != v);
            reverse.emplace_back(vars.size(), flag);
            Integer reverse_g(vars.size());
            if (sanitise_pseudoboolean_terms(reverse, reverse_g))
                propagators.define_pseudoboolean_ge(initial_state, move(reverse), reverse_g);

            flags.push_back(flag);
        }

        WeightedPseudoBooleanTerms forward, reverse;
        for (auto & flag : flags) {
            forward.emplace_back(1_i, flag);
            reverse.emplace_back(-1_i, flag);
        }
        forward.emplace_back(-1_i, _n_values);
        reverse.emplace_back(1_i, _n_values);
        Integer forward_g = 0_i, reverse_g = 0_i;
        if (sanitise_pseudoboolean_terms(forward, forward_g))
            propagators.define_pseudoboolean_ge(initial_state, move(forward), forward_g);
        if (sanitise_pseudoboolean_terms(reverse, reverse_g))
            propagators.define_pseudoboolean_ge(initial_state, move(reverse), reverse_g);
    }
}

auto NValue::describe_for_proof() -> std::string
{
    return "nvalue";
}
