#include <gcs/constraints/count.hh>
#include <gcs/innards/propagators.hh>
#include <gcs/innards/state.hh>

#include <util/enumerate.hh>

#include <optional>
#include <sstream>
#include <string>
#include <tuple>

using namespace gcs;
using namespace gcs::innards;

using std::pair;
using std::string;
using std::stringstream;
using std::tuple;
using std::unique_ptr;
using std::vector;

Count::Count(std::vector<IntegerVariableID> vars, const IntegerVariableID & value_of_interest, const IntegerVariableID & how_many) :
    _vars(move(vars)),
    _value_of_interest(value_of_interest),
    _how_many(how_many)
{
}

auto Count::clone() const -> unique_ptr<Constraint>
{
    return make_unique<Count>(_vars, _value_of_interest, _how_many);
}

auto Count::install(Propagators & propagators, State & initial_state) && -> void
{
    Triggers triggers;
    triggers.on_change.insert(triggers.on_change.end(), _vars.begin(), _vars.end());
    triggers.on_change.emplace_back(_value_of_interest);
    triggers.on_bounds.emplace_back(_how_many);

    vector<tuple<ProofFlag, ProofFlag, ProofFlag>> flags;
    if (propagators.want_definitions()) {
        for (auto & var : _vars) {
            auto flag = propagators.create_proof_flag("count");
            auto countb = propagators.create_proof_flag("countb");
            auto counts = propagators.create_proof_flag("counts");
            flags.emplace_back(flag, countb, counts);

            // countb -> (var < voi)
            propagators.define(initial_state, WeightedPseudoBooleanSum{} + (1_i * var) + (-1_i * _value_of_interest) <= -1_i,
                HalfReifyOnConjunctionOf{{countb}});

            // ! countb -> (var >= voi)
            propagators.define(initial_state, WeightedPseudoBooleanSum{} + (1_i * var) >= (1_i * _value_of_interest),
                HalfReifyOnConjunctionOf{{! countb}});

            // counts -> (voi < var)
            propagators.define(initial_state, WeightedPseudoBooleanSum{} + (-1_i * var) + (1_i * _value_of_interest) <= -1_i,
                HalfReifyOnConjunctionOf{{counts}});

            // ! counts -> (voi >= var)
            propagators.define(initial_state, WeightedPseudoBooleanSum{} + (-1_i * _value_of_interest) + (1_i * var) <= 0_i,
                HalfReifyOnConjunctionOf{{! counts}});

            // ! countb /\ ! counts -> flag
            propagators.define(initial_state, WeightedPseudoBooleanSum{} + 1_i * countb + 1_i * counts + 1_i * flag >= 1_i);

            // ! flag \/ (! countb /\ ! counts)
            propagators.define(initial_state, WeightedPseudoBooleanSum{} + 2_i * ! flag + 1_i * ! countb + 1_i * ! counts >= 2_i);
        }

        // sum flag == how_many
        WeightedPseudoBooleanSum forward, reverse;
        for (auto & [flag, _1, _2] : flags) {
            forward += 1_i * flag;
            reverse += -1_i * flag;
        }
        forward += -1_i * _how_many;
        reverse += 1_i * _how_many;
        Integer forward_g = 0_i, reverse_g = 0_i;

        propagators.define(initial_state, forward >= forward_g);
        propagators.define(initial_state, reverse >= reverse_g);
    }

    propagators.install(
        [vars = _vars, value_of_interest = _value_of_interest, how_many = _how_many, flags = flags](
            State & state) -> pair<Inference, PropagatorState> {
            int how_many_definitely_do_not = 0;
            for (auto & var : vars) {
                bool seen_any = false;
                state.for_each_value_while_immutable(value_of_interest, [&](const Integer & voi) {
                    if (state.in_domain(var, voi))
                        seen_any = true;
                    return ! seen_any;
                });

                if (! seen_any)
                    ++how_many_definitely_do_not;
            }

            auto how_many_is_less_than = Integer(vars.size() - how_many_definitely_do_not) + 1_i;
            auto inf = state.infer(how_many < how_many_is_less_than, JustifyExplicitly{[&](Proof & proof, vector<ProofLine> & to_delete) -> void {
                for (const auto & [idx, var] : enumerate(vars)) {
                    bool seen_any = false;
                    state.for_each_value_while_immutable(var, [&](const Integer & val) -> bool {
                        if (state.in_domain(value_of_interest, val))
                            seen_any = true;
                        return ! seen_any;
                    });

                    if (! seen_any)
                        to_delete.push_back(proof.emit_rup_proof_line_under_trail(state,
                            WeightedPseudoBooleanSum{} + 1_i * (! get<0>(flags[idx])) >= 1_i));
                }
            }});

            if (Inference::Contradiction == inf)
                return pair{inf, PropagatorState::Enable};

            int how_many_must = 0;
            auto voi = state.optional_single_value(value_of_interest);
            if (voi) {
                for (auto & v : vars)
                    if (state.optional_single_value(v) == voi)
                        ++how_many_must;
            }
            increase_inference_to(inf, state.infer(how_many >= Integer(how_many_must), JustifyUsingRUP{}));

            return pair{inf, PropagatorState::Enable};
        },
        triggers, "count");
}

auto Count::describe_for_proof() -> std::string
{
    return "count";
}
