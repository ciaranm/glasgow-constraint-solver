/* vim: set sw=4 sts=4 et foldmethod=syntax : */

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

using std::optional;
using std::pair;
using std::string;
using std::stringstream;
using std::to_string;
using std::tuple;
using std::unique_ptr;
using std::vector;

Count::Count(const std::vector<IntegerVariableID> & vars, const IntegerVariableID & value_of_interest, const IntegerVariableID & how_many) :
    _vars(vars),
    _value_of_interest(value_of_interest),
    _how_many(how_many)
{
}

auto Count::clone() const -> unique_ptr<Constraint>
{
    return make_unique<Count>(_vars, _value_of_interest, _how_many);
}

auto Count::install(Propagators & propagators, const State & initial_state) && -> void
{
    Triggers triggers;
    triggers.on_change.insert(triggers.on_change.end(), _vars.begin(), _vars.end());
    triggers.on_change.emplace_back(_value_of_interest);
    triggers.on_bounds.emplace_back(_how_many);

    vector<tuple<ProofFlag, ProofFlag, ProofFlag>> flags;
    optional<ProofLine> forward_sum_line, reverse_sum_line;
    if (propagators.want_definitions()) {
        for (auto & var : _vars) {
            auto flag = propagators.create_proof_flag("count");
            auto countb = propagators.create_proof_flag("countb");
            auto counts = propagators.create_proof_flag("counts");
            flags.emplace_back(flag, countb, counts);

            // countb -> (var < voi)
            auto cv1 = Linear{{1_i, var}, {-1_i, _value_of_interest}};
            propagators.define_linear_le(initial_state, cv1, -1_i, countb);

            // ! countb -> (var >= voi)
            auto cv1r = Linear{{1_i, _value_of_interest}, {-1_i, var}};
            propagators.define_linear_le(initial_state, cv1r, 0_i, ! countb);

            // counts -> (voi < var)
            auto cv2 = Linear{{-1_i, var}, {1_i, _value_of_interest}};
            propagators.define_linear_le(initial_state, cv2, -1_i, counts);

            // ! counts -> (voi >= var)
            auto cv2r = Linear{{-1_i, _value_of_interest}, {1_i, var}};
            propagators.define_linear_le(initial_state, cv2r, 0_i, ! counts);

            // ! countb /\ ! counts -> flag
            WeightedPseudoBooleanTerms forward{{1_i, countb}, {1_i, counts}, {1_i, flag}};
            // ! flag \/ (! countb /\ ! counts)
            WeightedPseudoBooleanTerms reverse{{2_i, ! flag}, {1_i, ! countb}, {1_i, ! counts}};
            Integer forward_g = 1_i, reverse_g = 2_i;
            if (sanitise_pseudoboolean_terms(forward, forward_g))
                propagators.define_pseudoboolean_ge(initial_state, move(forward), forward_g);
            if (sanitise_pseudoboolean_terms(reverse, reverse_g))
                propagators.define_pseudoboolean_ge(initial_state, move(reverse), reverse_g);
        }

        // sum flag == how_many
        WeightedPseudoBooleanTerms forward, reverse;
        for (auto & [flag, _1, _2] : flags) {
            forward.emplace_back(1_i, flag);
            reverse.emplace_back(-1_i, flag);
        }
        forward.emplace_back(-1_i, _how_many);
        reverse.emplace_back(1_i, _how_many);
        Integer forward_g = 0_i, reverse_g = 0_i;

        if (sanitise_pseudoboolean_terms(forward, forward_g))
            forward_sum_line = propagators.define_pseudoboolean_ge(initial_state, move(forward), forward_g);
        if (sanitise_pseudoboolean_terms(reverse, reverse_g))
            reverse_sum_line = propagators.define_pseudoboolean_ge(initial_state, move(reverse), reverse_g);
    }

    propagators.install(
        initial_state,
        [vars = _vars, value_of_interest = _value_of_interest, how_many = _how_many, flags = flags, forward_sum_line = forward_sum_line,
            reverse_sum_line = reverse_sum_line](State & state) -> pair<Inference, PropagatorState> {
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
                proof.need_proof_variable(how_many < how_many_is_less_than);
                proof.emit_proof_comment("need to show that " + proof.proof_variable(how_many < how_many_is_less_than) + " due to at least " + to_string(how_many_definitely_do_not) + " out of " + to_string(vars.size()) + " misses");
                for (const auto & [idx, var] : enumerate(vars)) {
                    bool seen_any = false;
                    state.for_each_value_while_immutable(var, [&](const Integer & val) -> bool {
                        if (state.in_domain(value_of_interest, val))
                            seen_any = true;
                        return ! seen_any;
                    });

                    if (! seen_any) {
                        stringstream line;
                        line << "u" << proof.trail_variables(state, 1_i);
                        line << " 1 " << proof.proof_variable(! get<0>(flags[idx])) << " >= 1 ;";
                        to_delete.push_back(proof.emit_proof_line(line.str()));
                    }
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
