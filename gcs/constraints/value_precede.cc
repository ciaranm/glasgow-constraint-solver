#include <gcs/constraints/value_precede.hh>
#include <gcs/innards/inference_tracker.hh>
#include <gcs/innards/proofs/names_and_ids_tracker.hh>
#include <gcs/innards/proofs/proof_logger.hh>
#include <gcs/innards/proofs/proof_model.hh>
#include <gcs/innards/propagators.hh>
#include <gcs/innards/reason.hh>
#include <gcs/innards/state.hh>

#include <version>

#if defined(__cpp_lib_print) && defined(__cpp_lib_format)
#include <format>
#include <print>
#else
#include <fmt/core.h>
#include <fmt/ostream.h>
#endif

#include <map>
#include <memory>
#include <sstream>
#include <utility>

using namespace gcs;
using namespace gcs::innards;

using std::make_unique;
using std::map;
using std::move;
using std::size_t;
using std::string;
using std::stringstream;
using std::unique_ptr;
using std::vector;

#if defined(__cpp_lib_print) && defined(__cpp_lib_format)
using std::format;
using std::print;
#else
using fmt::format;
using fmt::print;
#endif

ValuePrecede::ValuePrecede(vector<Integer> chain, vector<IntegerVariableID> vars) :
    _chain(move(chain)),
    _vars(move(vars))
{
}

ValuePrecede::ValuePrecede(Integer s, Integer t, vector<IntegerVariableID> vars) :
    _chain({s, t}),
    _vars(move(vars))
{
}

auto ValuePrecede::clone() const -> unique_ptr<Constraint>
{
    return make_unique<ValuePrecede>(_chain, _vars);
}

auto ValuePrecede::install(Propagators & propagators, State & initial_state, ProofModel * const optional_model) && -> void
{
    if (! prepare(propagators, initial_state, optional_model))
        return;

    if (optional_model)
        define_proof_model(*optional_model);

    install_propagators(propagators);
}

auto ValuePrecede::prepare(Propagators &, State &, ProofModel * const) -> bool
{
    return _chain.size() >= 2;
}

auto ValuePrecede::define_proof_model(ProofModel & model) -> void
{
    auto n = _vars.size();

    // OPB encoding: introduce one ProofOnlyIntegerVariableID pos[v] per
    // distinct chain value v, with domain [0, n] and the value n acting as
    // the sentinel "v does not appear in vars". The encoding pins pos[v] to
    // the leftmost occurrence of v in vars (or n if absent) via:
    //   - upper bound: (vars[i] = v) → pos[v] ≤ i
    //   - existence:   (pos[v] ≤ i) → ∃ k ≤ i, vars[k] = v
    //
    // The precede constraint per consecutive pair (s, t) is then:
    //   - if s != t: (pos[t] ≤ n-1) → pos[t] - pos[s] ≥ 1, i.e., when t
    //     appears, s's leftmost is strictly earlier.
    //   - if s == t: pos[s] ≥ n, i.e., s never appears (since the first s
    //     would have no preceding s). Special-cased to avoid emitting a
    //     degenerate 0 ≥ 1 constraint.
    map<Integer, ProofOnlySimpleIntegerVariableID> pos_vars;
    for (const auto & v : _chain) {
        if (! pos_vars.contains(v)) {
            auto pv = model.create_proof_only_integer_variable(
                0_i, Integer{static_cast<long long>(n)},
                format("value_precede_pos_{}", v),
                IntegerVariableProofRepresentation::Bits);
            pos_vars.emplace(v, pv);
        }
    }

    for (const auto & [v, pv] : pos_vars) {
        for (size_t i = 0; i < n; ++i) {
            // Upper bound: (vars[i] = v) → pos[v] ≤ i.
            model.add_constraint(
                "ValuePrecede", "upper bound",
                WPBSum{} + 1_i * pv <= Integer{static_cast<long long>(i)},
                HalfReifyOnConjunctionOf{{_vars[i] == v}});

            // Existence: (pos[v] ≤ i) → ∃ k ≤ i, vars[k] = v.
            // PB form: (pos[v] > i) + Σ_{k ≤ i} (vars[k] = v) ≥ 1.
            WPBSum existence;
            existence += 1_i * (pv >= Integer{static_cast<long long>(i) + 1});
            for (size_t k = 0; k <= i; ++k)
                existence += 1_i * (_vars[k] == v);
            model.add_constraint(
                "ValuePrecede", "existence",
                move(existence) >= 1_i);
        }
    }

    for (size_t j = 1; j < _chain.size(); ++j) {
        Integer s = _chain[j - 1];
        Integer t = _chain[j];
        if (s == t) {
            // pos[s] ≥ n: s must be absent from vars.
            model.add_constraint(
                "ValuePrecede", "no s",
                WPBSum{} + 1_i * pos_vars.at(s) >= Integer{static_cast<long long>(n)});
        }
        else {
            // (pos[t] ≤ n-1) → pos[t] - pos[s] ≥ 1.
            model.add_constraint(
                "ValuePrecede", "precede",
                WPBSum{} + 1_i * pos_vars.at(t) + (-1_i) * pos_vars.at(s) >= 1_i,
                HalfReifyOnConjunctionOf{{pos_vars.at(t) < Integer{static_cast<long long>(n)}}});
        }
    }
}

auto ValuePrecede::install_propagators(Propagators & propagators) -> void
{
    // Decompose into one propagator per consecutive chain pair. Each pair
    // (s, t) enforces value_precede(s, t, vars): if any element of vars is
    // t, then a strictly earlier element must be s.
    //
    // Algorithm: find alpha = leftmost index where s could still appear,
    // or n if s is impossible anywhere. Then x[i] = t is forbidden whenever
    // no earlier x[j] could be s — that's i in [0, alpha], inclusive at
    // alpha (since "earlier" means j < alpha, and no j < alpha can be s by
    // definition of alpha). When alpha == n there is no later position
    // either, so t is forbidden everywhere.
    //
    // The s == t case is handled by the same algorithm: pruning s from
    // [0, alpha] removes s from x[alpha], shifting alpha forward, and
    // eventually alpha == n. Each individual prune is RUP-derivable from
    // the encoding's `pos[s] ≥ n` constraint plus the upper bound.
    for (size_t j = 1; j < _chain.size(); ++j) {
        Integer s = _chain[j - 1];
        Integer t = _chain[j];

        Triggers triggers;
        for (const auto & v : _vars)
            triggers.on_change.push_back(v);

        propagators.install(
            [vars = _vars, s, t](
                const State & state, auto & inference, ProofLogger * const logger) -> PropagatorState {
                auto n = vars.size();

                size_t alpha = n;
                for (size_t i = 0; i < n; ++i) {
                    if (state.in_domain(vars[i], s)) {
                        alpha = i;
                        break;
                    }
                }

                auto reason = generic_reason(state, vars);

                // Prune t from positions [0, min(alpha+1, n)). If alpha == n
                // this is all positions; otherwise it's positions 0..alpha
                // inclusive.
                auto prune_up_to = (alpha == n) ? n : alpha + 1;
                for (size_t i = 0; i < prune_up_to; ++i) {
                    if (state.in_domain(vars[i], t))
                        inference.infer(logger, vars[i] != t, JustifyUsingRUP{}, reason);
                }

                if (alpha == n)
                    return PropagatorState::DisableUntilBacktrack;

                // If the alpha position is fixed to s, this pair is fully
                // discharged regardless of later positions.
                if (state.has_single_value(vars[alpha]) && state.bounds(vars[alpha]).first == s)
                    return PropagatorState::DisableUntilBacktrack;

                return PropagatorState::Enable;
            },
            triggers, "value_precede");
    }
}

auto ValuePrecede::s_exprify(const string & name, const ProofModel * const model) const -> string
{
    stringstream s;

    print(s, "{} value_precede (", name);
    for (const auto & val : _chain)
        print(s, " {}", val);
    print(s, ") (");
    for (const auto & var : _vars)
        print(s, " {}", model->names_and_ids_tracker().s_expr_name_of(var));
    print(s, ")");

    return s.str();
}
