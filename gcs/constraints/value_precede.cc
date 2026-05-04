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
#include <print>
#else
#include <fmt/ostream.h>
#endif

#include <memory>
#include <sstream>
#include <utility>

using namespace gcs;
using namespace gcs::innards;

using std::make_unique;
using std::move;
using std::size_t;
using std::string;
using std::stringstream;
using std::unique_ptr;
using std::vector;

#if defined(__cpp_lib_print) && defined(__cpp_lib_format)
using std::print;
#else
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

auto ValuePrecede::install(Propagators & propagators, State &, ProofModel * const) && -> void
{
    if (_chain.size() < 2)
        return;

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
    for (size_t j = 1; j < _chain.size(); ++j) {
        Integer s = _chain[j - 1];
        Integer t = _chain[j];

        // s == t is *not* a no-op: it requires every occurrence of s to
        // have an earlier occurrence of s, which can only be satisfied if
        // s never appears. The general algorithm below handles this
        // correctly — pruning s from [0, alpha] removes s from x[alpha],
        // shifting alpha forward, and eventually alpha == n.

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
        print(s, " {}", val.raw_value);
    print(s, ") (");
    for (const auto & var : _vars)
        print(s, " {}", model->names_and_ids_tracker().s_expr_name_of(var));
    print(s, ")");

    return s.str();
}
