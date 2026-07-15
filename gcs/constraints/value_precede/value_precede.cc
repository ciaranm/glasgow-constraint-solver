#include <gcs/constraints/value_precede/hints.hh>
#include <gcs/constraints/value_precede/value_precede.hh>
#include <gcs/innards/inference_tracker.hh>
#include <gcs/innards/proofs/names_and_ids_tracker.hh>
#include <gcs/innards/proofs/proof_logger.hh>
#include <gcs/innards/proofs/proof_model.hh>
#include <gcs/innards/propagators.hh>
#include <gcs/innards/reason.hh>
#include <gcs/innards/s_expr.hh>
#include <gcs/innards/state.hh>

#include <map>
#include <memory>
#include <optional>
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

ValuePrecede::ValuePrecede(vector<Integer> chain, vector<IntegerVariableID> vars) : _chain(move(chain)), _vars(move(vars))
{
}

ValuePrecede::ValuePrecede(Integer s, Integer t, vector<IntegerVariableID> vars) : _chain({s, t}), _vars(move(vars))
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
    if (n == 0)
        return;

    // OPB encoding, matching cake_pb_cp's value_precede / seq_precede encoder
    // (cp_to_ilp_lexicographicalScript.sml): one proof-only first-occurrence
    // index pos[v] per distinct chain value v, with the sentinel value n meaning
    // "v does not appear in vars". pos[v] is a proof-only integer variable whose
    // bits are named as cake's value-keyed flags, so the names line up:
    //   - bit b of pos[v] is the free flag v[id][v_b][pos];
    //   - [pos[v] >= k] is the reified flag v[id][v_k][pge] (k = 1..n).
    // pos[v] is pinned to the leftmost occurrence of v (or n if absent) via the
    // upper-bound and existence constraints; the precede constraints order first
    // occurrences along the chain. The bit-sum is implicitly bounded below by 0
    // (the bits are Boolean); an explicit pos[v] <= n bound row caps it above
    // (see there).

    map<Integer, ProofOnlySimpleIntegerVariableID> pos; // value -> pos[v]
    map<Integer, vector<ProofFlag>> pge;                // value -> [ [pos>=1], [pos>=2], ..., [pos>=n] ]

    for (const auto & v : _chain) {
        if (pos.contains(v))
            continue;

        // pos[v] in [0, n] (sentinel n = "v absent"): a proof-only integer variable
        // whose bits are named as cake's value flags v[id][v_b][pos] -- a free bit-sum
        // with no OPB bound lines, its ge atoms introduced lazily in the proof on use.
        auto pos_v = model.create_proof_only_integer_variable(0_i, Integer{static_cast<long long>(n)}, "value_precede_pos_" + v.to_string(),
            IntegerVariableProofRepresentation::Bits, CakeBitNaming{_constraint_id, {v.raw_value}, "pos", std::nullopt});
        pos.emplace(v, pos_v);

        // pos[v] <= n. Without this, an absent value v -- forced to pos[v] >= n by
        // the existence pins -- leaves the high bits free whenever the bit-width
        // over-represents [0, n] (n not 2^w - 1), so the proof-only pos[v] is not
        // pinned by unit propagation at a solution (it must be: see
        // proof_only_aux_must_be_determined). cake_pb_cp emits this bound row
        // unconditionally (labelled @c[id][ubn_<v>], upstream f43d14aa8), so the
        // solver matches it on both sides for every n: it is what lets the chain
        // verify at any width, not just the exact-width (n = 2^w - 1) sizes where
        // the bits alone already cap pos[v]. At those exact widths the row is
        // logically redundant but keeps the two OPBs in step.
        model.add_labelled_constraint(_constraint_id, "ubn_" + v.to_string(), WPBSum{} + 1_i * pos_v <= Integer{static_cast<long long>(n)});

        // [pos[v] >= k] <=> pos[v] >= k, for k = 1..n.
        vector<ProofFlag> ges;
        for (size_t k = 1; k <= n; ++k)
            ges.push_back(model.create_proof_flag_values_fully_reifying(_constraint_id, vector<long long>{v.raw_value, static_cast<long long>(k)},
                "pge", WPBSum{} + 1_i * pos_v >= Integer{static_cast<long long>(k)}));
        pge.emplace(v, move(ges));

        // Upper bound: (vars[i] = v) -> pos[v] <= i.
        for (size_t i = 0; i < n; ++i)
            model.add_labelled_constraint(_constraint_id, std::to_string(i) + "ub", WPBSum{} + 1_i * pos_v <= Integer{static_cast<long long>(i)},
                HalfReifyOnConjunctionOf{{_vars[i] == v}});

        // Existence: [pos[v] >= i+1] OR (exists k <= i. vars[k] = v).
        for (size_t i = 0; i < n; ++i) {
            WPBSum existence;
            existence += 1_i * pge.at(v)[i]; // [pos[v] >= i+1]
            for (size_t k = 0; k <= i; ++k)
                existence += 1_i * (_vars[k] == v);
            model.add_labelled_constraint(_constraint_id, std::to_string(i) + "ex", move(existence) >= 1_i);
        }
    }

    for (size_t j = 1; j < _chain.size(); ++j) {
        Integer s = _chain[j - 1];
        Integer t = _chain[j];
        auto pi = std::to_string(j - 1);
        if (s == t) {
            // pos[s] >= n: s must be absent from vars.
            model.add_labelled_constraint(_constraint_id, pi + "nos", WPBSum{} + 1_i * pos.at(s) >= Integer{static_cast<long long>(n)});
        }
        else {
            // ~[pos[t] >= n] -> pos[t] - pos[s] >= 1.
            model.add_labelled_constraint(
                _constraint_id, pi + "pr", WPBSum{} + 1_i * pos.at(t) + -1_i * pos.at(s) >= 1_i, HalfReifyOnConjunctionOf{{! pge.at(t)[n - 1]}});
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
            constraint_id(),
            // The reason ranges over the fixed variable scope, so build it once
            // at install (capture-init) and reuse it rather than rebuilding it
            // every wake. See dev_docs/propagator-performance.md.
            [vars = _vars, s, t, reason = generic_reason(_vars), owner = constraint_id()](
                const State & state, auto & inference, ProofLogger * const logger) -> PropagatorState {
                auto n = vars.size();

                size_t alpha = n;
                for (size_t i = 0; i < n; ++i) {
                    if (state.in_domain(vars[i], s)) {
                        alpha = i;
                        break;
                    }
                }

                // Prune t from positions [0, min(alpha+1, n)). If alpha == n
                // this is all positions; otherwise it's positions 0..alpha
                // inclusive.
                auto prune_up_to = (alpha == n) ? n : alpha + 1;
                for (size_t i = 0; i < prune_up_to; ++i) {
                    if (state.in_domain(vars[i], t))
                        inference.infer(logger, vars[i] != t, JustifyUsingRUP{hints::ValuePrecede{owner}}, reason);
                }

                if (alpha == n)
                    return PropagatorState::DisableUntilBacktrack;

                // If the alpha position is fixed to s, this pair is fully
                // discharged regardless of later positions.
                if (state.has_single_value(vars[alpha]) && state.bounds(vars[alpha]).first == s)
                    return PropagatorState::DisableUntilBacktrack;

                return PropagatorState::Enable;
            },
            triggers);
    }
}

auto ValuePrecede::constraint_type() const -> std::string
{
    return "value_precede";
}

auto ValuePrecede::s_expr(const ProofModel * const model) const -> SExpr
{
    auto & tracker = model->names_and_ids_tracker();
    std::vector<SExpr> chain;
    for (const auto & val : _chain)
        chain.push_back(SExpr::atom(val.to_string()));
    std::vector<SExpr> vars;
    for (const auto & var : _vars)
        vars.push_back(tracker.s_expr_term_of(var));
    return SExpr::list(
        {SExpr::atom(as_string(_constraint_id)), SExpr::atom(constraint_type()), SExpr::list(std::move(chain)), SExpr::list(std::move(vars))});
}
