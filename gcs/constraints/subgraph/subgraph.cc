#include <gcs/constraints/subgraph/hints.hh>
#include <gcs/constraints/subgraph/subgraph.hh>
#include <gcs/exception.hh>
#include <gcs/innards/inference_tracker.hh>
#include <gcs/innards/proofs/names_and_ids_tracker.hh>
#include <gcs/innards/proofs/proof_logger.hh>
#include <gcs/innards/proofs/proof_model.hh>
#include <gcs/innards/propagators.hh>
#include <gcs/innards/reason.hh>
#include <gcs/innards/s_expr.hh>
#include <gcs/innards/state.hh>

#include <memory>
#include <string>
#include <utility>
#include <vector>

using namespace gcs;
using namespace gcs::innards;

using std::make_unique;
using std::move;
using std::pair;
using std::size_t;
using std::string;
using std::to_string;
using std::unique_ptr;
using std::vector;

Subgraph::Subgraph(vector<pair<size_t, size_t>> edges, vector<IntegerVariableID> ns, vector<IntegerVariableID> es) :
    _edges(move(edges)), _ns(move(ns)), _es(move(es))
{
}

auto Subgraph::clone() const -> unique_ptr<Constraint>
{
    return make_unique<Subgraph>(_edges, _ns, _es);
}

auto Subgraph::constraint_type() const -> string
{
    return "subgraph";
}

auto Subgraph::s_expr(const ProofModel * const model) const -> SExpr
{
    auto & tracker = model->names_and_ids_tracker();
    vector<SExpr> from, to, ns, es;
    for (const auto & [u, v] : _edges) {
        from.push_back(SExpr::atom(to_string(u)));
        to.push_back(SExpr::atom(to_string(v)));
    }
    for (const auto & v : _ns)
        ns.push_back(tracker.s_expr_term_of(v));
    for (const auto & v : _es)
        es.push_back(tracker.s_expr_term_of(v));
    return SExpr::list({SExpr::atom(as_string(_constraint_id)), SExpr::atom(constraint_type()), SExpr::list(move(from)), SExpr::list(move(to)),
        SExpr::list(move(ns)), SExpr::list(move(es))});
}

auto Subgraph::prepare(Propagators &, State & initial_state, ProofModel * const) -> bool
{
    if (_edges.size() != _es.size())
        throw InvalidProblemDefinitionException{"Subgraph needs one edge selection variable per edge"};

    auto n = _ns.size();
    for (const auto & [u, v] : _edges)
        if (u >= n || v >= n)
            throw InvalidProblemDefinitionException{"Subgraph has an edge endpoint that is not a node"};

    // The rows below read ns and es as Booleans, so both have to be in range
    // before anything is said about them.
    for (const auto & vars : {&_ns, &_es})
        for (const auto & v : *vars) {
            auto [lower, upper] = initial_state.bounds(v);
            if (lower < 0_i || upper > 1_i)
                throw InvalidProblemDefinitionException{"Subgraph needs its node and edge variables to be 0 or 1"};
        }

    // An edge list with no edges says nothing at all.
    return ! _edges.empty();
}

auto Subgraph::define_proof_model(ProofModel & model, const State &) -> void
{
    // One row per endpoint per edge, which is what fzn_subgraph spells as two
    // implications. The role names the edge and which endpoint, because a role
    // has to name everything that varies for its row to be citable.
    for (size_t e = 0; e != _edges.size(); ++e) {
        model.add_labelled_constraint(
            _constraint_id, "sgf" + to_string(e), WPBSum{} + 1_i * (_ns[_edges[e].first] == 1_i) >= 1_i, HalfReifyOnConjunctionOf{{_es[e] == 1_i}});
        model.add_labelled_constraint(
            _constraint_id, "sgt" + to_string(e), WPBSum{} + 1_i * (_ns[_edges[e].second] == 1_i) >= 1_i, HalfReifyOnConjunctionOf{{_es[e] == 1_i}});
    }
}

auto Subgraph::install_propagators(Propagators & propagators) -> void
{
    Triggers triggers;
    for (const auto & v : _ns)
        triggers.on_change.push_back(v);
    for (const auto & v : _es)
        triggers.on_change.push_back(v);

    propagators.install(
        constraint_id(),
        [edges = _edges, ns = _ns, es = _es, owner = constraint_id()](
            const State & state, auto & inference, ProofLogger * const logger) -> PropagatorState {
            auto justify = JustifyUsingRUP{hints::Subgraph{owner}};
            auto fixed_to = [&](IntegerVariableID v, Integer x) {
                auto value = state.optional_single_value(v);
                return value && *value == x;
            };

            // Both directions of the same implication: a selected edge selects its
            // endpoints, and an edge with an unselected endpoint is not selected.
            // Each is RUP against the row for that edge and endpoint.
            for (size_t e = 0; e != edges.size(); ++e) {
                auto [u, w] = edges[e];
                if (fixed_to(es[e], 1_i)) {
                    for (auto & endpoint : {u, w})
                        if (! fixed_to(ns[endpoint], 1_i))
                            inference.infer(logger, ns[endpoint] == 1_i, justify, ExplicitReason{ReasonLiterals{es[e] == 1_i}});
                }
                else if (! fixed_to(es[e], 0_i)) {
                    for (auto & endpoint : {u, w})
                        if (fixed_to(ns[endpoint], 0_i)) {
                            inference.infer(logger, es[e] == 0_i, justify, ExplicitReason{ReasonLiterals{ns[endpoint] == 0_i}});
                            break;
                        }
                }
            }

            return PropagatorState::Enable;
        },
        triggers);
}
