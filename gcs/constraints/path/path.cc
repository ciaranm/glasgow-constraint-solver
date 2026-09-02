#include <gcs/constraints/linear.hh>
#include <gcs/constraints/path/path.hh>
#include <gcs/constraints/reachable.hh>
#include <gcs/exception.hh>
#include <gcs/innards/proofs/names_and_ids_tracker.hh>
#include <gcs/innards/proofs/proof_model.hh>
#include <gcs/innards/propagators.hh>
#include <gcs/innards/s_expr.hh>
#include <gcs/innards/state.hh>

#include <memory>
#include <string>
#include <utility>
#include <vector>

using namespace gcs;
using namespace gcs::innards;
using namespace gcs::innards::path;

using std::make_unique;
using std::move;
using std::pair;
using std::size_t;
using std::string;
using std::to_string;
using std::unique_ptr;
using std::vector;

PathBase::PathBase(vector<pair<size_t, size_t>> edges, IntegerVariableID start, IntegerVariableID end, vector<IntegerVariableID> ns,
    vector<IntegerVariableID> es, bool directed) : _edges(move(edges)), _start(start), _end(end), _ns(move(ns)), _es(move(es)), _directed(directed)
{
}

auto PathBase::prepare(Propagators & propagators, State & initial_state, ProofModel * const model) -> bool
{
    if (_ns.empty())
        throw InvalidProblemDefinitionException{"Path needs at least one node: both endpoints have to be nodes, and have to be selected"};
    if (_edges.size() != _es.size())
        throw InvalidProblemDefinitionException{"Path needs one edge selection variable per edge"};

    auto n = _ns.size();
    for (const auto & [u, v] : _edges)
        if (u >= n || v >= n)
            throw InvalidProblemDefinitionException{"Path has an edge endpoint that is not a node"};

    for (const auto & vars : {&_ns, &_es})
        for (const auto & v : *vars) {
            auto [lower, upper] = initial_state.bounds(v);
            if (lower < 0_i || upper > 1_i)
                throw InvalidProblemDefinitionException{"Path needs its node and edge variables to be 0 or 1"};
        }

    // The end has to be a node number. Reachable pins the start down for us, by
    // saying exactly one node is the root, but nothing says as much about the end,
    // so a caller who declared it wider than the numbering needs telling here ---
    // as Circuit tells its successors.
    propagators.define_bound(initial_state, model, _end, Bound::Lower, 0_i);
    propagators.define_bound(initial_state, model, _end, Bound::Upper, Integer(static_cast<long long>(n) - 1));

    // Everything selected is reached from the start, which also gives subgraph and
    // "the start is selected". The children carry this constraint's identity, and
    // two of them can because they label different roles; see Tree.
    if (_directed) {
        DReachable reach{_edges, _start, _ns, _es};
        reach.set_constraint_id(constraint_id());
        move(reach).install(propagators, initial_state, model);
    }
    else {
        Reachable reach{_edges, _start, _ns, _es};
        reach.set_constraint_id(constraint_id());
        move(reach).install(propagators, initial_state, model);
    }

    WeightedSum cardinality;
    for (const auto & v : _es)
        cardinality += 1_i * v;
    for (const auto & v : _ns)
        cardinality += (-1_i) * v;
    LinearEquality card{move(cardinality), -1_i};
    card.set_constraint_id(constraint_id());
    move(card).install(propagators, initial_state, model);

    // The end is selected, whichever node it turns out to be. Reachable says as
    // much about the start already.
    for (size_t v = 0; v != n; ++v)
        _rules.push_back(graph_rules::Selected{"endin" + to_string(v), _ns[v], {_end == Integer(static_cast<long long>(v))}});

    if (_directed) {
        vector<vector<IntegerVariableID>> entering(n), leaving(n);
        for (size_t e = 0; e != _edges.size(); ++e) {
            entering[_edges[e].second].push_back(_es[e]);
            leaving[_edges[e].first].push_back(_es[e]);
        }
        for (size_t v = 0; v != n; ++v) {
            auto node = Integer(static_cast<long long>(v));
            // At most one edge in and one out makes the selected subgraph a set of
            // paths and cycles; reachability from the start then makes it one walk.
            if (! entering[v].empty()) {
                _rules.push_back(graph_rules::AtMost{"indeg" + to_string(v), entering[v], 1_i, {}});
                // Nothing enters the start, so the walk begins there.
                _rules.push_back(graph_rules::AtMost{"startin" + to_string(v), entering[v], 0_i, {_start == node}});
            }
            if (! leaving[v].empty()) {
                _rules.push_back(graph_rules::AtMost{"outdeg" + to_string(v), leaving[v], 1_i, {}});
                // Nothing leaves the end, so the walk stops there. With start = end
                // this is also what empties the path: nothing leaves the start
                // either, so nothing else is reachable.
                _rules.push_back(graph_rules::AtMost{"endout" + to_string(v), leaving[v], 0_i, {_end == node}});
            }
        }
    }
    else {
        // Undirected, an edge contributes to the degree of each of its endpoints,
        // so a self loop contributes twice --- which is what makes a self loop
        // unusable in a path, exactly as the doubled edge set would.
        vector<vector<IntegerVariableID>> incident(n);
        for (size_t e = 0; e != _edges.size(); ++e) {
            incident[_edges[e].first].push_back(_es[e]);
            incident[_edges[e].second].push_back(_es[e]);
        }
        for (size_t v = 0; v != n; ++v) {
            if (incident[v].empty())
                continue;
            auto node = Integer(static_cast<long long>(v));
            _rules.push_back(graph_rules::AtMost{"deg" + to_string(v), incident[v], 2_i, {}});
            // The two ends of a path have one edge each. "At most one" is all that
            // needs saying when they differ: an end with no edge at all makes
            // nothing else reachable, and the other end then has to be it.
            _rules.push_back(graph_rules::AtMost{"startdeg" + to_string(v), incident[v], 1_i, {_start == node}});
            _rules.push_back(graph_rules::AtMost{"enddeg" + to_string(v), incident[v], 1_i, {_end == node}});
            // When they are the same node, though, "at most one" is not enough: it
            // would admit that node joined to one more, which is a path of length
            // one and not a path from the node to itself. Nothing incident at all is
            // what makes the subgraph that node alone, through reachability.
            _rules.push_back(graph_rules::AtMost{"loop" + to_string(v), incident[v], 0_i, {_start == node, _end == node}});
        }
    }

    return ! _rules.empty();
}

auto PathBase::define_proof_model(ProofModel & model, const State &) -> void
{
    graph_rules::define(model, _constraint_id, _rules);
}

auto PathBase::install_propagators(Propagators & propagators) -> void
{
    Triggers triggers;
    for (const auto & v : graph_rules::variables_of(_rules))
        triggers.on_change.push_back(v);

    propagators.install(
        constraint_id(),
        [rules = _rules, owner = constraint_id()](const State & state, auto & inference, ProofLogger * const logger) -> PropagatorState {
            graph_rules::propagate(rules, owner, state, inference, logger);
            return PropagatorState::Enable;
        },
        triggers);
}

auto PathBase::base_s_expr(const ProofModel * const model) const -> SExpr
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
        tracker.s_expr_term_of(_start), tracker.s_expr_term_of(_end), SExpr::list(move(ns)), SExpr::list(move(es))});
}

Path::Path(vector<pair<size_t, size_t>> edges, IntegerVariableID start, IntegerVariableID end, vector<IntegerVariableID> ns,
    vector<IntegerVariableID> es) : PathBase(move(edges), start, end, move(ns), move(es), false)
{
}

auto Path::clone() const -> unique_ptr<Constraint>
{
    return make_unique<Path>(_edges, _start, _end, _ns, _es);
}

auto Path::constraint_type() const -> string
{
    return "path";
}

auto Path::s_expr(const ProofModel * const model) const -> SExpr
{
    return base_s_expr(model);
}

DPath::DPath(vector<pair<size_t, size_t>> edges, IntegerVariableID start, IntegerVariableID end, vector<IntegerVariableID> ns,
    vector<IntegerVariableID> es) : PathBase(move(edges), start, end, move(ns), move(es), true)
{
}

auto DPath::clone() const -> unique_ptr<Constraint>
{
    return make_unique<DPath>(_edges, _start, _end, _ns, _es);
}

auto DPath::constraint_type() const -> string
{
    return "dpath";
}

auto DPath::s_expr(const ProofModel * const model) const -> SExpr
{
    return base_s_expr(model);
}
