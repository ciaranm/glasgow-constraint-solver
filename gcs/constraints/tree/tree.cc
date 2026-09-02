#include <gcs/constraints/linear.hh>
#include <gcs/constraints/reachable.hh>
#include <gcs/constraints/tree/tree.hh>
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
using namespace gcs::innards::tree;

using std::make_unique;
using std::move;
using std::pair;
using std::size_t;
using std::string;
using std::to_string;
using std::unique_ptr;
using std::vector;

TreeBase::TreeBase(vector<pair<size_t, size_t>> edges, IntegerVariableID root, vector<IntegerVariableID> ns, vector<IntegerVariableID> es,
    bool directed) : _edges(move(edges)), _root(root), _ns(move(ns)), _es(move(es)), _directed(directed)
{
}

auto TreeBase::prepare(Propagators & propagators, State & initial_state, ProofModel * const model) -> bool
{
    // Validate here rather than leaving it to the reachability child, so that a
    // caller who got a Tree argument wrong is told about Tree.
    if (_ns.empty())
        throw InvalidProblemDefinitionException{"Tree needs at least one node: the root has to be a node, and has to be selected"};
    if (_edges.size() != _es.size())
        throw InvalidProblemDefinitionException{"Tree needs one edge selection variable per edge"};

    auto n = _ns.size();
    for (const auto & [u, v] : _edges)
        if (u >= n || v >= n)
            throw InvalidProblemDefinitionException{"Tree has an edge endpoint that is not a node"};

    for (const auto & vars : {&_ns, &_es})
        for (const auto & v : *vars) {
            auto [lower, upper] = initial_state.bounds(v);
            if (lower < 0_i || upper > 1_i)
                throw InvalidProblemDefinitionException{"Tree needs its node and edge variables to be 0 or 1"};
        }

    // Everything selected is reached from the root, and the root is selected.
    // This is where subgraph comes from too, so nothing here restates it.
    //
    // The children carry this constraint's identity, as SeqPrecedeChain's and
    // Circuit's do (issue #449). Two children can share it because they label
    // different roles --- Reachable's are per node and per edge, the linear
    // equality's are le and ge --- and a third linear child could not, which is
    // why the counting rules below are this constraint's own rows rather than
    // more children.
    if (_directed) {
        DReachable reach{_edges, _root, _ns, _es};
        reach.set_constraint_id(constraint_id());
        move(reach).install(propagators, initial_state, model);
    }
    else {
        Reachable reach{_edges, _root, _ns, _es};
        reach.set_constraint_id(constraint_id());
        move(reach).install(propagators, initial_state, model);
    }

    // One fewer edge than node. Together with connectivity this is what makes it
    // a tree rather than just a connected subgraph.
    WeightedSum cardinality;
    for (const auto & v : _es)
        cardinality += 1_i * v;
    for (const auto & v : _ns)
        cardinality += (-1_i) * v;
    LinearEquality card{move(cardinality), -1_i};
    card.set_constraint_id(constraint_id());
    move(card).install(propagators, initial_state, model);

    // Directed, a node may have at most one selected edge coming in. Undirected,
    // there is nothing to add: the count and connectivity are the whole of it.
    if (_directed) {
        vector<vector<IntegerVariableID>> entering(n);
        for (size_t e = 0; e != _edges.size(); ++e)
            entering[_edges[e].second].push_back(_es[e]);
        for (size_t v = 0; v != n; ++v)
            if (! entering[v].empty())
                _rules.push_back(graph_rules::AtMost{"indeg" + to_string(v), move(entering[v]), 1_i, {}});
    }

    return ! _rules.empty();
}

auto TreeBase::define_proof_model(ProofModel & model, const State &) -> void
{
    graph_rules::define(model, _constraint_id, _rules);
}

auto TreeBase::install_propagators(Propagators & propagators) -> void
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

auto TreeBase::base_s_expr(const ProofModel * const model) const -> SExpr
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
        tracker.s_expr_term_of(_root), SExpr::list(move(ns)), SExpr::list(move(es))});
}

Tree::Tree(vector<pair<size_t, size_t>> edges, IntegerVariableID root, vector<IntegerVariableID> ns, vector<IntegerVariableID> es) :
    TreeBase(move(edges), root, move(ns), move(es), false)
{
}

auto Tree::clone() const -> unique_ptr<Constraint>
{
    return make_unique<Tree>(_edges, _root, _ns, _es);
}

auto Tree::constraint_type() const -> string
{
    return "tree";
}

auto Tree::s_expr(const ProofModel * const model) const -> SExpr
{
    return base_s_expr(model);
}

DTree::DTree(vector<pair<size_t, size_t>> edges, IntegerVariableID root, vector<IntegerVariableID> ns, vector<IntegerVariableID> es) :
    TreeBase(move(edges), root, move(ns), move(es), true)
{
}

auto DTree::clone() const -> unique_ptr<Constraint>
{
    return make_unique<DTree>(_edges, _root, _ns, _es);
}

auto DTree::constraint_type() const -> string
{
    return "dtree";
}

auto DTree::s_expr(const ProofModel * const model) const -> SExpr
{
    return base_s_expr(model);
}
