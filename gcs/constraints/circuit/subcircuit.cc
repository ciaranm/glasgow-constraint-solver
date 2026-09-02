#include <gcs/constraints/all_different.hh>
#include <gcs/constraints/all_different/encoding.hh>
#include <gcs/constraints/all_different/vc_all_different.hh>
#include <gcs/constraints/circuit/hints.hh>
#include <gcs/constraints/circuit/subcircuit.hh>
#include <gcs/exception.hh>
#include <gcs/innards/inference_tracker.hh>
#include <gcs/innards/proofs/names_and_ids_tracker.hh>
#include <gcs/innards/proofs/pol_builder.hh>
#include <gcs/innards/proofs/proof_model.hh>
#include <gcs/innards/propagators.hh>
#include <gcs/innards/s_expr.hh>

#include <util/enumerate.hh>
#include <util/overloaded.hh>

#include <algorithm>
#include <any>
#include <map>
#include <memory>
#include <optional>
#include <string>
#include <utility>
#include <variant>
#include <vector>
#include <version>

#if defined(__cpp_lib_print) && defined(__cpp_lib_format)
#include <format>
#else
#include <fmt/core.h>
#endif

using namespace gcs;
using namespace gcs::innards;
using namespace gcs::innards::subcircuit;

using gcs::subcircuit::Check;
using gcs::subcircuit::Prevent;

#if defined(__cpp_lib_print) && defined(__cpp_lib_format)
using std::format;
#else
using fmt::format;
#endif

using std::make_optional;
using std::make_unique;
using std::map;
using std::nullopt;
using std::optional;
using std::size_t;
using std::string;
using std::to_string;
using std::unique_ptr;
using std::vector;

namespace
{
    // The membership sum: how many nodes are on the tour. A node off the tour points at
    // itself, so this is just a count of the "not a self loop" literals, which means the
    // tour's length is a linear expression over literals the solver already has and needs
    // no auxiliary variable of its own. That is what keeps the wrap-around row linear.
    auto tour_size_sum(const vector<IntegerVariableID> & succ) -> WPBSum
    {
        WPBSum sum;
        for (const auto & [idx, s] : enumerate(succ))
            sum += 1_i * (s != Integer(static_cast<long long>(idx)));
        return sum;
    }

    // One walk of the graph of fixed successor edges, splitting it into the closed cycles
    // and the open chains. Self loops are their own one-node cycles: a node pointing at
    // itself is off the tour, so it neither closes anything nor blocks anything.
    struct FixedEdges
    {
        // Each cycle, in order, as visited. Length one means a self loop.
        vector<vector<long>> cycles;
        // Each maximal open chain, in order: chain.front() has no fixed predecessor and
        // chain.back()'s successor is not yet fixed.
        vector<vector<long>> chains;
    };

    auto walk_fixed_edges(const vector<IntegerVariableID> & succ, const State & state) -> FixedEdges
    {
        auto n = static_cast<long>(succ.size());
        auto fixed = vector<optional<long>>(n, nullopt);
        auto has_fixed_pred = vector<bool>(n, false);
        for (long i = 0; i < n; ++i)
            if (auto v = state.optional_single_value(succ[i])) {
                fixed[i] = v->raw_value;
                has_fixed_pred[v->raw_value] = true;
            }

        FixedEdges result;
        auto seen = vector<bool>(n, false);

        // Open chains first: they start at a fixed edge whose tail nothing points at.
        for (long i = 0; i < n; ++i) {
            if (! fixed[i] || has_fixed_pred[i] || seen[i])
                continue;
            vector<long> chain{i};
            seen[i] = true;
            auto j = *fixed[i];
            while (true) {
                // A node is only ever reached once from a chain start, because a node with
                // a fixed predecessor is not a chain start -- unless two successors are
                // fixed to the same value, which the all-different pass above rejects. If
                // it somehow happens anyway, stop rather than following the loop forever:
                // circuit_base.cc guards the same spot for the same reason.
                if (seen[j])
                    break;
                chain.emplace_back(j);
                seen[j] = true;
                if (! fixed[j])
                    break;
                j = *fixed[j];
            }
            result.chains.emplace_back(std::move(chain));
        }

        // Whatever still has a fixed successor and has not been seen is on a cycle.
        for (long i = 0; i < n; ++i) {
            if (! fixed[i] || seen[i])
                continue;
            vector<long> cycle;
            auto j = i;
            auto closed = false;
            do {
                cycle.emplace_back(j);
                seen[j] = true;
                j = *fixed[j];
                if (j == i) {
                    closed = true;
                    break;
                }
            } while (! seen[j]);

            // The walk can only fail to come back to where it started if two successors
            // are fixed to the same value, which the all-different pass above rejects. Drop
            // the walk rather than hand a certificate a list of edges that are not all
            // really there.
            if (closed)
                result.cycles.emplace_back(std::move(cycle));
        }

        return result;
    }

    // Francis and Stuckey's evidence node: one that cannot be a self loop, and so must be
    // on the tour. Without one, a closed cycle is not yet wrong -- every other node might
    // still opt out -- so nothing at all can be inferred. Returns the lowest-numbered such
    // node outside `exclude`, which is their default choice.
    auto find_evidence_node(const vector<IntegerVariableID> & succ, const State & state, const vector<bool> & exclude) -> optional<long>
    {
        for (const auto & [idx, s] : enumerate(succ)) {
            auto i = static_cast<long>(idx);
            if (exclude[i])
                continue;
            if (! state.in_domain(s, Integer{i}))
                return i;
        }
        return nullopt;
    }
}

namespace
{
    // Derive, at the current proof level, that the tour holds at most `cycle.size()` nodes
    // given the assignments round `cycle`.
    //
    // Two cases have to be covered, and they pull in opposite directions:
    //
    //  * no node of the cycle is `first`, so every edge takes its step row, and chaining
    //    those round the cycle telescopes to 0 >= |cycle|, which is absurd;
    //  * some node a of the cycle is `first`, so the edge into a takes its wrap row
    //    instead, and chaining telescopes to |tour| <= |cycle|.
    //
    // Adding the first row to each of the others resolves away the `first` flags, leaving
    // the bound with no case still open. Circuit needs none of this: its anchor is node 0,
    // so it always knows statically which edge is the wrap edge.
    auto derive_tour_at_most(ProofLogger & logger, const SubCircuitPosData & pos_data, const vector<long> & cycle) -> void
    {
        auto k = cycle.size();
        auto next = [&](size_t t) { return cycle[(t + 1) % k]; };

        // Running-saturate, as circuit_scc.cc does: the first push is plain, every
        // subsequent one is followed by `s`, because these sums are not clause-shaped and
        // an intermediate saturation can shrink coefficients usefully.
        auto add_sat = [](PolBuilder & p, ProofLine line) -> PolBuilder & { return p.empty() ? p.add(line) : p.add(line).saturate(); };

        if (! pos_data.defined)
            throw UnexpectedException{"SubCircuit tried to justify an inference with no position encoding"};

        // One comment for the whole derivation rather than one per case: there are
        // |cycle| + 1 cases and a proof comment costs bytes at every firing.
        logger.emit_proof_comment(format("this cycle of {} bounds the whole tour, whichever of its nodes is first", k));

        PolBuilder no_first;
        for (size_t t = 0; t < k; ++t)
            add_sat(no_first, pos_data.edges.at(cycle[t]).at(next(t)).step_ge);

        PolBuilder combine;
        combine.add(no_first.emit(logger, ProofLevel::Current));
        for (size_t s = 0; s < k; ++s) {
            PolBuilder this_first;
            for (size_t t = 0; t < k; ++t) {
                const auto & lines = pos_data.edges.at(cycle[t]).at(next(t));
                add_sat(this_first, next(t) == cycle[s] ? lines.wrap_le : lines.step_le);
            }
            add_sat(combine, this_first.emit(logger, ProofLevel::Current));
        }

        combine.emit(logger, ProofLevel::Current);
    }

    auto propagate_subcircuit(const vector<IntegerVariableID> & succ, const ConstraintID & owner, const SubCircuitPosData & pos_data,
        const ConstraintStateHandle & unassigned_handle, const bool prevent, const State & state, auto & inference, ProofLogger * const logger)
        -> void
    {
        if (! propagate_non_gac_alldifferent(unassigned_handle, state, inference, logger, owner))
            return;

        auto n = succ.size();
        // One walk per call, from scratch. circuit::Prevent keeps its chain endpoints in
        // backtrackable state and folds each newly fixed edge in in O(1); nothing here
        // needs that yet, and a from-scratch walk is much easier to read, but it is the
        // obvious thing to do if this ever shows up in a profile.
        auto edges = walk_fixed_edges(succ, state);

        // A closed cycle of two or more nodes is the whole tour, so every other node has
        // to be a self loop. This is Francis and Stuckey's `check`: for Circuit a short
        // cycle is a flat contradiction, but here it only pins down everyone else.
        for (const auto & cycle : edges.cycles) {
            if (cycle.size() < 2)
                continue; // a self loop says only that its own node is off the tour

            auto on_cycle = vector<bool>(n, false);
            for (auto v : cycle)
                on_cycle[v] = true;

            vector<Literal> off;
            for (size_t m = 0; m < n; ++m) {
                if (on_cycle[m])
                    continue;
                auto here = Integer(static_cast<long long>(m));
                // Skip only a node already sitting on its own index: one fixed to anything
                // else has to go through infer() so that the contradiction is raised and
                // justified. That is the whole of what makes `check` complete -- Francis
                // and Stuckey report failure exactly when a node outside the cycle cannot
                // be a self cycle, and a node fixed elsewhere cannot.
                if (state.optional_single_value(succ[m]) == here)
                    continue;
                off.emplace_back(succ[m] == here);
            }

            // Nothing left to say: the cycle is the whole graph, or everyone else is
            // already a self loop.
            if (off.empty())
                continue;

            auto justf = [&, cycle](const ReasonLiterals &) { derive_tour_at_most(*logger, pos_data, cycle); };
            inference.infer_all(logger, off, JustifyExplicitly{justf, ThenRUP::Yes, hints::SubCircuit{owner}}, generic_reason(succ));
        }

        if (! prevent)
            return;

        // Now the lookahead. A chain of fixed edges must not close into a cycle while some
        // node outside it cannot be a self loop -- that node would have nowhere to go. With
        // no such evidence node there is nothing to infer, because the chain closing and
        // everyone else opting out is a perfectly good solution.
        for (const auto & chain : edges.chains) {
            auto on_chain = vector<bool>(n, false);
            for (auto v : chain)
                on_chain[v] = true;

            if (! find_evidence_node(succ, state, on_chain))
                continue;

            auto start = chain.front();
            auto end = chain.back();
            if (! state.in_domain(succ[end], Integer{start}))
                continue;

            auto closed = chain;
            auto justf = [&, closed](const ReasonLiterals &) { derive_tour_at_most(*logger, pos_data, closed); };
            inference.infer(
                logger, succ[end] != Integer{start}, JustifyExplicitly{justf, ThenRUP::Yes, hints::SubCircuit{owner}}, generic_reason(succ));
        }
    }
}

SubCircuit::SubCircuit(vector<IntegerVariableID> succ) : _succ(std::move(succ))
{
    // As Circuit: two slots pinned to the same constant are a valid (if trivially
    // infeasible) model, so only reject true variable aliasing.
    for (size_t i = 0; i < _succ.size(); ++i) {
        if (is_constant_variable(_succ[i]))
            continue;
        for (size_t j = i + 1; j < _succ.size(); ++j)
            if (_succ[i] == _succ[j])
                throw InvalidProblemDefinitionException{"SubCircuit: successor array contains the same variable handle twice"};
    }
}

auto SubCircuit::with_algorithm(SubCircuitAlgorithm algorithm) -> SubCircuit &
{
    _algorithm = algorithm;
    return *this;
}

auto SubCircuit::with_gac_all_different(optional<bool> enable) -> SubCircuit &
{
    _gac_all_different = enable.value_or(true);
    return *this;
}

auto SubCircuit::prepare(Propagators & propagators, State & initial_state, ProofModel * const model) -> bool
{
    for (const auto & s : _succ) {
        propagators.define_bound(initial_state, model, s, Bound::Lower, 0_i);
        propagators.define_bound(initial_state, model, s, Bound::Upper, Integer(static_cast<long long>(_succ.size() - 1)));
    }

    // As Circuit: the GAC all-different is a child constraint, so it can only be installed
    // from here, and it must carry this constraint's identity or two SubCircuits in one
    // problem would share its labelled rows and pair selectors (issue #449). The non-GAC
    // alternative is pure encoding and lives in define_proof_model().
    if (_gac_all_different) {
        AllDifferent all_diff{_succ};
        all_diff.set_constraint_id(constraint_id());
        std::move(all_diff).install(propagators, initial_state, model);
    }

    NonGacAllDifferentUnassigned unassigned{};
    for (auto v : _succ)
        unassigned.emplace_back(v);
    _state_handles.unassigned = initial_state.add_constraint_state(unassigned);

    return true;
}

auto SubCircuit::define_proof_model(ProofModel & model, const State &) -> void
{
    if (! _gac_all_different)
        define_clique_not_equals_encoding(model, _constraint_id, _succ);

    if (_succ.empty())
        return;

    auto n = static_cast<long>(_succ.size());
    auto tour_size = tour_size_sum(_succ);
    auto & data = _pos_data;
    data.defined = true;

    for (long i = 0; i < n; ++i)
        data.pos.emplace(i, model.create_proof_only_integer_variable(0_i, Integer{n - 1}, "subpos", IntegerVariableProofRepresentation::Bits));

    // first[i]: node i is on the tour and every lower-numbered node is off it, written as
    // "all i+1 of these literals hold". Fully reified, so unit propagation fixes the flag
    // from the successors -- a half-reified flag would leave it free on a solution and the
    // rows below that need it would not check.
    for (long i = 0; i < n; ++i) {
        auto conjunction = WPBSum{} + 1_i * (_succ[i] != Integer{i});
        for (long j = 0; j < i; ++j)
            conjunction += 1_i * (_succ[j] == Integer{j});
        data.first.emplace(i, model.create_proof_flag_fully_reifying(_constraint_id, {i}, "first", conjunction >= Integer{i + 1}));
    }

    // The tour starts at whichever node is first...
    for (long i = 0; i < n; ++i)
        data.first_is_zero.emplace(i,
            model.add_labelled_constraint(
                _constraint_id, "first_pos_" + to_string(i), WPBSum{} + 1_i * data.pos.at(i) <= 0_i, HalfReifyOnConjunctionOf{{data.first.at(i)}}));

    // ...and a node off the tour is given position zero. Nothing here needs the positions to
    // be a permutation -- no certificate below relies on them being distinct -- and an
    // off-tour node takes part in no position row at all: it has no successor other than
    // itself, and by all-different nothing else can point at it either. So the only job
    // these rows have is to leave `pos` determined by the successors under unit
    // propagation, which is what solution checking needs, and zero does that as well as
    // anything.
    //
    // The stdlib decomposition instead numbers off-tour nodes after every on-tour one, in
    // index order, which does make the positions a permutation. That is what to reach for
    // if the wrap rows below ever move into the proof -- the counting argument they would
    // need is a pigeonhole over the positions -- but it costs n rows of n+1 terms where
    // this costs n rows of one, and nothing today buys anything with it.
    for (long i = 0; i < n; ++i)
        model.add_labelled_constraint(
            _constraint_id, "off_pos_" + to_string(i), WPBSum{} + 1_i * data.pos.at(i) <= 0_i, HalfReifyOnConjunctionOf{{_succ[i] == Integer{i}}});

    // Each edge gets two row families rather than Circuit's one, because which edge wraps
    // around is not known statically: it is the edge into whichever node is `first`, and
    // that is only pinned down once the membership literals are. Circuit anchors on node 0,
    // so it writes the `+1` form for every column but 0 and the wrap form for column 0, and
    // never both for the same edge.
    //
    // This is the one place where the encoding carries something for the proof's benefit
    // rather than saying the constraint as compactly as it could, so it is worth recording
    // why rather than leaving it to be rediscovered. The wrap rows are what let a
    // propagator that has found a closed cycle *count*: chaining them gives "the tour is no
    // longer than this cycle" in a bounded number of steps (see derive_tour_at_most).
    // Without them the encoding is smaller -- n^2 row families rather than 2n^2, smaller
    // than the stdlib decomposition -- and still exact, because a cycle avoiding the anchor
    // still chains to 0 = k. But then that counting fact has to be derived instead, and
    // deriving it needs "the on-tour positions are exactly 0..L-1", a pigeonhole induction
    // *conditional on the variable L*. That is the same obstacle that stops circuit_scc.cc's
    // machinery being ported here, so the smaller encoding is not a free reformulation: it
    // is blocked on the same open problem.
    //
    // The other way out is a statically known anchor, which collapses this to exactly
    // Circuit's shape, since only the n edges into a nominated on-tour node can wrap. That
    // needs the caller to name one. The C++ and .scp interfaces could; MiniZinc cannot on
    // the models that matter, because both challenge models post their "this node is
    // visited" constraint *after* the subcircuit call and MiniZinc flattens in source order,
    // so the domain is not yet narrowed when the redefinition runs.
    for (long i = 0; i < n; ++i)
        for (long j = 0; j < n; ++j) {
            if (i == j)
                continue;

            auto step = WPBSum{} + 1_i * data.pos.at(j) + -1_i * data.pos.at(i);
            auto [step_le, step_ge] = model.add_labelled_constraint(_constraint_id, "pos_step_" + to_string(i) + "_" + to_string(j) + "_le",
                "pos_step_" + to_string(i) + "_" + to_string(j) + "_ge", step == 1_i,
                HalfReifyOnConjunctionOf{{_succ[i] == Integer{j}, ! data.first.at(j)}});

            auto wrap = WPBSum{} + 1_i * data.pos.at(j) + -1_i * data.pos.at(i);
            for (const auto & term : tour_size.terms)
                wrap += term;
            auto [wrap_le, wrap_ge] = model.add_labelled_constraint(_constraint_id, "pos_wrap_" + to_string(i) + "_" + to_string(j) + "_le",
                "pos_wrap_" + to_string(i) + "_" + to_string(j) + "_ge", wrap == 1_i,
                HalfReifyOnConjunctionOf{{_succ[i] == Integer{j}, data.first.at(j)}});

            data.edges[i].emplace(j, EdgePosLines{step_le, step_ge, wrap_le, wrap_ge});
        }
}

auto SubCircuit::install_propagators(Propagators & propagators) -> void
{
    auto prevent = std::holds_alternative<Prevent>(_algorithm);

    Triggers triggers;
    triggers.on_instantiated = {_succ.begin(), _succ.end()};
    propagators.install(
        constraint_id(),
        [succ = _succ, owner = constraint_id(), pos_data = std::move(_pos_data), unassigned_handle = _state_handles.unassigned, prevent](
            const State & state, auto & inference, ProofLogger * const logger) -> PropagatorState {
            propagate_subcircuit(succ, owner, pos_data, unassigned_handle, prevent, state, inference, logger);
            // Deliberately not claiming idempotence, unlike circuit::Prevent: forcing a
            // node to be a self loop fixes a successor, which changes the chain structure
            // this pass walked, and one pass makes no attempt to reach the fixpoint of
            // that cascade. The triggers cover it -- every inference here instantiates a
            // successor, so the propagator is re-woken.
            return PropagatorState::Enable;
        },
        triggers);
}

auto SubCircuit::clone() const -> unique_ptr<Constraint>
{
    auto cloned = make_unique<SubCircuit>(_succ);
    cloned->with_algorithm(_algorithm);
    cloned->with_gac_all_different(_gac_all_different);
    return cloned;
}

auto SubCircuit::constraint_type() const -> string
{
    return "subcircuit";
}

auto SubCircuit::s_expr(const ProofModel * const model) const -> SExpr
{
    auto & tracker = model->names_and_ids_tracker();
    vector<SExpr> vars;
    for (const auto & var : _succ)
        vars.push_back(tracker.s_expr_term_of(var));
    return SExpr::list({SExpr::atom(as_string(_constraint_id)), SExpr::atom(constraint_type()), SExpr::list(std::move(vars))});
}
