#include <gcs/constraints/all_different.hh>
#include <gcs/constraints/circuit/circuit.hh>
#include <gcs/constraints/circuit/circuit_base.hh>
#include <gcs/constraints/circuit/circuit_prevent.hh>
#include <gcs/constraints/circuit/circuit_scc.hh>
#include <gcs/constraints/circuit/hints.hh>
#include <gcs/innards/inference_tracker.hh>
#include <gcs/innards/proofs/names_and_ids_tracker.hh>
#include <gcs/innards/proofs/proof_model.hh>
#include <gcs/innards/propagators.hh>
#include <gcs/innards/s_expr.hh>

#include <util/enumerate.hh>
#include <util/overloaded.hh>

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
using std::format;
#else
#include <fmt/core.h>
using fmt::format;
#endif

using namespace gcs;
using namespace gcs::innards;
using namespace gcs::innards::circuit;

using gcs::circuit::Prevent;
using gcs::circuit::SCC;

using std::make_unique;
using std::map;
using std::optional;
using std::size_t;
using std::unique_ptr;
using std::vector;

Circuit::Circuit(vector<IntegerVariableID> succ) : _succ(std::move(succ))
{
    // The same variable in two slots cannot be all different, so the model is
    // unsatisfiable. That is a legal post, not a misuse: MiniZinc gives two
    // entries one variable whenever a model equates them (#1047), so it is
    // answered with a root contradiction, as AllDifferent does. Two slots
    // pinned to the same constant are left to the propagators.
    for (size_t i = 0; i < _succ.size() && ! _has_duplicate_vars; ++i) {
        if (is_constant_variable(_succ[i]))
            continue;
        for (size_t j = i + 1; j < _succ.size(); ++j)
            if (_succ[i] == _succ[j])
                _has_duplicate_vars = true;
    }
}

auto Circuit::with_algorithm(CircuitAlgorithm algorithm) -> Circuit &
{
    _algorithm = algorithm;
    return *this;
}

auto Circuit::with_gac_all_different(optional<bool> enable) -> Circuit &
{
    _gac_all_different = enable.value_or(true);
    return *this;
}

auto Circuit::with_prune_root(optional<bool> enable) -> Circuit &
{
    _scc_options.prune_root = enable.value_or(true);
    return *this;
}

auto Circuit::with_prune_skip(optional<bool> enable) -> Circuit &
{
    _scc_options.prune_skip = enable.value_or(true);
    return *this;
}

auto Circuit::with_fix_req(optional<bool> enable) -> Circuit &
{
    _scc_options.fix_req = enable.value_or(true);
    return *this;
}

auto Circuit::with_prune_within(optional<bool> enable) -> Circuit &
{
    _scc_options.prune_within = enable.value_or(true);
    return *this;
}

auto Circuit::with_prove_using_dominance(optional<bool> enable) -> Circuit &
{
    _scc_options.prove_using_dominance = enable.value_or(true);
    return *this;
}

auto Circuit::with_enable_comments(optional<bool> enable) -> Circuit &
{
    _scc_options.enable_comments = enable.value_or(true);
    return *this;
}

auto Circuit::with_prove_am1_by_contradiction(optional<bool> enable) -> Circuit &
{
    _scc_options.prove_am1_by_contradiction = enable.value_or(true);
    return *this;
}

auto Circuit::with_short_reasons(optional<bool> enable) -> Circuit &
{
    _scc_options.short_reasons = enable.value_or(true);
    return *this;
}

auto Circuit::prepare(Propagators & propagators, State & initial_state, ProofModel * const model) -> bool
{
    // The empty circuit is vacuously true, as MiniZinc's own decomposition has it: there
    // is no node to visit, so there is nothing to encode or propagate, here, in
    // define_proof_model() or in install_propagators() (issue #1307). SubCircuit treats
    // its empty array the same way.
    if (_succ.empty())
        return true;

    // Can't have negative values
    for (const auto & s : _succ)
        propagators.define_bound(initial_state, model, s, Bound::Lower, 0_i);

    // Can't have too-large values
    for (const auto & s : _succ)
        propagators.define_bound(initial_state, model, s, Bound::Upper, Integer(static_cast<long long>(_succ.size() - 1)));

    // The GAC all-different is a child constraint, which needs propagators, state and
    // model together, so it can only be installed from here. The non-GAC alternative
    // is pure encoding and lives in define_proof_model(); either way the rows land
    // before the position encoding, as they did before.
    // With a repeated variable nothing propagates, so there is no child: the rows it
    // would have written come from define_proof_model() instead.
    if (_gac_all_different && ! _has_duplicate_vars) {
        AllDifferent all_diff{_succ};
        // The child must carry this constraint's identity, as SeqPrecedeChain's does:
        // AllDifferent keys its labelled OPB lines and its pair selectors on its id, so
        // an unnamed child writes @c[unnamed] rows and x[unnamed] flags that two such
        // circuits in one problem would share (issue #449). With the id set, the rows
        // are the ones the non-GAC branch would have written anyway.
        all_diff.set_constraint_id(constraint_id());
        std::move(all_diff).install(propagators, initial_state, model);
    }

    // Backtrackable state for whichever algorithm install_propagators() picks. Both
    // track the unassigned successors; only Prevent keeps the incremental chain
    // endpoints, so only Prevent pays for that slot.
    NonGacAllDifferentUnassigned unassigned{};
    for (auto v : _succ)
        unassigned.emplace_back(v);
    _state_handles.unassigned = initial_state.add_constraint_state(unassigned);

    if (std::holds_alternative<Prevent>(_algorithm))
        _state_handles.chain = initial_state.add_constraint_state(make_prevent_chain_data(_succ.size()));

    return true;
}

auto Circuit::define_proof_model(ProofModel & model, const State &) -> void
{
    // The all-different encoding. Under the GAC option the child AllDifferent that
    // prepare() installed has already emitted it. With a repeated variable, the
    // pair rows for the two slots collapse to a unit and its negation, which is
    // what the root contradiction cites.
    if (! _gac_all_different || _has_duplicate_vars)
        define_clique_not_equals_encoding(model, _constraint_id, _succ);

    // No position encoding for the empty circuit: its positions would range over 0..-1.
    if (_succ.empty())
        return;

    // Define encoding to eliminate sub-cycles. This is cake_pb_cp's encoding, names,
    // labels and row contents alike, so that a proof which reasons about a position
    // checks against cake's OPB as well as ours (#1459).
    auto & pos_var_data = _pos_var_data;

    auto n = static_cast<long long>(_succ.size());
    // pos[i] = k means "node i is the kth visited, starting from node 0". Each is a
    // free bit-sum over 0..n-1 whose bits are named as cake's x[id][i_b][bin], with no
    // bound rows of its own: the labelled rows below are its bounds, as in cake.
    for (unsigned int idx = 0; idx < _succ.size(); ++idx)
        pos_var_data.emplace(idx,
            PosVarData{format("p[{}]", idx),
                model.create_proof_only_integer_variable(0_i, Integer{n - 1}, "pos" + std::to_string(idx), IntegerVariableProofRepresentation::Bits,
                    CakeBitNaming{_constraint_id, {static_cast<long long>(idx)}, "bin", std::nullopt, true}),
                map<long, PosVarLineData>{}});

    // WLOG start at node 0, so pos[0] = 0, and every pos[i] <= n - 1.
    model.add_labelled_constraint(_constraint_id, "pos0eq0", WPBSum{} + 1_i * pos_var_data.at(0).var <= 0_i);
    for (unsigned int idx = 0; idx < _succ.size(); ++idx)
        model.add_labelled_constraint(_constraint_id, format("pos{}lt{}", idx, n), WPBSum{} + 1_i * pos_var_data.at(idx).var <= Integer{n - 1});

    // cake_pb_cp labels these position relations @c[id][pos_suc_<i>_<j>_le/ge]:
    //   succ[i] = 0 -> pos[i] = n - 1          (the edge that closes the tour)
    //   succ[i] = j -> pos[j] - pos[i] = 1     (j != 0, including i = 0 and i = j)
    // so succ[0] = 0 is possible only when n = 1, and succ[i] = i (i != 0) never.
    for (unsigned int idx = 0; idx < _succ.size(); ++idx) {
        for (unsigned int jdx = 0; jdx < _succ.size(); ++jdx) {
            auto sum = (0 == jdx) ? WPBSum{} + 1_i * pos_var_data.at(idx).var == Integer{n - 1}
                                  : WPBSum{} + 1_i * pos_var_data.at(jdx).var + -1_i * pos_var_data.at(idx).var == 1_i;
            auto cell = std::to_string(idx) + "_" + std::to_string(jdx);
            auto [leq_line, geq_line] = model.add_labelled_constraint(_constraint_id, "pos_suc_" + cell + "_le", "pos_suc_" + cell + "_ge",
                std::move(sum), HalfReifyOnConjunctionOf{{_succ[idx] == Integer{jdx}}});
            pos_var_data.at(idx).plus_one_lines.emplace(jdx, PosVarLineData{leq_line, geq_line});
        }
    }
}

auto Circuit::install_propagators(Propagators & propagators) -> void
{
    if (_has_duplicate_vars) {
        propagators.install_initial_contradiction(constraint_id(), constraint_type(),
            "A Circuit constraint was posted with the same variable more than once", JustifyUsingRUP{hints::Circuit{constraint_id()}});
        return;
    }

    // Nothing to propagate for the empty circuit, and the SCC propagator's walk starts at
    // node 0, which it does not have.
    if (_succ.empty())
        return;

    // Infer succ[i] != i at top of search, but no other propagation defined here: use circuit::Prevent or circuit::SCC
    if (_succ.size() > 1) {
        propagators.install(
            constraint_id(),
            [succ = _succ, owner = constraint_id()](const State &, auto & inference, ProofLogger * const logger) -> PropagatorState {
                for (auto [idx, s] : enumerate(succ)) {
                    inference.infer_not_equal(
                        logger, s, Integer(static_cast<long long>(idx)), JustifyUsingRUP{hints::Circuit{owner}}, generic_reason(succ));
                }
                return PropagatorState::DisableUntilBacktrack;
            },
            Triggers{});
    }

    overloaded{
        [&](const SCC &) { install_circuit_scc(propagators, constraint_id(), _succ, _scc_options, std::move(_pos_var_data), _state_handles); }, //
        [&](const Prevent &) { install_circuit_prevent(propagators, constraint_id(), _succ, std::move(_pos_var_data), _state_handles); }}
        .visit(_algorithm);
}

auto Circuit::clone() const -> unique_ptr<Constraint>
{
    auto cloned = make_unique<Circuit>(_succ);
    cloned->with_algorithm(_algorithm);
    cloned->with_gac_all_different(_gac_all_different);
    cloned->_scc_options = _scc_options;
    return cloned;
}

auto Circuit::constraint_type() const -> std::string
{
    return "circuit";
}

auto Circuit::s_expr(const ProofModel * const model) const -> SExpr
{
    auto & tracker = model->names_and_ids_tracker();
    vector<SExpr> vars;
    for (const auto & var : _succ)
        vars.push_back(tracker.s_expr_term_of(var));
    return SExpr::list({SExpr::atom(as_string(_constraint_id)), SExpr::atom(constraint_type()), SExpr::list(std::move(vars))});
}
