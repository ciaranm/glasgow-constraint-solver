#include <gcs/constraints/all_different.hh>
#include <gcs/constraints/circuit/circuit.hh>
#include <gcs/constraints/circuit/circuit_base.hh>
#include <gcs/constraints/circuit/circuit_prevent.hh>
#include <gcs/constraints/circuit/circuit_scc.hh>
#include <gcs/constraints/circuit/hints.hh>
#include <gcs/exception.hh>
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
using std::tie;
using std::unique_ptr;
using std::vector;

Circuit::Circuit(vector<IntegerVariableID> succ) : _succ(std::move(succ))
{
    // Two slots pinned to the same constant are a valid (if trivially
    // infeasible) model; only reject true variable aliasing.
    for (size_t i = 0; i < _succ.size(); ++i) {
        if (is_constant_variable(_succ[i]))
            continue;
        for (size_t j = i + 1; j < _succ.size(); ++j)
            if (_succ[i] == _succ[j])
                throw InvalidProblemDefinitionException{"Circuit: successor array contains the same variable handle twice"};
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

auto Circuit::set_up(Propagators & propagators, State & initial_state, ProofModel * const model) -> PosVarDataMap
{
    // Can't have negative values
    for (const auto & s : _succ)
        propagators.define_bound(initial_state, model, s, Bound::Lower, 0_i);

    // Can't have too-large values
    for (const auto & s : _succ)
        propagators.define_bound(initial_state, model, s, Bound::Upper, Integer(static_cast<long long>(_succ.size() - 1)));

    // Define all different, either gac or non-gac
    if (_gac_all_different) {
        AllDifferent all_diff{_succ};
        std::move(all_diff).install(propagators, initial_state, model);
    }
    else {
        // Still need to define the all different encoding.
        if (model)
            define_clique_not_equals_encoding(*model, _constraint_id, _succ);
    }

    // Define encoding to eliminate sub-cycles
    PosVarDataMap pos_var_data{};

    if (model) {
        auto n = static_cast<long long>(_succ.size());
        // Define encoding to eliminate sub-cycles
        // Need extra proof variable: pos[i] = j means "the ith node visited in the circuit is the jth var"
        // WLOG start at node 0, so pos[0] = 0
        pos_var_data.emplace(0,
            PosVarData{"p[0]", model->create_proof_only_integer_variable(0_i, Integer{n - 1}, "pos0", IntegerVariableProofRepresentation::Bits),
                map<long, PosVarLineData>{}});
        model->add_constraint(WPBSum{} + 1_i * pos_var_data.at(0).var <= 0_i);
        // Hence we can only have succ[0] = 0 (self cycle) if there is only one node i.e. n - 1 = 0
        // cake_pb_cp labels these position relations @c[id][pos_suc_<i>_<j>_le/ge].
        auto [leq_line, geq_line] = model->add_labelled_constraint(
            _constraint_id, "pos_suc_0_0_le", "pos_suc_0_0_ge", WPBSum{} == Integer{n - 1}, HalfReifyOnConjunctionOf{{_succ[0] == 0_i}});

        pos_var_data.at(0).plus_one_lines.emplace(0, PosVarLineData{leq_line, geq_line});

        for (unsigned int idx = 1; idx < _succ.size(); ++idx) {
            pos_var_data.emplace(idx,
                PosVarData{format("p[{}]", idx),
                    model->create_proof_only_integer_variable(0_i, Integer{n - 1}, "pos0", IntegerVariableProofRepresentation::Bits),
                    map<long, PosVarLineData>{}});
        }

        for (unsigned int idx = 1; idx < _succ.size(); ++idx) {
            // (succ[0] = i) -> pos[i] - pos[0] = 1
            tie(leq_line, geq_line) =
                model->add_labelled_constraint(_constraint_id, "pos_suc_0_" + std::to_string(idx) + "_le", "pos_suc_0_" + std::to_string(idx) + "_ge",
                    WPBSum{} + 1_i * pos_var_data.at(idx).var + -1_i * 1_c == 0_i, HalfReifyOnConjunctionOf{{_succ[0] == Integer{idx}}});
            pos_var_data.at(0).plus_one_lines.emplace(idx, PosVarLineData{leq_line, geq_line});

            // (succ[i] = 0) -> pos[0] - pos[i] = 1-n
            tie(leq_line, geq_line) =
                model->add_labelled_constraint(_constraint_id, "pos_suc_" + std::to_string(idx) + "_0_le", "pos_suc_" + std::to_string(idx) + "_0_ge",
                    WPBSum{} + 1_i * pos_var_data.at(0).var + -1_i * pos_var_data.at(idx).var == Integer{1 - n},
                    HalfReifyOnConjunctionOf{{_succ[idx] == 0_i}});
            pos_var_data.at(idx).plus_one_lines.emplace(0, PosVarLineData{leq_line, geq_line});

            // (succ[i] = j) -> pos[j] = pos[i] + 1
            for (unsigned int jdx = 1; jdx < _succ.size(); ++jdx) {
                tie(leq_line, geq_line) =
                    model->add_labelled_constraint(_constraint_id, "pos_suc_" + std::to_string(idx) + "_" + std::to_string(jdx) + "_le",
                        "pos_suc_" + std::to_string(idx) + "_" + std::to_string(jdx) + "_ge",
                        WPBSum{} + 1_i * pos_var_data.at(jdx).var + -1_i * pos_var_data.at(idx).var == 1_i,
                        HalfReifyOnConjunctionOf{{_succ[idx] == Integer{jdx}}});
                pos_var_data.at(idx).plus_one_lines.emplace(jdx, PosVarLineData{leq_line, geq_line});
            }
        }
    }

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

    return pos_var_data;
}

auto Circuit::install(Propagators & propagators, State & initial_state, ProofModel * const model) && -> void
{
    auto pos_var_data = set_up(propagators, initial_state, model);

    overloaded{[&](const SCC &) { install_circuit_scc(propagators, initial_state, constraint_id(), _succ, _scc_options, std::move(pos_var_data)); },
        [&](const Prevent &) { install_circuit_prevent(propagators, initial_state, constraint_id(), _succ, std::move(pos_var_data)); }}
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

auto Circuit::s_expr(const ProofModel * const model) const -> SExpr
{
    auto & tracker = model->names_and_ids_tracker();
    vector<SExpr> vars;
    for (const auto & var : _succ)
        vars.push_back(tracker.s_expr_term_of(var));
    return SExpr::list({SExpr::atom(as_string(_constraint_id)), SExpr::atom("circuit"), SExpr::list(std::move(vars))});
}
