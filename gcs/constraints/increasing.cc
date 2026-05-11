#include <gcs/constraints/increasing.hh>
#include <gcs/innards/inference_tracker.hh>
#include <gcs/innards/proofs/names_and_ids_tracker.hh>
#include <gcs/innards/proofs/proof_logger.hh>
#include <gcs/innards/proofs/proof_model.hh>
#include <gcs/innards/propagators.hh>
#include <gcs/innards/state.hh>

#include <version>

#if defined(__cpp_lib_print) && defined(__cpp_lib_format)
#include <print>
#else
#include <fmt/ostream.h>
#endif

#include <algorithm>
#include <sstream>
#include <string>

using namespace gcs;
using namespace gcs::innards;

using std::make_unique;
using std::move;
using std::ranges::reverse;
using std::string;
using std::stringstream;
using std::unique_ptr;
using std::vector;

#if defined(__cpp_lib_print) && defined(__cpp_lib_format)
using std::print;
#else
using fmt::print;
#endif

IncreasingChain::IncreasingChain(vector<IntegerVariableID> vars, bool strict, bool descending) :
    _vars(move(vars)),
    _strict(strict),
    _descending(descending)
{
}

auto IncreasingChain::clone() const -> unique_ptr<Constraint>
{
    return make_unique<IncreasingChain>(_vars, _strict, _descending);
}

auto IncreasingChain::install(Propagators & propagators, State & initial_state, ProofModel * const optional_model) && -> void
{
    if (! prepare(propagators, initial_state, optional_model))
        return;

    if (optional_model)
        define_proof_model(*optional_model);

    install_propagators(propagators);
}

auto IncreasingChain::prepare(Propagators &, State &, ProofModel * const) -> bool
{
    // Reverse for descending so the rest of install is single-direction.
    _ordered_vars = move(_vars);
    if (_descending)
        reverse(_ordered_vars);

    return _ordered_vars.size() > 1;
}

auto IncreasingChain::define_proof_model(ProofModel & model) -> void
{
    auto offset = _strict ? -1_i : 0_i;
    for (size_t i = 0; i + 1 < _ordered_vars.size(); ++i)
        model.add_constraint("IncreasingChain", "chain step",
            WPBSum{} + 1_i * _ordered_vars[i] + -1_i * _ordered_vars[i + 1] <= offset);
}

auto IncreasingChain::install_propagators(Propagators & propagators) -> void
{
    auto step = _strict ? 1_i : 0_i;

    Triggers triggers;
    triggers.on_bounds.insert(triggers.on_bounds.end(), _ordered_vars.begin(), _ordered_vars.end());

    propagators.install([vars = move(_ordered_vars), step](
                            const State & state, auto & inference, ProofLogger * const logger) -> PropagatorState {
        auto n = vars.size();

        // Forward sweep: lb(vars[i]) >= lb(vars[i-1]) + step.
        auto prev_lb = state.bounds(vars[0]).first;
        for (size_t i = 1; i < n; ++i) {
            auto needed = prev_lb + step;
            auto cur_lb = state.bounds(vars[i]).first;
            if (needed > cur_lb) {
                auto reason_lb = prev_lb;
                inference.infer_greater_than_or_equal(logger, vars[i], needed,
                    JustifyUsingRUP{},
                    ReasonFunction{[v = vars[i - 1], reason_lb]() { return Reason{{v >= reason_lb}}; }});
                prev_lb = needed;
            }
            else {
                prev_lb = cur_lb;
            }
        }

        // Backward sweep: ub(vars[i]) <= ub(vars[i+1]) - step.
        auto prev_ub = state.bounds(vars[n - 1]).second;
        for (size_t k = 0; k + 1 < n; ++k) {
            auto i = n - 2 - k;
            auto needed = prev_ub - step;
            auto cur_ub = state.bounds(vars[i]).second;
            if (needed < cur_ub) {
                auto reason_ub = prev_ub;
                inference.infer_less_than(logger, vars[i], needed + 1_i,
                    JustifyUsingRUP{},
                    ReasonFunction{[v = vars[i + 1], reason_ub]() { return Reason{{v < reason_ub + 1_i}}; }});
                prev_ub = needed;
            }
            else {
                prev_ub = cur_ub;
            }
        }

        // Entailment: every adjacent pair is already separated by at least step.
        bool entailed = true;
        for (size_t i = 0; i + 1 < n; ++i) {
            if (state.bounds(vars[i]).second + step > state.bounds(vars[i + 1]).first) {
                entailed = false;
                break;
            }
        }
        return entailed ? PropagatorState::DisableUntilBacktrack : PropagatorState::Enable;
    },
        triggers);
}

auto IncreasingChain::s_exprify(const ProofModel * const model) const -> string
{
    stringstream s;

    const char * keyword = _strict
        ? (_descending ? "strictly_decreasing" : "strictly_increasing")
        : (_descending ? "decreasing" : "increasing");

    print(s, "{} {}", _name, keyword);
    for (const auto & v : _vars)
        print(s, " {}", model->names_and_ids_tracker().s_expr_name_of(v));

    return s.str();
}
