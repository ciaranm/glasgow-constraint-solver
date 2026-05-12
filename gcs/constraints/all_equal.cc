#include <gcs/constraints/all_equal.hh>
#include <gcs/innards/inference_tracker.hh>
#include <gcs/innards/proofs/names_and_ids_tracker.hh>
#include <gcs/innards/proofs/proof_logger.hh>
#include <gcs/innards/proofs/proof_model.hh>
#include <gcs/innards/propagators.hh>
#include <gcs/innards/reason.hh>
#include <gcs/innards/state.hh>

#include <memory>
#include <sstream>
#include <utility>
#include <version>

#if defined(__cpp_lib_print) && defined(__cpp_lib_format)
#include <format>
#include <print>
#else
#include <fmt/ostream.h>
#endif

using namespace gcs;
using namespace gcs::innards;

using std::make_unique;
using std::move;
using std::string;
using std::stringstream;
using std::unique_ptr;
using std::vector;

#if defined(__cpp_lib_print) && defined(__cpp_lib_format)
using std::print;
#else
using fmt::print;
#endif

AllEqual::AllEqual(vector<IntegerVariableID> vars) :
    _vars(move(vars))
{
}

auto AllEqual::clone() const -> unique_ptr<Constraint>
{
    return make_unique<AllEqual>(_vars);
}

auto AllEqual::install(Propagators & propagators, State & initial_state, ProofModel * const optional_model) && -> void
{
    if (! prepare(propagators, initial_state, optional_model))
        return;

    if (optional_model)
        define_proof_model(*optional_model);

    install_propagators(propagators);
}

auto AllEqual::prepare(Propagators &, State &, ProofModel * const) -> bool
{
    return _vars.size() > 1;
}

auto AllEqual::define_proof_model(ProofModel & model) -> void
{
    for (size_t i = 0; i + 1 < _vars.size(); ++i)
        model.add_constraint("AllEqual", "chain step",
            WPBSum{} + 1_i * _vars[i] + -1_i * _vars[i + 1] == 0_i);
}

auto AllEqual::install_propagators(Propagators & propagators) -> void
{
    Triggers triggers;
    triggers.on_change.insert(triggers.on_change.end(), _vars.begin(), _vars.end());

    propagators.install([vars = move(_vars)](
                            const State & state, auto & inference, ProofLogger * const logger) -> PropagatorState {
        auto n = vars.size();

        // Tighten each var to [lo, hi] where lo is the largest lower bound
        // and hi is the smallest upper bound across all vars. Use a fixed
        // witness var per direction so RUP only has to chain through the
        // OPB equalities.
        auto [lo, hi] = state.bounds(vars[0]);
        auto argmax_lo = vars[0];
        auto argmin_hi = vars[0];
        for (size_t i = 1; i < n; ++i) {
            auto [lbi, ubi] = state.bounds(vars[i]);
            if (lbi > lo) {
                lo = lbi;
                argmax_lo = vars[i];
            }
            if (ubi < hi) {
                hi = ubi;
                argmin_hi = vars[i];
            }
        }

        for (size_t i = 0; i < n; ++i) {
            if (state.lower_bound(vars[i]) < lo)
                inference.infer_greater_than_or_equal(logger, vars[i], lo,
                    JustifyUsingRUP{},
                    ReasonFunction{[w = argmax_lo, lo = lo]() { return Reason{{w >= lo}}; }});
            if (state.upper_bound(vars[i]) > hi)
                inference.infer_less_than(logger, vars[i], hi + 1_i,
                    JustifyUsingRUP{},
                    ReasonFunction{[w = argmin_hi, hi = hi]() { return Reason{{w < hi + 1_i}}; }});
        }

        // If any domain has holes, prune every var to the intersection of
        // all domains. Reason for "vars[i] != val" is "witness != val" for
        // any var whose domain doesn't contain val.
        bool any_holes = false;
        for (const auto & v : vars)
            if (state.domain_has_holes(v)) {
                any_holes = true;
                break;
            }

        if (any_holes) {
            auto common = state.copy_of_values(vars[0]);
            for (size_t i = 1; i < n; ++i)
                common.intersect_with(state.copy_of_values(vars[i]));

            for (size_t i = 0; i < n; ++i) {
                auto vi_set = state.copy_of_values(vars[i]);
                for (auto [l, u] : vi_set.each_interval_minus(common)) {
                    for (Integer val = l; val <= u; ++val) {
                        IntegerVariableID witness = vars[0];
                        for (size_t j = 0; j < n; ++j)
                            if (! state.in_domain(vars[j], val)) {
                                witness = vars[j];
                                break;
                            }
                        inference.infer_not_equal(logger, vars[i], val,
                            JustifyUsingRUP{},
                            ReasonFunction{[w = witness, val]() { return Reason{{w != val}}; }});
                    }
                }
            }
        }

        // Entailed once any var is single-valued: the chain equalities will
        // have propagated that value to every other var (or contradicted),
        // so further calls have nothing to do.
        if (state.has_single_value(vars[0]))
            return PropagatorState::DisableUntilBacktrack;

        return PropagatorState::Enable;
    },
        triggers);
}

auto AllEqual::s_exprify(const ProofModel * const model) const -> string
{
    stringstream s;
    print(s, "{} all_equal", _name);
    for (const auto & v : _vars)
        print(s, " {}", model->names_and_ids_tracker().s_expr_name_of(v));
    return s.str();
}
