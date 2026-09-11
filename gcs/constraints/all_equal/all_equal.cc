#include <gcs/constraints/all_equal/all_equal.hh>
#include <gcs/constraints/all_equal/hints.hh>
#include <gcs/constraints/innards/justify_not_in_range.hh>
#include <gcs/innards/inference_tracker.hh>
#include <gcs/innards/proofs/names_and_ids_tracker.hh>
#include <gcs/innards/proofs/proof_logger.hh>
#include <gcs/innards/proofs/proof_model.hh>
#include <gcs/innards/propagators.hh>
#include <gcs/innards/reason.hh>
#include <gcs/innards/s_expr.hh>
#include <gcs/innards/state.hh>

#include <memory>
#include <sstream>
#include <utility>
#include <version>

#if defined(__cpp_lib_print) && defined(__cpp_lib_format)
#include <print>
#else
#include <fmt/ostream.h>
#endif

using namespace gcs;
using namespace gcs::innards;

using std::make_unique;
using std::move;
using std::pair;
using std::string;
using std::stringstream;
using std::to_string;
using std::unique_ptr;
using std::vector;

#if defined(__cpp_lib_print) && defined(__cpp_lib_format)
using std::print;
#else
using fmt::print;
#endif

AllEqual::AllEqual(vector<IntegerVariableID> vars) : _vars(move(vars))
{
}

auto AllEqual::clone() const -> unique_ptr<Constraint>
{
    return make_unique<AllEqual>(_vars);
}

auto AllEqual::prepare(Propagators &, State &, ProofModel * const) -> bool
{
    return _vars.size() > 1;
}

auto AllEqual::define_proof_model(ProofModel & model, const State &) -> void
{
    // cake_pb_cp labels each consecutive-pair equality's two halves
    // @c[id][<i>le] (vars[i+1] - vars[i] >= 0) and @c[id][<i>ge]
    // (vars[i] - vars[i+1] >= 0). Match those so the encoding lines up with
    // cake's. The proof never references these lines by name (the propagator
    // justifies its prunings by RUP), so this is a pure OPB-definition rename.
    for (size_t i = 0; i + 1 < _vars.size(); ++i)
        model.add_labelled_constraint(
            _constraint_id, to_string(i) + "le", to_string(i) + "ge", WPBSum{} + 1_i * _vars[i] + -1_i * _vars[i + 1] == 0_i);
}

auto AllEqual::install_propagators(Propagators & propagators) -> void
{
    Triggers triggers;
    triggers.on_change.insert(triggers.on_change.end(), _vars.begin(), _vars.end());

    propagators.install(
        constraint_id(),
        [vars = move(_vars), owner = constraint_id()](const State & state, auto & inference, ProofLogger * const logger) -> PropagatorState {
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
                    inference.infer_greater_than_or_equal(
                        logger, vars[i], lo, JustifyUsingRUP{hints::AllEqual{owner}}, ExplicitReason{ReasonLiterals{{argmax_lo >= lo}}});
                if (state.upper_bound(vars[i]) > hi)
                    inference.infer_less_than(
                        logger, vars[i], hi + 1_i, JustifyUsingRUP{hints::AllEqual{owner}}, ExplicitReason{ReasonLiterals{{argmin_hi <= hi}}});
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
                // Snapshot every domain up front. The old code took `common` from
                // the state at the top of this block and then pruned against it, so
                // the removal set is the one the domains had on entry; recomputing
                // a domain mid-loop would use one this block has already shrunk and
                // could remove more. Snapshots keep the removals exactly what they
                // were.
                vector<IntervalSet<Integer>> domains;
                domains.reserve(n);
                for (const auto & v : vars)
                    domains.push_back(state.copy_of_values(v));

                auto common = domains[0];
                for (size_t i = 1; i < n; ++i)
                    common.intersect_with(domains[i]);

                // The values to remove were already computed as intervals and then
                // written out one at a time. What stopped that being a one-line
                // change is the *witness*: the reason names some variable whose
                // domain lacks the value, and because the difference is taken
                // against the intersection of every domain, which variable that is
                // can change part-way through an interval.
                //
                // So the difference is taken against one variable at a time
                // instead. Every range that yields against `vars[j]` has `vars[j]`
                // as a witness for the whole of it, by construction. Ranges already
                // accounted for are struck off as we go, so each is removed once
                // rather than once per variable that happens to witness it --- which
                // matters, since every emission carries two lemmas.
                //
                // The union over j of (D_i minus D_j) is D_i minus the intersection
                // of the others, and that is D_i minus `common`, so the removal set
                // is exactly what it was.
                //
                // A range asserts order atoms and never bits, so it cannot cross
                // the model's bit-sum equality on its own; the two ge-layer bound
                // lemmas carry the bounds over to vars[j] first, and then the
                // reason's range literal is a clause with every literal falsified.
                // Same helper, and same argument, as equals.cc --- the model here is
                // a chain of consecutive-pair equalities, so for non-adjacent i and
                // j unit propagation walks the chain between them. Views are no
                // different: a view's range literals live on its own encoded
                // variable, which is the representation the chain equalities are
                // stated in.
                auto prune_range = [&](size_t i, size_t j, Integer l, Integer u) {
                    inference.infer_not_in_range(logger, vars[i], l, u,
                        JustifyExplicitly{[logger, &vars, i, j, l, u](const ReasonLiterals & r) {
                                              justify_not_in_range_across_equality(*logger, r, vars[i], l, u, vars[j], l, u);
                                          },
                            ThenRUP::Yes, hints::AllEqual{owner}},
                        ExplicitReason{ReasonLiterals{{not_in_range(vars[j], l, u)}}});
                };

                for (size_t i = 0; i < n; ++i) {
                    for (auto [l, u] : domains[i].each_interval_minus(common)) {
                        if (l == u) {
                            // A width-1 range literal *is* the eq atom -- the proof
                            // machinery never makes an interval of one -- so saying
                            // it that way is the same inference, and finding its
                            // witness is n in_domain checks against no set at all.
                            // Worth the branch: over holey domains most removed
                            // intervals are single values, and routing them through
                            // the interval path instead cost 2%.
                            IntegerVariableID witness = vars[0];
                            for (size_t j = 0; j < n; ++j)
                                if (! state.in_domain(vars[j], l)) {
                                    witness = vars[j];
                                    break;
                                }
                            inference.infer_not_equal(
                                logger, vars[i], l, JustifyUsingRUP{hints::AllEqual{owner}}, ExplicitReason{ReasonLiterals{{witness != l}}});
                            continue;
                        }

                        // Almost always one variable's hole explains the whole
                        // of a removed interval, and then there is nothing to
                        // split: a scan for a single covering witness is n
                        // merge-walks with no allocation, where building the
                        // leftover set to subtract from costs one whatever
                        // happens. Measured: with the splitting machinery run
                        // unconditionally this was 2% slower on a search over
                        // holey domains, and the fast path takes that back.
                        IntervalSet<Integer> range{l, u};
                        auto witness = n;
                        for (size_t j = 0; j < n; ++j)
                            if (j != i && ! domains[j].contains_any_of(range)) {
                                witness = j;
                                break;
                            }

                        if (witness != n) {
                            prune_range(i, witness, l, u);
                            continue;
                        }

                        // Mixed: different parts of this interval are missing
                        // from different variables, which is the whole reason
                        // the per-value form needed a witness lookup per value.
                        // Take the difference against one variable at a time and
                        // strike off what it accounts for, so each part is
                        // removed once rather than once per variable that
                        // witnesses it --- every emission carries two lemmas.
                        IntervalSet<Integer> todo{l, u};
                        for (size_t j = 0; j < n && ! todo.empty(); ++j) {
                            if (j == i)
                                continue;

                            // Collected before erasing: each_interval_minus()
                            // borrows `todo`, which must not be modified while
                            // the generator is live.
                            vector<pair<Integer, Integer>> witnessed;
                            for (auto [wl, wu] : todo.each_interval_minus(domains[j]))
                                witnessed.emplace_back(wl, wu);

                            for (auto [wl, wu] : witnessed) {
                                todo.erase_range(wl, wu);
                                prune_range(i, j, wl, wu);
                            }
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

auto AllEqual::constraint_type() const -> std::string
{
    return "all_equal";
}

auto AllEqual::s_expr(const ProofModel * const model) const -> SExpr
{
    auto & tracker = model->names_and_ids_tracker();
    std::vector<SExpr> vars;
    for (const auto & v : _vars)
        vars.push_back(tracker.s_expr_term_of(v));
    return SExpr::list({SExpr::atom(as_string(_constraint_id)), SExpr::atom(constraint_type()), SExpr::list(std::move(vars))});
}
