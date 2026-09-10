#include <gcs/constraints/comparison/comparison.hh>
#include <gcs/constraints/comparison/hints.hh>
#include <gcs/constraints/innards/reified_dispatcher.hh>
#include <gcs/constraints/innards/reified_state.hh>
#include <gcs/exception.hh>
#include <gcs/innards/inference_tracker.hh>
#include <gcs/innards/proofs/names_and_ids_tracker.hh>
#include <gcs/innards/proofs/proof_logger.hh>
#include <gcs/innards/proofs/proof_model.hh>
#include <gcs/innards/propagators.hh>
#include <gcs/innards/s_expr.hh>
#include <gcs/innards/state.hh>

#include <util/overloaded.hh>

#include <version>

#if defined(__cpp_lib_print) && defined(__cpp_lib_format)
#include <format>
#include <print>
#else
#include <fmt/core.h>
#include <fmt/ostream.h>
#endif

#include <sstream>
#include <string>

using namespace gcs;
using namespace gcs::innards;

using std::nullopt;
using std::optional;
using std::string;
using std::unique_ptr;
using std::vector;

#if defined(__cpp_lib_print) && defined(__cpp_lib_format)
using std::format;
using std::print;
#else
using fmt::format;
using fmt::print;
#endif

namespace
{
    // Does this reification condition ask for the *negation* of the inequality
    // to be enforced? MustNotHold does unconditionally, NotIf does under its
    // condition, and the other three do not.
    //
    // An inequality's negation is another inequality of the same family, with
    // the operands the other way round and the strictness flipped: NOT(a < b)
    // is a >= b. So the two negated forms are named and serialised as what they
    // enforce, rather than having no spelling of their own; define_proof_model
    // emits exactly that row for them, which is what keeps the name honest.
    [[nodiscard]] auto enforces_the_negation(const ReificationCondition & cond) -> bool
    {
        return overloaded{
            [](const reif::MustHold &) { return false; },   //
            [](const reif::MustNotHold &) { return true; }, //
            [](const reif::If &) { return false; },         //
            [](const reif::NotIf &) { return true; },       //
            [](const reif::Iff &) { return false; }         //
        }
            .visit(cond);
    }
}

ReifiedCompareLessThanOrMaybeEqual::ReifiedCompareLessThanOrMaybeEqual(
    const IntegerVariableID v1, const IntegerVariableID v2, ReificationCondition cond, bool or_equal, bool vars_swapped) :
    _v1(v1), _v2(v2), _reif_cond(cond), _or_equal(or_equal), _vars_swapped(vars_swapped)
{
}

LessThan::LessThan(const IntegerVariableID v1, const IntegerVariableID v2) : ReifiedCompareLessThanOrMaybeEqual(v1, v2, reif::MustHold{}, false)
{
    // Two constants that happen to be equal is a valid (if trivially
    // infeasible) model; only reject true variable aliasing.
    if (v1 == v2 && ! is_constant_variable(v1))
        throw InvalidProblemDefinitionException{"LessThan: both operands are the same variable handle"};
}

GreaterThan::GreaterThan(const IntegerVariableID v1, const IntegerVariableID v2) :
    ReifiedCompareLessThanOrMaybeEqual(v2, v1, reif::MustHold{}, false, true)
{
    if (v1 == v2 && ! is_constant_variable(v1))
        throw InvalidProblemDefinitionException{"GreaterThan: both operands are the same variable handle"};
}

auto ReifiedCompareLessThanOrMaybeEqual::clone() const -> unique_ptr<Constraint>
{
    return make_unique<ReifiedCompareLessThanOrMaybeEqual>(_v1, _v2, _reif_cond, _or_equal, _vars_swapped);
}

auto ReifiedCompareLessThanOrMaybeEqual::prepare(Propagators &, State & initial_state, ProofModel * const) -> bool
{
    _v1_is_constant = initial_state.optional_single_value(_v1);
    _v2_is_constant = initial_state.optional_single_value(_v2);
    _evaluated_cond = test_reification_condition(initial_state, _reif_cond);
    return true;
}

auto ReifiedCompareLessThanOrMaybeEqual::define_proof_model(ProofModel & model, const State &) -> void
{
    // `role` is the cake_pb_cp @c label role, empty for the forms cake labels
    // with the bare @c[<id>] (a comparison is a single inequality, so there is
    // no half to name). Every row is labelled: an unlabelled row cannot be
    // cited, and the difference-logic presolver lifts these into a global
    // propagator whose `pol`s cite exactly this row. Checked against
    // cake_pb_cp: `less_equal`, `less_than`, `greater_equal`, `greater_than`
    // and their `_if` spellings all come back as @c[<id>], and the `_iff`
    // spelling as @c[<id>][r] and @c[<id>][f].
    //
    // MustNotHold and NotIf get the bare @c[<id>] too. Their row states the
    // *negated* inequality, which is still a single difference inequality with
    // the operands the other way round --- and that is a comparison in its own
    // right, so it is also what they are named and spelled as (see
    // enforces_the_negation() and s_expr()), and the label cake gives the
    // mirrored row is the same bare @c[<id>]. What that costs a citer is that
    // @c[<id>] no longer means `_v1 <op> _v2` for every form: anything citing
    // it must look at the reification condition to know which inequality it got
    // (see gcs/presolvers/difference_logic/difference_logic.cc).
    auto do_less = [&](IntegerVariableID v1, IntegerVariableID v2, optional<HalfReifyOnConjunctionOf> cond, bool or_equal, const string & role) {
        model.add_labelled_constraint(_constraint_id, role, WPBSum{} + 1_i * v1 + -1_i * v2 <= (or_equal ? 0_i : -1_i), cond);
    };

    overloaded{
        [&](const reif::MustHold &) { do_less(_v1, _v2, nullopt, _or_equal, ""); },                                   //
        [&](const reif::MustNotHold &) { do_less(_v2, _v1, nullopt, ! _or_equal, ""); },                              //
        [&](const reif::If & cond) { do_less(_v1, _v2, HalfReifyOnConjunctionOf{{cond.cond}}, _or_equal, ""); },      //
        [&](const reif::NotIf & cond) { do_less(_v2, _v1, HalfReifyOnConjunctionOf{{cond.cond}}, ! _or_equal, ""); }, //
        [&](const reif::Iff & cond) {
            // cake_pb_cp labels the !cond half [f] and the cond half [r].
            do_less(_v1, _v2, HalfReifyOnConjunctionOf{{cond.cond}}, _or_equal, "r");
            do_less(_v2, _v1, HalfReifyOnConjunctionOf{{! cond.cond}}, ! _or_equal, "f");
        } //
    }
        .visit(_reif_cond);
}

auto innards::ConstraintProofModelData<ReifiedCompareLessThanOrMaybeEqual>::primary_row_role(const ReifiedCompareLessThanOrMaybeEqual & c)
    -> optional<string>
{
    // Deliberately a second visit over the same ReificationCondition that
    // define_proof_model visits, rather than a field it sets: define_proof_model
    // does not run when proofs are off, and a presolver that asks this must get
    // the same answer either way. The two are kept honest by
    // constraint_row_test.cc, which posts each kind and checks that a published
    // role resolves to a label the .opb actually contains.
    return overloaded{
        [&](const reif::MustHold &) -> optional<string> { return ""; },         //
        [&](const reif::If &) -> optional<string> { return ""; },               //
        [&](const reif::MustNotHold &) -> optional<string> { return nullopt; }, //
        [&](const reif::NotIf &) -> optional<string> { return nullopt; },       //
        [&](const reif::Iff &) -> optional<string> { return nullopt; }          //
    }
        .visit(c.reification_condition());
}

auto ReifiedCompareLessThanOrMaybeEqual::install_propagators(Propagators & propagators) -> void
{
    // Every reason below is guarded on inference.want_reasons(), and they all
    // have to be: a comparison's reason is only two or three literals, which
    // looks too cheap to be worth a branch, but ReasonLiterals is a small_vector
    // over a nested variant, so an element is large and building one is a
    // memcpy. With proofs off SimpleInferenceTracker never reads it (see the
    // query's own comment in inference_tracker.hh), and at the propagation rates
    // this family runs at that assembly was 30% of instructions and a third of
    // runtime -- see issue #907, and #864 / #873 for the same defect in equals.
    // Keep the guard on any reason added here, including the cold ones: a file
    // where only some reasons are guarded is the state that let this survive.
    if (_v1_is_constant && _v2_is_constant) {
        /* special case: both values are constant, so we're potentially forcing
         * the reification condition, or just giving contradiction, but will never
         * propagate beyond that. */
        bool holds = (_or_equal ? *_v1_is_constant <= *_v2_is_constant : *_v1_is_constant < *_v2_is_constant);
        overloaded{
            [&](const evaluated_reif::MustHold & reif) {
                if (! holds)
                    propagators.install_initialiser(
                        [v1 = _v1, v2 = _v2, v1_is_constant = _v1_is_constant, v2_is_constant = _v2_is_constant, cond = reif.cond,
                            owner = constraint_id()](const State &, auto & inference, ProofLogger * const logger) -> void {
                            const Reason reason = inference.want_reasons()
                                ? Reason{ExplicitReason{ReasonLiterals{{cond, v1 == *v1_is_constant, v2 == *v2_is_constant}}}}
                                : Reason{};
                            inference.infer(logger, ! cond, JustifyUsingRUP{hints::Comparison{owner}}, reason);
                        });
            }, //
            [&](const evaluated_reif::MustNotHold & reif) {
                if (holds)
                    propagators.install_initialiser(
                        [v1 = _v1, v2 = _v2, v1_is_constant = _v1_is_constant, v2_is_constant = _v2_is_constant, cond = reif.cond,
                            owner = constraint_id()](const State &, auto & inference, ProofLogger * const logger) -> void {
                            const Reason reason = inference.want_reasons()
                                ? Reason{ExplicitReason{ReasonLiterals{{cond, v1 == *v1_is_constant, v2 == *v2_is_constant}}}}
                                : Reason{};
                            inference.infer(logger, ! cond, JustifyUsingRUP{hints::Comparison{owner}}, reason);
                        });
            }, //
            [&](const evaluated_reif::Undecided & reif) {
                auto lit = holds ? reif.cond_to_infer_if_constraint_must_hold() : reif.cond_to_infer_if_constraint_must_not_hold();
                if (lit)
                    propagators.install_initialiser(
                        [v1 = _v1, v2 = _v2, v1_is_constant = _v1_is_constant, v2_is_constant = _v2_is_constant, lit = *lit, owner = constraint_id()](
                            const State &, auto & inference, ProofLogger * const logger) -> void {
                            const Reason reason = inference.want_reasons()
                                ? Reason{ExplicitReason{ReasonLiterals{{v1 == *v1_is_constant, v2 == *v2_is_constant}}}}
                                : Reason{};
                            inference.infer(logger, lit, JustifyUsingRUP{hints::Comparison{owner}}, reason);
                        });
            },                                         //
            [](const evaluated_reif::Deactivated &) {} //
        }
            .visit(_evaluated_cond);
    }
    else {
        auto enforce_constraint_must_hold = [v1 = _v1, v2 = _v2, or_equal = _or_equal, owner = constraint_id()](const State & state, auto & inference,
                                                ProofLogger * const logger, const Literal & cond) -> PropagatorState {
            auto v1_bounds = state.bounds(v1), v2_bounds = state.bounds(v2);
            if (! inference.infer_less_than_or_stop(logger, v1, v2_bounds.second + (or_equal ? 1_i : 0_i), JustifyUsingRUP{hints::Comparison{owner}},
                    inference.want_reasons() ? Reason{ExplicitReason{ReasonLiterals{{cond, v2 <= v2_bounds.second}}}} : Reason{}))
                return PropagatorState::Enable; // contradiction: loop sees tracker.contradicted()
            if (! inference.infer_greater_than_or_equal_or_stop(logger, v2, v1_bounds.first + (or_equal ? 0_i : 1_i),
                    JustifyUsingRUP{hints::Comparison{owner}},
                    inference.want_reasons() ? Reason{ExplicitReason{ReasonLiterals{{cond, v1 >= v1_bounds.first}}}} : Reason{}))
                return PropagatorState::Enable;
            return v1_bounds.second < (v2_bounds.first + (or_equal ? 1_i : 0_i)) ? PropagatorState::DisableUntilBacktrack : PropagatorState::Enable;
        };

        auto enforce_constraint_must_not_hold = [v1 = _v1, v2 = _v2, or_equal = _or_equal, owner = constraint_id()](const State & state,
                                                    auto & inference, ProofLogger * const logger, const Literal & cond) -> PropagatorState {
            auto v1_bounds = state.bounds(v1), v2_bounds = state.bounds(v2);
            if (! inference.infer_less_than_or_stop(logger, v2, v1_bounds.second + (! or_equal ? 1_i : 0_i),
                    JustifyUsingRUP{hints::Comparison{owner}},
                    inference.want_reasons() ? Reason{ExplicitReason{ReasonLiterals{{cond, v1 <= v1_bounds.second}}}} : Reason{}))
                return PropagatorState::Enable; // contradiction: loop sees tracker.contradicted()
            if (! inference.infer_greater_than_or_equal_or_stop(logger, v1, v2_bounds.first + (! or_equal ? 0_i : 1_i),
                    JustifyUsingRUP{hints::Comparison{owner}},
                    inference.want_reasons() ? Reason{ExplicitReason{ReasonLiterals{{cond, v2 >= v2_bounds.first}}}} : Reason{}))
                return PropagatorState::Enable;
            return v2_bounds.second < (v1_bounds.first + (! or_equal ? 1_i : 0_i)) ? PropagatorState::DisableUntilBacktrack : PropagatorState::Enable;
        };

        auto infer_cond_when_undecided = [v1 = _v1, v2 = _v2, or_equal = _or_equal, owner = constraint_id()](const State & state, auto & inference,
                                             ProofLogger * const,
                                             const IntegerVariableCondition &) -> ReificationVerdictFor<JustifyUsingRUP<hints::Comparison>> {
            // Aliased non-constant operands: v1<v2 never (when strict),
            // v1≤v2 always. Returning the resolved verdict here lets the
            // dispatcher pin cond at root instead of relying on bounds
            // shrinking to expose the contradiction.
            if (v1 == v2 && ! is_constant_variable(v1)) {
                if (or_equal)
                    return reification_verdict::MustHold<JustifyUsingRUP<hints::Comparison>>{
                        .justification = JustifyUsingRUP{hints::Comparison{owner}}, //
                        .reason = NoReason{}                                        //
                    };
                else
                    return reification_verdict::MustNotHold<JustifyUsingRUP<hints::Comparison>>{
                        .justification = JustifyUsingRUP{hints::Comparison{owner}}, //
                        .reason = NoReason{}                                        //
                    };
            }
            auto v1_bounds = state.bounds(v1), v2_bounds = state.bounds(v2);
            if (or_equal ? (v1_bounds.second <= v2_bounds.first) : (v1_bounds.second < v2_bounds.first)) {
                // v1 has to be less than (or equal): constraint must hold.
                return reification_verdict::MustHold<JustifyUsingRUP<hints::Comparison>>{
                    .justification = JustifyUsingRUP{hints::Comparison{owner}}, //
                    .reason = inference.want_reasons() ? Reason{ExplicitReason{ReasonLiterals{{v1 <= v1_bounds.second, v2 >= v2_bounds.first}}}}
                                                       : Reason{} //
                };
            }
            else if (or_equal ? (v1_bounds.first > v2_bounds.second) : (v1_bounds.first >= v2_bounds.second)) {
                // v1 has to be greater than (or equal): constraint cannot hold.
                return reification_verdict::MustNotHold<JustifyUsingRUP<hints::Comparison>>{
                    .justification = JustifyUsingRUP{hints::Comparison{owner}}, //
                    .reason = inference.want_reasons() ? Reason{ExplicitReason{ReasonLiterals{{v1 >= v1_bounds.first, v2 <= v2_bounds.second}}}}
                                                       : Reason{} //
                };
            }
            else
                return reification_verdict::StillUndecided{};
        };

        Triggers triggers{.on_bounds = {_v1, _v2}};
        install_reified_dispatcher(propagators, constraint_id(), _evaluated_cond, _reif_cond, triggers, std::move(enforce_constraint_must_hold),
            std::move(enforce_constraint_must_not_hold), std::move(infer_cond_when_undecided));
    }
}

// cake_pb_cp's names: less_than / less_equal / greater_than / greater_equal.
// A form that enforces the negation is named for the inequality it enforces, so
// a MustNotHold less_than is a greater_equal: both flips, since the negation
// exchanges the operands and flips the strictness.
auto ReifiedCompareLessThanOrMaybeEqual::constraint_type() const -> std::string
{
    auto negated = enforces_the_negation(_reif_cond);
    return format("{}_{}", (_vars_swapped != negated) ? "greater" : "less", (_or_equal != negated) ? "equal" : "than");
}

auto ReifiedCompareLessThanOrMaybeEqual::s_expr(const ProofModel * const model) const -> SExpr
{
    auto & tracker = model->names_and_ids_tracker();

    // The negated forms take the suffix of the condition they carry, not of the
    // reification kind: constraint_type() has already turned the negation into
    // a comparison of its own, so a NotIf is that comparison, half-reified.
    auto reif_suffix = overloaded{
        [&](const reif::MustHold &) -> string { return ""; },    //
        [&](const reif::MustNotHold &) -> string { return ""; }, //
        [&](const reif::If &) -> string { return "_if"; },       //
        [&](const reif::NotIf &) -> string { return "_if"; },    //
        [&](const reif::Iff &) -> string { return "_iff"; }      //
    }
                           .visit(_reif_cond);

    string cmp = constraint_type() + reif_suffix;

    vector<SExpr> terms{SExpr::atom(as_string(_constraint_id)), SExpr::atom(cmp)};
    if (auto cond = tracker.s_expr_term_of(_reif_cond))
        terms.push_back(std::move(*cond));
    // The constraint enforces _v1 <op> _v2. cake reads "less A B" as A<=B but
    // "greater A B" as A>=B, so for the greater form the operands are reversed:
    // "greater _v2 _v1" reads as _v2 >= _v1, i.e. _v1 <= _v2.
    //
    // A negated form needs nothing here: negating exchanges the operands, and
    // constraint_type() has already swapped less for greater, which exchanges
    // them again. The two cancel, so a MustNotHold `less_than _v1 _v2` is
    // `greater_equal _v1 _v2` --- the same two terms in the same order.
    terms.push_back(tracker.s_expr_term_of(_vars_swapped ? _v2 : _v1));
    terms.push_back(tracker.s_expr_term_of(_vars_swapped ? _v1 : _v2));

    return SExpr::list(std::move(terms));
}
