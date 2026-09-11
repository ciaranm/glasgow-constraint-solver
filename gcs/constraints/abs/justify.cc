#include <gcs/constraints/abs/justify.hh>
#include <gcs/innards/proofs/names_and_ids_tracker.hh>
#include <gcs/innards/proofs/pol_builder.hh>

#include <util/overloaded.hh>

using namespace gcs;
using namespace gcs::innards;

using std::holds_alternative;
using std::variant;
using std::visit;

namespace
{
    // The pol-side item defining a literal: a proof line when the atom has a
    // reified definition, or the literal itself when the atom is primitive
    // (say, the bound coincides with the variable's declared domain boundary,
    // or a 0/1 variable's own bit). The helpers below resolve with either;
    // grabbing the ProofLine alternative unconditionally was issue #446.
    using PolItem = variant<ProofLine, XLiteral>;

    auto add_item(PolBuilder & builder, const PolItem & item, const NamesAndIDsTracker & tracker) -> void
    {
        visit(overloaded{
                  [&](const ProofLine & l) { builder.add(l); },        //
                  [&](const XLiteral & x) { builder.add(x, tracker); } //
              },
            item);
    }

    // PB resolution: sum the operand proof lines (or literal axioms) and
    // saturate, eliminating any literals whose coefficients cancel.
    auto emit_resolution(ProofLogger & logger, const PolItem & a, const PolItem & b) -> void
    {
        auto & tracker = logger.names_and_ids_tracker();
        PolBuilder builder;
        add_item(builder, a, tracker);
        add_item(builder, b, tracker);
        builder.saturate().emit(logger, ProofLevel::Temporary);
    }

    auto emit_resolution(ProofLogger & logger, const PolItem & a, const PolItem & b, const PolItem & c) -> void
    {
        auto & tracker = logger.names_and_ids_tracker();
        PolBuilder builder;
        add_item(builder, a, tracker);
        add_item(builder, b, tracker);
        add_item(builder, c, tracker);
        builder.saturate().emit(logger, ProofLevel::Temporary);
    }
}

auto gcs::innards::justify_abs_hole(ProofLogger & logger, const ReasonLiterals & reason, IntegerVariableID v1, IntegerVariableID v2, Integer val)
    -> void
{
    // (v2 == val /\ v1 >= 0) -> v1 == val
    logger.emit_rup_proof_line_under_reason_then_deview(
        reason, WPBSum{} + 1_i * (v1 < 0_i) + 1_i * (v1 == val) + 1_i * (v2 != val) >= 1_i, ProofLevel::Temporary);

    // (v2 == val /\ v1 < 0) -> v1 == -val
    logger.emit_rup_proof_line_under_reason_then_deview(
        reason, WPBSum{} + 1_i * (v1 >= 0_i) + 1_i * (v1 != -val) + 1_i * (v2 != val) >= 1_i, ProofLevel::Temporary);

    // rest follows by RUP
}

auto gcs::innards::justify_abs_hole_range(ProofLogger & logger, const ReasonLiterals & reason, const IntegerVariableID & v1,
    const IntegerVariableID & v2, Integer lo, Integer hi, ProofLine abs_nonneg_le, ProofLine abs_nonneg_ge, ProofLine abs_neg_le,
    ProofLine abs_neg_ge) -> void
{
    auto & ids = logger.names_and_ids_tracker();

    // Each resolution is the model half plus the defining item of the two atoms
    // whose arithmetic it uses; the halves' bit coefficients are the operands'
    // own, so v1's and v2's terms cancel and saturation leaves a clause.
    //
    // v1 >= 0 branch, where abs_nonneg_le is v2 <= v1 and abs_nonneg_ge is
    // v2 >= v1. v2 >= lo carries to v1 >= lo, and v2 <= hi to v1 <= hi.
    emit_resolution(logger, abs_nonneg_le, ids.need_pol_item_defining_literal(v2 >= lo), ids.need_pol_item_defining_literal(v1 < lo));
    emit_resolution(logger, abs_nonneg_ge, ids.need_pol_item_defining_literal(v2 < hi + 1_i), ids.need_pol_item_defining_literal(v1 >= hi + 1_i));

    // v1 < 0 branch, where abs_neg_le is v2 <= -v1 and abs_neg_ge is v2 >= -v1,
    // so the range is mirrored: v2 >= lo carries to v1 <= -lo, and v2 <= hi to
    // v1 >= -hi.
    emit_resolution(logger, abs_neg_le, ids.need_pol_item_defining_literal(v2 >= lo), ids.need_pol_item_defining_literal(v1 >= -lo + 1_i));
    emit_resolution(logger, abs_neg_ge, ids.need_pol_item_defining_literal(v2 < hi + 1_i), ids.need_pol_item_defining_literal(v1 < -hi));

    // With each branch's pair in the database, v2 inside [lo, hi] falsifies
    // every literal of that branch's reason literal, leaving the sign. Spelled
    // with the two order atoms rather than the range literal, so no range flag
    // has to be defined for this line.
    logger.emit_rup_proof_line_under_reason(
        reason, WPBSum{} + 1_i * (v1 < 0_i) + 1_i * (v2 < lo) + 1_i * (v2 >= hi + 1_i) >= 1_i, ProofLevel::Temporary);
    logger.emit_rup_proof_line_under_reason(
        reason, WPBSum{} + 1_i * (v1 >= 0_i) + 1_i * (v2 < lo) + 1_i * (v2 >= hi + 1_i) >= 1_i, ProofLevel::Temporary);

    // The two signs being a literal and its negation, the rest follows by RUP.
}

auto gcs::innards::justify_abs_preimage_range(ProofLogger & logger, const IntegerVariableID & v1, const IntegerVariableID & v2, Integer lo,
    Integer hi, ProofLine abs_nonneg_le, ProofLine abs_nonneg_ge, ProofLine abs_neg_le, ProofLine abs_neg_ge) -> void
{
    auto & ids = logger.names_and_ids_tracker();

    if (lo >= 0_i) {
        // v1 inside [lo, hi] with lo >= 0 forces the sign, and that is the first
        // resolution: v1 >= lo and v1 <= -1 are contradictory arithmetic, so
        // saturation leaves `v1 < lo \/ v1 >= 0`.
        emit_resolution(logger, ids.need_pol_item_defining_literal(v1 >= lo), ids.need_pol_item_defining_literal(v1 < 0_i));

        // Then the two bounds the nonneg row licenses, in the other direction to
        // the image case: v1 >= lo carries to v2 >= lo, v1 <= hi to v2 <= hi.
        emit_resolution(logger, abs_nonneg_ge, ids.need_pol_item_defining_literal(v1 >= lo), ids.need_pol_item_defining_literal(v2 < lo));
        emit_resolution(logger, abs_nonneg_le, ids.need_pol_item_defining_literal(v1 < hi + 1_i), ids.need_pol_item_defining_literal(v2 >= hi + 1_i));
    }
    else {
        // hi < 0, so v1 <= hi forces the sign the other way, and the mirror runs
        // through the neg row: v1 >= lo gives v2 <= -lo, v1 <= hi gives
        // v2 >= -hi.
        emit_resolution(logger, ids.need_pol_item_defining_literal(v1 < hi + 1_i), ids.need_pol_item_defining_literal(v1 >= 0_i));
        emit_resolution(logger, abs_neg_le, ids.need_pol_item_defining_literal(v1 >= lo), ids.need_pol_item_defining_literal(v2 >= -lo + 1_i));
        emit_resolution(logger, abs_neg_ge, ids.need_pol_item_defining_literal(v1 < hi + 1_i), ids.need_pol_item_defining_literal(v2 < -hi));
    }

    // rest follows by RUP
}

auto gcs::innards::justify_abs_v2_ge_zero(ProofLogger & logger, IntegerVariableID v1, IntegerVariableID v2, ProofLine abs_nonneg_ge) -> void
{
    if (holds_alternative<ConstantIntegerVariableID>(v1))
        return;

    auto & ids = logger.names_and_ids_tracker();
    auto v1_ge0 = ids.need_pol_item_defining_literal(v1 >= 0_i);
    auto v2_lt0 = ids.need_pol_item_defining_literal(v2 < 0_i);
    emit_resolution(logger, v1_ge0, abs_nonneg_ge, v2_lt0);
}

auto gcs::innards::justify_abs_v2_lb(ProofLogger & logger, IntegerVariableID v1, IntegerVariableID v2, AbsLbSide side, Integer v2_lb,
    ProofLine abs_ge, const ReasonLiterals & reason) -> void
{
    if (holds_alternative<ConstantIntegerVariableID>(v1))
        return;

    auto & ids = logger.names_and_ids_tracker();
    auto v2_lt_lb = ids.need_pol_item_defining_literal(v2 < v2_lb);

    // Materialise the relevant v1 bound under the reason, then resolve
    // with the matching half-reified piece. abs_ge under v1 >= 0 gives
    // v2 - v1 >= 0; under v1 < 0 gives v2 + v1 >= 0. Resolving with the
    // v1 bound and v2 < v2_lb leaves a single side; the v1 sign branch
    // not taken is closed by RUP from the reason.
    auto v1_bound_line = (side == AbsLbSide::Nonneg)
        ? logger.emit_rup_proof_line_under_reason_then_deview(reason, WPBSum{} + -1_i * v1 <= -v2_lb, ProofLevel::Temporary)
        : logger.emit_rup_proof_line_under_reason_then_deview(reason, WPBSum{} + 1_i * v1 <= -v2_lb, ProofLevel::Temporary);

    emit_resolution(logger, abs_ge, v1_bound_line, v2_lt_lb);
}

auto gcs::innards::justify_abs_v1_le_v2_ub(
    ProofLogger & logger, IntegerVariableID v1, IntegerVariableID v2, Integer v2_ub, ProofLine abs_nonneg_ge, const ReasonLiterals & reason) -> void
{
    if (holds_alternative<ConstantIntegerVariableID>(v1))
        return;

    auto & ids = logger.names_and_ids_tracker();
    auto v1_ge_bound_plus_1 = ids.need_pol_item_defining_literal(v1 > v2_ub);
    auto v2_upper = logger.emit_rup_proof_line_under_reason_then_deview(reason, WPBSum{} + 1_i * v2 <= v2_ub, ProofLevel::Temporary);
    emit_resolution(logger, abs_nonneg_ge, v2_upper, v1_ge_bound_plus_1);

    auto v1_lt0 = ids.need_pol_item_defining_literal(v1 < 0_i);
    emit_resolution(logger, v1_ge_bound_plus_1, v1_lt0);
}

auto gcs::innards::justify_abs_v1_ge_neg_v2_ub(
    ProofLogger & logger, IntegerVariableID v1, IntegerVariableID v2, Integer v2_ub, ProofLine abs_neg_ge, const ReasonLiterals & reason) -> void
{
    if (holds_alternative<ConstantIntegerVariableID>(v1))
        return;

    auto & ids = logger.names_and_ids_tracker();
    auto v1_lt_neg_bound = ids.need_pol_item_defining_literal(v1 < -v2_ub);
    auto v2_upper = logger.emit_rup_proof_line_under_reason_then_deview(reason, WPBSum{} + 1_i * v2 <= v2_ub, ProofLevel::Temporary);
    emit_resolution(logger, abs_neg_ge, v2_upper, v1_lt_neg_bound);

    auto v1_ge0 = ids.need_pol_item_defining_literal(v1 >= 0_i);
    emit_resolution(logger, v1_ge0, v1_lt_neg_bound);
}

auto gcs::innards::justify_abs_v2_le_big_m(ProofLogger & logger, IntegerVariableID v1, IntegerVariableID v2, Integer v1_lb, Integer v1_ub,
    Integer big_m, ProofLine abs_nonneg_le, ProofLine abs_neg_le, const ReasonLiterals & reason) -> void
{
    if (holds_alternative<ConstantIntegerVariableID>(v1))
        return;

    auto & ids = logger.names_and_ids_tracker();
    auto v2_ge_M_plus_1 = ids.need_pol_item_defining_literal(v2 > big_m);

    // The v1 bounds are emitted in VIEW form (no deview): abs_nonneg_le /
    // abs_neg_le carry v1 in its view encoding (the OPB holds the view form
    // post-#237), so the resolution only cancels v1's terms if the operand
    // bound is in that same encoding. A deviewed (underlying-variable) bound
    // wouldn't cancel against the view-form halves, leaving v1 terms behind
    // and stranding the closing RUP. Unlike the other consequence-bound
    // helpers -- whose final inference is on the *other* variable, so the
    // auto-RUP closes via the view link regardless -- this bound is on v2 and
    // needs both sign halves to resolve to a clean v2 bound.
    auto v1_upper = logger.emit_rup_proof_line_under_reason(reason, WPBSum{} + 1_i * v1 <= v1_ub, ProofLevel::Temporary);
    emit_resolution(logger, abs_nonneg_le, v1_upper, v2_ge_M_plus_1);

    auto v1_lower = logger.emit_rup_proof_line_under_reason(reason, WPBSum{} + -1_i * v1 <= -v1_lb, ProofLevel::Temporary);
    emit_resolution(logger, abs_neg_le, v1_lower, v2_ge_M_plus_1);
}
