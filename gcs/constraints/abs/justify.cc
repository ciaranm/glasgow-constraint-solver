#include <gcs/constraints/abs/justify.hh>
#include <gcs/innards/proofs/names_and_ids_tracker.hh>
#include <gcs/innards/proofs/pol_builder.hh>

using namespace gcs;
using namespace gcs::innards;

using std::get;
using std::holds_alternative;

namespace
{
    // PB resolution: sum the operand proof lines and saturate, eliminating
    // any literals whose coefficients cancel.
    auto emit_resolution(ProofLogger & logger, ProofLine a, ProofLine b) -> void
    {
        PolBuilder{}.add(a).add(b).saturate().emit(logger, ProofLevel::Temporary);
    }

    auto emit_resolution(ProofLogger & logger, ProofLine a, ProofLine b, ProofLine c) -> void
    {
        PolBuilder{}.add(a).add(b).add(c).saturate().emit(logger, ProofLevel::Temporary);
    }
}

auto gcs::innards::justify_abs_hole(
    ProofLogger & logger,
    const ReasonFunction & reason,
    IntegerVariableID v1,
    IntegerVariableID v2,
    Integer val) -> void
{
    // (v2 == val /\ v1 >= 0) -> v1 == val
    logger.emit_rup_proof_line_under_reason(reason,
        WPBSum{} + 1_i * (v1 < 0_i) + 1_i * (v1 == val) + 1_i * (v2 != val) >= 1_i, ProofLevel::Temporary);

    // (v2 == val /\ v1 < 0) -> v1 == -val
    logger.emit_rup_proof_line_under_reason(reason,
        WPBSum{} + 1_i * (v1 >= 0_i) + 1_i * (v1 != -val) + 1_i * (v2 != val) >= 1_i, ProofLevel::Temporary);

    // rest follows by RUP
}

auto gcs::innards::justify_abs_v2_ge_zero(
    ProofLogger & logger,
    IntegerVariableID v1,
    IntegerVariableID v2,
    ProofLine abs_nonneg_ge) -> void
{
    if (holds_alternative<ConstantIntegerVariableID>(v1))
        return;

    auto & ids = logger.names_and_ids_tracker();
    auto v1_ge0 = get<ProofLine>(ids.need_pol_item_defining_literal(v1 >= 0_i));
    auto v2_lt0 = get<ProofLine>(ids.need_pol_item_defining_literal(v2 < 0_i));
    emit_resolution(logger, v1_ge0, abs_nonneg_ge, v2_lt0);
}

auto gcs::innards::justify_abs_v2_lb(
    ProofLogger & logger,
    IntegerVariableID v1,
    IntegerVariableID v2,
    AbsLbSide side,
    Integer v2_lb,
    ProofLine abs_ge,
    const ReasonFunction & reason) -> void
{
    if (holds_alternative<ConstantIntegerVariableID>(v1))
        return;

    auto & ids = logger.names_and_ids_tracker();
    auto v2_lt_lb = get<ProofLine>(ids.need_pol_item_defining_literal(v2 < v2_lb));

    // Materialise the relevant v1 bound under the reason, then resolve
    // with the matching half-reified piece. abs_ge under v1 >= 0 gives
    // v2 - v1 >= 0; under v1 < 0 gives v2 + v1 >= 0. Resolving with the
    // v1 bound and v2 < v2_lb leaves a single side; the v1 sign branch
    // not taken is closed by RUP from the reason.
    auto v1_bound_line = (side == AbsLbSide::Nonneg)
        ? logger.emit_rup_proof_line_under_reason(reason,
              WPBSum{} + -1_i * v1 <= -v2_lb, ProofLevel::Temporary)
        : logger.emit_rup_proof_line_under_reason(reason,
              WPBSum{} + 1_i * v1 <= -v2_lb, ProofLevel::Temporary);

    emit_resolution(logger, abs_ge, v1_bound_line, v2_lt_lb);
}

auto gcs::innards::justify_abs_v1_le_v2_ub(
    ProofLogger & logger,
    IntegerVariableID v1,
    IntegerVariableID v2,
    Integer v2_ub,
    ProofLine abs_nonneg_ge,
    const ReasonFunction & reason) -> void
{
    if (holds_alternative<ConstantIntegerVariableID>(v1))
        return;

    auto & ids = logger.names_and_ids_tracker();
    auto v1_ge_bound_plus_1 = get<ProofLine>(
        ids.need_pol_item_defining_literal(v1 >= v2_ub + 1_i));
    auto v2_upper = logger.emit_rup_proof_line_under_reason(reason,
        WPBSum{} + 1_i * v2 <= v2_ub, ProofLevel::Temporary);
    emit_resolution(logger, abs_nonneg_ge, v2_upper, v1_ge_bound_plus_1);

    auto v1_lt0 = get<ProofLine>(ids.need_pol_item_defining_literal(v1 < 0_i));
    emit_resolution(logger, v1_ge_bound_plus_1, v1_lt0);
}

auto gcs::innards::justify_abs_v1_ge_neg_v2_ub(
    ProofLogger & logger,
    IntegerVariableID v1,
    IntegerVariableID v2,
    Integer v2_ub,
    ProofLine abs_neg_ge,
    const ReasonFunction & reason) -> void
{
    if (holds_alternative<ConstantIntegerVariableID>(v1))
        return;

    auto & ids = logger.names_and_ids_tracker();
    auto v1_lt_neg_bound = get<ProofLine>(
        ids.need_pol_item_defining_literal(v1 < -v2_ub));
    auto v2_upper = logger.emit_rup_proof_line_under_reason(reason,
        WPBSum{} + 1_i * v2 <= v2_ub, ProofLevel::Temporary);
    emit_resolution(logger, abs_neg_ge, v2_upper, v1_lt_neg_bound);

    auto v1_ge0 = get<ProofLine>(ids.need_pol_item_defining_literal(v1 >= 0_i));
    emit_resolution(logger, v1_ge0, v1_lt_neg_bound);
}

auto gcs::innards::justify_abs_v2_le_big_m(
    ProofLogger & logger,
    IntegerVariableID v1,
    IntegerVariableID v2,
    Integer v1_lb,
    Integer v1_ub,
    Integer big_m,
    ProofLine abs_nonneg_le,
    ProofLine abs_neg_le,
    const ReasonFunction & reason) -> void
{
    if (holds_alternative<ConstantIntegerVariableID>(v1))
        return;

    auto & ids = logger.names_and_ids_tracker();
    auto v2_ge_M_plus_1 = get<ProofLine>(
        ids.need_pol_item_defining_literal(v2 >= big_m + 1_i));

    auto v1_upper = logger.emit_rup_proof_line_under_reason(reason,
        WPBSum{} + 1_i * v1 <= v1_ub, ProofLevel::Temporary);
    emit_resolution(logger, abs_nonneg_le, v1_upper, v2_ge_M_plus_1);

    auto v1_lower = logger.emit_rup_proof_line_under_reason(reason,
        WPBSum{} + -1_i * v1 <= -v1_lb, ProofLevel::Temporary);
    emit_resolution(logger, abs_neg_le, v1_lower, v2_ge_M_plus_1);
}
