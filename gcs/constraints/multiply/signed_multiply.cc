#include <gcs/constraints/innards/product_bounds.hh>
#include <gcs/constraints/innards/product_justify.hh>
#include <gcs/constraints/multiply/hints.hh>
#include <gcs/constraints/multiply/signed_multiply.hh>
#include <gcs/exception.hh>
#include <gcs/innards/inference_tracker.hh>
#include <gcs/innards/proofs/names_and_ids_tracker.hh>
#include <gcs/innards/proofs/pol_builder.hh>
#include <gcs/innards/proofs/proof_logger.hh>
#include <gcs/innards/proofs/proof_model.hh>

#include <optional>
#include <tuple>
#include <utility>
#include <vector>

using namespace gcs;
using namespace gcs::innards;
using namespace gcs::innards::signed_multiply;

using std::nullopt;
using std::optional;
using std::string;
using std::vector;

namespace pj = gcs::innards::product_justify;

auto gcs::innards::signed_multiply::make_data(ProofModel * const optional_model, const State & initial_state, const ConstraintID & constraint_id,
    const string & label, SimpleIntegerVariableID x, SimpleIntegerVariableID y, SimpleIntegerVariableID z, optional<long long> link) -> Data
{
    Data data;
    data.x = x;
    data.y = y;
    data.z = z;
    std::tie(data.x_init_lo, data.x_init_hi) = initial_state.bounds(x);
    std::tie(data.y_init_lo, data.y_init_hi) = initial_state.bounds(y);

    if (optional_model) {
        // cake_pb_cp's multiplication encoding: a magnitude channel per
        // operand slot (axis 0 -> "X", 1 -> "Y", a fresh proof-only magnitude
        // each, even for a repeated operand), the bit-product grid, the
        // result channel pinning |z| to the grid sum, and the six sign
        // clauses (all entailed for non-negative operands, but cake always
        // emits them, so the labels resolve in the chain).
        product_enc::LinkNaming naming{link};
        data.chan_x = product_enc::emit_magnitude_channel(*optional_model, initial_state, constraint_id, label, "MultiplyBC", x, 0, "X", naming);
        data.chan_y = product_enc::emit_magnitude_channel(*optional_model, initial_state, constraint_id, label, "MultiplyBC", y, 1, "Y", naming);
        data.grid = product_enc::emit_bit_product_grid(*optional_model, constraint_id, label, data.chan_x->mag, data.chan_y->mag, naming);
        data.zchan = product_enc::emit_result_channel(*optional_model, label, "MultiplyBC", z, data.grid, naming);
        product_enc::emit_sign_clauses(*optional_model, label, "MultiplyBC", x, y, z, naming);
    }

    return data;
}

namespace
{
    // The signed bound lines a pattern's magnitude channels draw from: the
    // operand's lower and upper bound as proof lines, either from the reason
    // (current domains) or with one side an assumed excluded-range atom (the
    // factor-bound refutations).
    struct BoundSources
    {
        pj::ConditionalBound lower;
        pj::ConditionalBound upper;
    };

    // Channel a pattern's magnitude lower and upper bounds for one operand
    // slot: on the negative branch the sources swap and the directions flip.
    struct ChannelledPair
    {
        pj::ConditionalBound mag_lb;
        pj::ConditionalBound mag_ub;
    };

    auto channel_pair(ProofLogger & logger, const BoundSources & src, SimpleIntegerVariableID v, const product_enc::MagnitudeChannel & chan,
        bool negative_branch, bool strengthen_lb) -> ChannelledPair
    {
        auto mag_lb = pj::channel_bound_to_magnitude(logger, negative_branch ? src.upper : src.lower, v, chan, negative_branch, strengthen_lb);
        auto mag_ub = pj::channel_bound_to_magnitude(logger, negative_branch ? src.lower : src.upper, v, chan, negative_branch);
        return {mag_lb, mag_ub};
    }

    // Justify both bounds on z (thesis Justification Procedure 7.5): derive
    // each live sign case's product bound through the grid, channel to z, and
    // resolve the cases; then restate the two bound atoms, which the caller's
    // infer_all applies.
    auto justify_z_bounds(ProofLogger & logger, const ReasonLiterals & reason, Data & d, Integer x_lo, Integer x_hi, Integer y_lo, Integer y_hi,
        Integer prod_lo, Integer prod_hi) -> void
    {
        auto dims = vector<pj::SignCaseDimension>{{d.x >= 0_i, d.x < 0_i}, {d.y >= 0_i, d.y < 0_i}};
        vector<optional<pj::ConditionalBound>> lower_premises(4, nullopt), upper_premises(4, nullopt);

        auto xs = BoundSources{pj::derive_operand_bound(logger, reason, d.x, true, x_lo), pj::derive_operand_bound(logger, reason, d.x, false, x_hi)};
        auto ys = BoundSources{pj::derive_operand_bound(logger, reason, d.y, true, y_lo), pj::derive_operand_bound(logger, reason, d.y, false, y_hi)};

        for (unsigned pattern = 0; pattern < 4; ++pattern) {
            bool xneg = pattern & 1u, yneg = pattern & 2u;
            if ((xneg ? x_lo >= 0_i : x_hi < 0_i) || (yneg ? y_lo >= 0_i : y_hi < 0_i))
                continue;
            bool zneg = xneg != yneg;

            auto xc = channel_pair(logger, xs, d.x, *d.chan_x, xneg, false);
            auto yc = channel_pair(logger, ys, d.y, *d.chan_y, yneg, false);
            auto glb = pj::grid_sum_lower_bound(logger, reason, d.grid, d.chan_x->mag, xc.mag_lb, yc.mag_lb);
            auto gub = pj::grid_sum_upper_bound(logger, reason, d.grid, d.chan_x->mag, d.chan_y->mag, xc.mag_ub, yc.mag_ub);
            if (! zneg) {
                lower_premises[pattern] = pj::channel_grid_bound_to_result(logger, reason, d.z, *d.zchan, glb, false, true);
                upper_premises[pattern] = pj::channel_grid_bound_to_result(logger, reason, d.z, *d.zchan, gub, false, false);
            }
            else {
                lower_premises[pattern] = pj::channel_grid_bound_to_result(logger, reason, d.z, *d.zchan, gub, true, false);
                upper_premises[pattern] = pj::channel_grid_bound_to_result(logger, reason, d.z, *d.zchan, glb, true, true);
            }
        }

        pj::conclude_by_sign_cases(logger, reason, WPBSum{} + 1_i * d.z >= prod_lo, dims, lower_premises);
        pj::conclude_by_sign_cases(logger, reason, WPBSum{} + -1_i * d.z >= -prod_hi, dims, upper_premises);
        logger.emit_rup_proof_line_under_reason(reason, WPBSum{} + 1_i * (d.z <= prod_hi) >= 1_i, ProofLevel::Current);
        logger.emit_rup_proof_line_under_reason(reason, WPBSum{} + 1_i * (d.z >= prod_lo) >= 1_i, ProofLevel::Current);
    }

    // Justify one factor bound (thesis Justification Procedures 7.6/7.7):
    // assume the refuted excluded range for the target, derive each live sign
    // case's product bound, clash it with whichever of z's actual bounds it
    // violates, and resolve the cases into the new bound on the target.
    auto justify_factor_bound(ProofLogger & logger, const ReasonLiterals & reason, Data & d, bool on_x, bool upper, Integer t, Integer target_init_lo,
        Integer target_init_hi, Integer cof_lo, Integer cof_hi, Integer z_lo, Integer z_hi) -> void
    {
        auto target = on_x ? d.x : d.y;
        auto cofactor = on_x ? d.y : d.x;
        const auto & target_chan = on_x ? *d.chan_x : *d.chan_y;
        const auto & cof_chan = on_x ? *d.chan_y : *d.chan_x;

        // The target's bounds over the refuted excluded range: the assumed
        // atom is supplied as a unit by the negated goal; the other side is
        // the target's initial-domain row.
        auto ts = upper ? BoundSources{pj::derive_assumed_operand_bound(logger, target, true, t + 1_i),
                              pj::derive_operand_bound(logger, ReasonLiterals{}, target, false, target_init_hi)}
                        : BoundSources{pj::derive_operand_bound(logger, ReasonLiterals{}, target, true, target_init_lo),
                              pj::derive_assumed_operand_bound(logger, target, false, t - 1_i)};
        auto cs = BoundSources{
            pj::derive_operand_bound(logger, reason, cofactor, true, cof_lo), pj::derive_operand_bound(logger, reason, cofactor, false, cof_hi)};
        auto z_lb = pj::derive_operand_bound(logger, reason, d.z, true, z_lo);
        auto z_ub = pj::derive_operand_bound(logger, reason, d.z, false, z_hi);

        auto excl_lo = upper ? t + 1_i : target_init_lo;
        auto excl_hi = upper ? target_init_hi : t - 1_i;

        auto dims = vector<pj::SignCaseDimension>{{target >= 0_i, target < 0_i}, {cofactor >= 0_i, cofactor < 0_i}};
        vector<optional<pj::ConditionalBound>> premises(4, nullopt);
        vector<Literal> zero_refs;
        for (unsigned pattern = 0; pattern < 4; ++pattern) {
            bool tneg = pattern & 1u, cneg = pattern & 2u;
            if (tneg ? (excl_lo >= 0_i || target_init_lo >= 0_i) : (excl_hi < 0_i || target_init_hi < 0_i))
                continue;
            if (cneg ? cof_lo >= 0_i : cof_hi < 0_i)
                continue;
            bool zneg = tneg != cneg;

            // A spanning cofactor's magnitude lower bound must be lifted to
            // one under [cofactor != 0]; the zero case is refuted through the
            // grid against z's nonzero range.
            bool strengthen = cneg ? -cof_hi < 1_i : cof_lo < 1_i;
            if (strengthen && zero_refs.empty())
                zero_refs.emplace_back(cofactor != 0_i);

            auto tc = channel_pair(logger, ts, target, target_chan, tneg, false);
            auto cc = channel_pair(logger, cs, cofactor, cof_chan, cneg, strengthen);
            auto glb = on_x ? pj::grid_sum_lower_bound(logger, reason, d.grid, d.chan_x->mag, tc.mag_lb, cc.mag_lb)
                            : pj::grid_sum_lower_bound(logger, reason, d.grid, d.chan_x->mag, cc.mag_lb, tc.mag_lb);
            auto gub = on_x ? pj::grid_sum_upper_bound(logger, reason, d.grid, d.chan_x->mag, d.chan_y->mag, tc.mag_ub, cc.mag_ub)
                            : pj::grid_sum_upper_bound(logger, reason, d.grid, d.chan_x->mag, d.chan_y->mag, cc.mag_ub, tc.mag_ub);
            auto z_case_lower = zneg ? pj::channel_grid_bound_to_result(logger, reason, d.z, *d.zchan, gub, true, false)
                                     : pj::channel_grid_bound_to_result(logger, reason, d.z, *d.zchan, glb, false, true);
            auto z_case_upper = zneg ? pj::channel_grid_bound_to_result(logger, reason, d.z, *d.zchan, glb, true, true)
                                     : pj::channel_grid_bound_to_result(logger, reason, d.z, *d.zchan, gub, false, false);

            optional<ProofLine> clash;
            HalfReifyOnConjunctionOf clash_cases;
            if (z_case_lower.rhs > z_hi) {
                PolBuilder builder;
                builder.add(z_case_lower.line).add(z_ub.line).saturate();
                clash = builder.emit(logger, ProofLevel::Temporary);
                clash_cases = z_case_lower.cases;
            }
            else if (-z_case_upper.rhs < z_lo) {
                PolBuilder builder;
                builder.add(z_case_upper.line).add(z_lb.line).saturate();
                clash = builder.emit(logger, ProofLevel::Temporary);
                clash_cases = z_case_upper.cases;
            }
            if (! clash)
                throw UnexpectedException{"factor bound case does not refute"};
            premises[pattern] = pj::ConditionalBound{WPBSum{}, 1_i, clash_cases, *clash};
        }

        auto conclusion = upper ? WPBSum{} + -1_i * target >= -t : WPBSum{} + 1_i * target >= t;
        pj::conclude_by_sign_cases(logger, reason, conclusion, dims, premises, zero_refs);
        logger.emit_rup_proof_line_under_reason(reason, WPBSum{} + 1_i * (upper ? target <= t : target >= t) >= 1_i, ProofLevel::Current);
    }

    // Filter one factor from the cofactor's and z's bounds, mirroring the
    // JaCoP case breakdown in quotient_filter.
    template <typename Tracker_>
    auto filter_factor(Data & d, bool on_x, const State & state, Tracker_ & inference, ProofLogger * const logger, const ConstraintID & owner) -> void
    {
        auto target = on_x ? d.x : d.y;
        auto cofactor = on_x ? d.y : d.x;
        auto [cof_lo, cof_hi] = state.bounds(cofactor);
        auto [z_lo, z_hi] = state.bounds(d.z);
        auto [t_lo, t_hi] = state.bounds(target);
        auto target_init_lo = on_x ? d.x_init_lo : d.y_init_lo;
        auto target_init_hi = on_x ? d.x_init_hi : d.y_init_hi;

        auto qf = quotient_filter(cof_lo, cof_hi, z_lo, z_hi);
        using Kind = QuotientFilter::Kind;
        switch (qf.kind) {
        case Kind::NoFilter: return;
        case Kind::EmptyBecauseYZero:
            // cofactor is fixed to zero but z excludes zero: no target value works
            inference.contradiction(logger, JustifyUsingRUP{hints::Multiply{owner}}, ExplicitReason{ReasonLiterals{cofactor == 0_i, d.z != 0_i}});
            return;
        case Kind::Bounds: {
            auto reason = ReasonLiterals{d.z >= z_lo, d.z <= z_hi, cofactor >= cof_lo, cofactor <= cof_hi};
            if (qf.hi < t_hi) {
                auto justf = [&, t = qf.hi](const ReasonLiterals & materialised) {
                    justify_factor_bound(*logger, materialised, d, on_x, true, t, target_init_lo, target_init_hi, cof_lo, cof_hi, z_lo, z_hi);
                };
                inference.infer(logger, target < qf.hi + 1_i, JustifyExplicitly{justf, ThenRUP::No, hints::Multiply{owner}}, ExplicitReason{reason});
            }
            if (qf.lo > t_lo) {
                auto justf = [&, t = qf.lo](const ReasonLiterals & materialised) {
                    justify_factor_bound(*logger, materialised, d, on_x, false, t, target_init_lo, target_init_hi, cof_lo, cof_hi, z_lo, z_hi);
                };
                inference.infer(logger, target >= qf.lo, JustifyExplicitly{justf, ThenRUP::No, hints::Multiply{owner}}, ExplicitReason{reason});
            }
            return;
        }
        }
    }
}

auto gcs::innards::signed_multiply::propagate(Data & d, const State & state, auto & inference, ProofLogger * const logger, const ConstraintID & owner)
    -> void
{
    auto [x_lo, x_hi] = state.bounds(d.x);
    auto [y_lo, y_hi] = state.bounds(d.y);
    auto [prod_lo, prod_hi] = product_bounds(x_lo, x_hi, y_lo, y_hi);

    auto justf = [&](const ReasonLiterals & reason) { justify_z_bounds(*logger, reason, d, x_lo, x_hi, y_lo, y_hi, prod_lo, prod_hi); };
    inference.infer_all(logger, {d.z <= prod_hi, d.z >= prod_lo}, JustifyExplicitly{justf, ThenRUP::No, hints::Multiply{owner}},
        ReasonLiterals{d.x >= x_lo, d.x <= x_hi, d.y >= y_lo, d.y <= y_hi});

    filter_factor(d, true, state, inference, logger, owner);
    filter_factor(d, false, state, inference, logger, owner);
}

template auto gcs::innards::signed_multiply::propagate(Data &, const State &, SimpleInferenceTracker &, ProofLogger * const, const ConstraintID &)
    -> void;
template auto gcs::innards::signed_multiply::propagate(
    Data &, const State &, EagerProofLoggingInferenceTracker &, ProofLogger * const, const ConstraintID &) -> void;
