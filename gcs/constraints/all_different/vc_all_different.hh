#ifndef GLASGOW_CONSTRAINT_SOLVER_VC_ALL_DIFFERENT_HH
#define GLASGOW_CONSTRAINT_SOLVER_VC_ALL_DIFFERENT_HH

#include <gcs/constraints/all_different/encoding.hh>
#include <gcs/innards/inference_tracker-fwd.hh>
#include <gcs/innards/proofs/proof_logger-fwd.hh>
#include <gcs/innards/proofs/proof_only_variables.hh>
#include <gcs/innards/reason.hh>
#include <gcs/innards/state.hh>
#include <gcs/variable_id.hh>
#include <optional>
#include <utility>
#include <vector>

namespace gcs
{
    namespace innards
    {
        // The not-yet-assigned variables tracked as backtrackable constraint state by
        // the non-GAC all_different propagator (and circuit, which shares it). Order is
        // not significant: the propagators may permute it (swap-and-pop erase), so it is
        // a flat contiguous container rather than a list, to keep the per-search-node
        // backtracking copy of the constraint state cheap (one allocation + memcpy, or
        // none at all, instead of a heap node per element).
        using NonGacAllDifferentUnassigned = std::vector<IntegerVariableID>;

        // single_value_reasons, when non-null, is a constraint-owned (not backtracked)
        // table of prebuilt "v == its single value" reasons, indexed by the variable's
        // SimpleIntegerVariableID index minus reason_base, so the hot loops hand back a
        // reference instead of constructing a reason. Variables with no entry (views /
        // constants, or an out-of-range index) fall back to building the reason inline.
        [[nodiscard]] auto propagate_non_gac_alldifferent(const ConstraintStateHandle & unassigned_handle, const State & state,
            auto & inference_tracker, ProofLogger * const logger, const ConstraintID & owner,
            const std::vector<Reason> * single_value_reasons = nullptr, unsigned long long reason_base = 0) -> bool;
    }

}
#endif // GLASGOW_CONSTRAINT_SOLVER_VC_ALL_DIFFERENT_HH
