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

        // Prebuilt "v == its single value" reasons for the SimpleIntegerVariableIDs of
        // one scope, so the hot loops hand back a reference instead of constructing a
        // reason. Each is a deferred ExactSingleValue, which materialises to v ==
        // whatever value v is fixed to at the point of inference. Constraint-owned,
        // not backtracked: it never changes during search.
        //
        // Sized by the scope, not by the span of its variable IDs (issue #1008). A
        // table indexed directly by ID over the columns of a row-major n x n Latin
        // square holds n^3 reasons, which was 194 MB at n = 100 before any search.
        // Lookup is a binary search over the sorted indices instead, paid once per
        // newly fixed variable, and each such variable is then checked against every
        // unassigned one anyway.
        struct NonGacAllDifferentSingleValueReasons
        {
            std::vector<unsigned long long> indices; // sorted
            std::vector<Reason> reasons;             // reasons[i] is for indices[i]

            [[nodiscard]] static auto build(const std::vector<IntegerVariableID> & vars) -> NonGacAllDifferentSingleValueReasons;

            // The prebuilt reason for v, or null for a view, a constant, or a
            // variable not in the scope.
            [[nodiscard]] auto find(const IntegerVariableID & v) const -> const Reason *;
        };

        // single_value_reasons, when non-null, supplies the prebuilt "v == its single
        // value" reasons. Variables with no entry fall back to building the reason
        // inline.
        [[nodiscard]] auto propagate_non_gac_alldifferent(const ConstraintStateHandle & unassigned_handle, const State & state,
            auto & inference_tracker, ProofLogger * const logger, const ConstraintID & owner,
            const NonGacAllDifferentSingleValueReasons * single_value_reasons = nullptr) -> bool;
    }

}
#endif // GLASGOW_CONSTRAINT_SOLVER_VC_ALL_DIFFERENT_HH
