#ifndef GLASGOW_CONSTRAINT_SOLVER_GAC_ALL_DIFFERENT_HH
#define GLASGOW_CONSTRAINT_SOLVER_GAC_ALL_DIFFERENT_HH

#include <gcs/constraint.hh>
#include <gcs/constraints/all_different/encoding.hh>
#include <gcs/innards/inference_tracker-fwd.hh>
#include <gcs/innards/proofs/proof_logger.hh>
#include <gcs/innards/proofs/proof_only_variables.hh>
#include <gcs/variable_id.hh>

#include <cstdint>
#include <map>
#include <memory>
#include <optional>
#include <utility>
#include <vector>

namespace gcs
{
    namespace innards
    {
        struct GacAllDifferentScratch;

        /**
         * \brief Make the reusable working storage for propagate_gac_all_different.
         *
         * Create one per installed propagator (a `shared_ptr` captured into the
         * propagator closure works well) and pass the same object to every call:
         * the propagator clears rather than reallocates its working buffers, so
         * the hot path stops paying for dozens of allocations on every wake. The
         * type is opaque outside gac_all_different.cc.
         *
         * \ingroup Innards
         */
        [[nodiscard]] auto make_gac_all_different_scratch() -> std::shared_ptr<GacAllDifferentScratch>;

        /**
         * \brief Make all-different over \p vars, whose values are drawn from
         * \p vals, generalised arc consistent.
         *
         * If \p values_in_every_matching is given, it is set on return to one
         * entry per \p vals, true when every matching that covers all of
         * \p vars takes that value. Every value is taken when there are as many
         * values as variables. Otherwise these are the values that no
         * alternating path reaches from a value the matching leaves free. The
         * deletions made here remove only edges that no such matching uses, so
         * they leave the answer the same. Inverse's injection form reads it
         * (#1047).
         */
        auto propagate_gac_all_different(const ConstraintID & constraint_id, const std::vector<IntegerVariableID> & vars,
            const std::vector<Integer> & vals, const std::vector<Integer> & excluded, std::map<Integer, ProofLine> & value_am1_constraint_numbers,
            GacAllDifferentScratch & scratch, const State & state, auto & inference_tracker, ProofLogger * const logger,
            std::vector<uint8_t> * values_in_every_matching = nullptr) -> void;
    }

}
#endif // GLASGOW_CONSTRAINT_SOLVER_GAC_ALL_DIFFERENT_HH
