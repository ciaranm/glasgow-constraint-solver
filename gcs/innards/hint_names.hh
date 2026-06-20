#ifndef GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_INNARDS_HINT_NAMES_HH
#define GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_INNARDS_HINT_NAMES_HH

#include <string_view>

namespace gcs::innards::hints
{
    /**
     * \brief The coarse, model-level assertion-hint names — the second annotation
     * field carried on an asserted inference, for vanilla-VeriPB statistics.
     *
     * One named constant per constraint family (plus the framework-level
     * categories), defined here once so the strings are not repeated across call
     * sites and the whole set is extractable from a single place. This is the
     * coarse level only; the fine, per-justification-shape discriminator (the
     * "justifier" keyword) lives decentralised on each hint's witness struct in
     * gcs::innards::hints (e.g. AllDifferentHall::justifier), reached by ADL.
     *
     * \ingroup Innards
     */
    inline constexpr std::string_view all_different = "all_different";
    inline constexpr std::string_view abs = "abs";
    inline constexpr std::string_view equals = "equals";
    inline constexpr std::string_view linear_equality = "linear_equality";
    inline constexpr std::string_view plus = "plus";

    // Framework-level annotation categories (not constraint families): emitted by
    // the proof logger / names-and-ids tracker rather than a constraint.
    inline constexpr std::string_view initial_bound = "initial_bound";
    inline constexpr std::string_view bound_link = "bound_link";
    inline constexpr std::string_view backtrack = "backtrack";
    inline constexpr std::string_view solx_block = "solx_block";
    inline constexpr std::string_view soli_improve = "soli_improve";
}

#endif
