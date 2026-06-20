#ifndef GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_INNARDS_HINT_NAMES_HH
#define GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_INNARDS_HINT_NAMES_HH

#include <string_view>

namespace gcs::innards::hints
{
    /**
     * \brief The coarse, model-level assertion-hint names — the second annotation
     * field carried on an asserted inference, for vanilla-VeriPB statistics.
     *
     * Transitional: these are the constraints that still set a coarse name without
     * a typed witness. As each migrates to the JustifyByWitness path its name moves
     * onto its witness struct (a \c static constexpr \c hint_name in
     * gcs::innards::hints), and the entry here goes away; once the last one migrates
     * this header is deleted. (all_different has already moved; the framework-level
     * categories are now inline literals at their emit sites, since they are not
     * constraints and never become witnesses.)
     *
     * \ingroup Innards
     */
    inline constexpr std::string_view abs = "abs";
    inline constexpr std::string_view equals = "equals";
    inline constexpr std::string_view linear_equality = "linear_equality";
    inline constexpr std::string_view plus = "plus";
}

#endif
