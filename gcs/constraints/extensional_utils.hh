#ifndef GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_CONSTRAINTS_EXTENSIONAL_UTILS_HH
#define GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_CONSTRAINTS_EXTENSIONAL_UTILS_HH

#include <gcs/extensional.hh>
#include <gcs/innards/inference_tracker-fwd.hh>
#include <gcs/innards/justification.hh>
#include <gcs/innards/proofs/proof_logger-fwd.hh>
#include <gcs/innards/propagators-fwd.hh>
#include <gcs/innards/reason.hh>
#include <gcs/innards/state-fwd.hh>
#include <gcs/integer.hh>
#include <gcs/variable_id.hh>

#include <cstdint>
#include <limits>
#include <memory>
#include <optional>
#include <utility>
#include <vector>

namespace gcs::innards
{
    /**
     * \brief Cached "residual supports" for gcs::innards::propagate_extensional().
     *
     * For each (variable position, value) the last tuple found to support it. On
     * the next call, if that tuple is still selectable and still matches, the value
     * is known supported in O(1) without re-scanning the table. Non-backtrackable:
     * a stale residue is simply re-sought, and a residue never becomes unsound
     * across backtrack (a relaxed domain can only make more tuples selectable).
     * Indexed [var position][value - base]; \c base and the sizes are captured from
     * the first propagate() call, which happens at the root, so they cover every
     * value the variable can hold during search.
     *
     * \ingroup Innards
     */
    struct ExtensionalResidues
    {
        static constexpr std::uint32_t none = std::numeric_limits<std::uint32_t>::max();
        std::vector<std::vector<std::uint32_t>> support;
        std::vector<long long> base;
        bool initialised = false;
    };

    /**
     * \brief Data for gcs::innards::propagate_extensional().
     *
     * \ingroup Innards
     */
    struct ExtensionalData
    {
        /**
         * Always a variable this constraint allocated itself, so it is concrete:
         * naming it as such lets State's SimpleIntegerVariableID overloads skip
         * the IntegerVariableID variant visit and the view arithmetic. Pass 2's
         * residue fast path asks in_domain() about it once per (variable, value)
         * examined, which is millions of reads on a table of any size.
         */
        SimpleIntegerVariableID selector;
        std::vector<IntegerVariableID> vars;
        ExtensionalTuples tuples;
        std::shared_ptr<ExtensionalResidues> residues = std::make_shared<ExtensionalResidues>();

        /**
         * The reason for every inference this table makes, built once here rather
         * than by calling generic_reason(vars) at each inference site.
         *
         * Sound to hoist because the scope is fixed and Reason is declarative: it
         * captures the variables and defers reading their domains to
         * materialise(). The factories take their scope by value, so a per-site
         * call copies the whole scope vector into a fresh shared_ptr on every
         * inference -- and does it even with proofs off, where the reason is
         * never materialised at all.
         */
        Reason reason;

        ExtensionalData(SimpleIntegerVariableID selector, std::vector<IntegerVariableID> vars, ExtensionalTuples tuples);
    };

    /**
     * \brief Propagator for extensional constraints.
     *
     * This function performs propagation for the Table constraint, but also for
     * various other constraints that end up producing something table-like.
     *
     * The optional \c hint is the typed assertion hint carried on the
     * (RUP-derivable) prunings and contradictions: a constraint that owns its
     * propagation -- Table, the GAC linear encoding -- passes its own hint so the
     * assertions name it; a caller with no single owning constraint (e.g. the
     * AutoTable presolver, installed unnamed) omits it and the default \c NoHint
     * keeps the wire empty. Carried here rather than inside ExtensionalData since
     * it is a proof-only concern, orthogonal to the table data.
     *
     * \sa Table
     */
    template <typename Hint_ = NoHint>
    auto propagate_extensional(
        const ExtensionalData &, const State &, auto & inference_tracker, innards::ProofLogger * const, const Hint_ & hint = {}) -> PropagatorState;
}

#endif
