#ifndef GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_INNARDS_REASON_HH
#define GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_INNARDS_REASON_HH

#include <gcs/array_param.hh>
#include <gcs/innards/literal.hh>
#include <gcs/innards/proofs/reification.hh>
#include <gcs/innards/state-fwd.hh>
#include <gcs/variable_id.hh>

#include <gch/small_vector.hpp>

#include <functional>
#include <optional>
#include <variant>
#include <vector>

namespace gcs::innards
{
    // The materialised conjunction of facts a proof line is reified under.
    // Typical sizes are 1 (singleton_reason for reified flags) to a handful
    // (bounds_reason / generic_reason over a small set of variables). Inline
    // capacity 2 keeps the common 1- and 2-element cases off the heap. An
    // interval-shaped fact is stated as an interval: a range condition (see
    // in_range() / not_in_range()) is an ordinary condition, whose proof name
    // is the range ("in") literal.
    using ReasonLiterals = gch::small_vector<ProofLiteralOrFlag, 2>;

    // Owned / shared / borrowed handle over the variable scope a reason reasons
    // about, reusing gcs::ArrayParam (gcs/array_param.hh). "Borrowed" is the
    // unowned mode: a constraint that always reasons over the same scope passes
    // `&_vars` and allocates nothing.
    using ReasonVars = VectorArrayParam<IntegerVariableID>;

    // Escape hatch for the bespoke tail: reads state, appends to `out`.
    using LazyReasonFn = std::function<auto(const State &, ReasonLiterals & out)->void>;

    /**
     * \brief A declarative description of a reason: cheap to build, copyable,
     * and storable. The domain walk that turns it into ReasonLiterals is
     * deferred to materialise(), so building one off the perf-critical
     * (proofs-off) path costs nothing but a handle.
     */
    struct NoReason
    {
    };

    /// Reason given as already-known literals (singletons, fixed lists, eager snapshots).
    struct ExplicitReason
    {
        ReasonLiterals literals;
    };

    /// Reason recording every value in each variable's domain (bounds + holes), plus an optional extra literal.
    struct GenericReasonOver
    {
        ReasonVars vars;
        std::optional<Literal> extra;
    };

    /// Reason recording only the lower and upper bound of each variable, plus an optional extra literal.
    struct BothBoundsReasonOver
    {
        ReasonVars vars;
        std::optional<Literal> extra;
    };

    /// Reason recording that each variable in `vars` is fixed to exactly its
    /// single current value (`var == value`). Equivalent to BothBoundsReasonOver
    /// for an already-instantiated variable, but it states the equality directly
    /// and emits `extra` *first*, matching the literal order of the hand-written
    /// explicit reasons it replaces, so the proof stays byte-identical. Cheap to
    /// build off the proofs-off path: it captures the (borrowable) variable scope
    /// and defers reading the value to materialise().
    struct ExactSingleValue
    {
        ReasonVars vars;
        std::optional<Literal> extra;
    };

    /// Reason whose literals are computed by a bespoke callback reading state; `vars` records the implicated scope.
    struct LazyReasonOver
    {
        ReasonVars vars;
        LazyReasonFn fn;
    };

    // Narrowable counterparts: same payload, different tag. "Narrowable" means
    // the constraint is content with being handed tightened domains, so the
    // reason may be re-materialised lazily against whatever (narrower) state is
    // current later. In eager proof-logging mode they behave identically to
    // their non-narrowable twins (we always materialise now, against the current
    // state), so the tag is a no-op until a deferred tracker exists. Default
    // everything to non-narrowable; settling it per constraint needs a pass with
    // proof-soundness sign-off.
    struct NarrowableGenericReasonOver
    {
        ReasonVars vars;
        std::optional<Literal> extra;
    };

    struct NarrowableBothBoundsReasonOver
    {
        ReasonVars vars;
        std::optional<Literal> extra;
    };

    struct NarrowableLazyReasonOver
    {
        ReasonVars vars;
        LazyReasonFn fn;
    };

    /**
     * \brief A reason for an inference, as a declarative variant.
     *
     * Implemented as a thin wrapper over a std::variant so it can also be
     * implicitly built from a materialised ReasonLiterals (used directly as the
     * reason). Inspect with visit(); materialise() turns it into ReasonLiterals.
     */
    class Reason
    {
    public:
        using Variant = std::variant<
            NoReason, ExplicitReason,
            GenericReasonOver, BothBoundsReasonOver, ExactSingleValue, LazyReasonOver,
            NarrowableGenericReasonOver, NarrowableBothBoundsReasonOver, NarrowableLazyReasonOver>;

        Reason() :
            _variant(NoReason{})
        {
        }

        Reason(NoReason r) :
            _variant(std::move(r))
        {
        }

        Reason(ExplicitReason r) :
            _variant(std::move(r))
        {
        }

        Reason(GenericReasonOver r) :
            _variant(std::move(r))
        {
        }

        Reason(BothBoundsReasonOver r) :
            _variant(std::move(r))
        {
        }

        Reason(ExactSingleValue r) :
            _variant(std::move(r))
        {
        }

        Reason(LazyReasonOver r) :
            _variant(std::move(r))
        {
        }

        Reason(NarrowableGenericReasonOver r) :
            _variant(std::move(r))
        {
        }

        Reason(NarrowableBothBoundsReasonOver r) :
            _variant(std::move(r))
        {
        }

        Reason(NarrowableLazyReasonOver r) :
            _variant(std::move(r))
        {
        }

        /// Materialised literals used verbatim as the reason.
        Reason(ReasonLiterals literals) :
            _variant(ExplicitReason{std::move(literals)})
        {
        }

        template <typename Visitor_>
        [[nodiscard]] auto visit(Visitor_ && visitor) const -> decltype(auto)
        {
            return std::visit(std::forward<Visitor_>(visitor), _variant);
        }

    private:
        Variant _variant;
    };

    /**
     * \brief Materialise a reason into its literal conjunction against the given
     * state. This is the only place a reason walks variable domains; the
     * caller (a proof-logging inference tracker) does this once it has decided
     * it needs the literals. Stateless variants ignore `state`.
     */
    [[nodiscard]] auto materialise(const Reason & reason, const State & state) -> ReasonLiterals;

    /**
     * \brief Build a reason recording every value in each variable's domain
     * (lower bound, upper bound, and any holes). If `extra_lit` is supplied it
     * is appended too — handy for reified propagators that want the reification
     * literal in the reason alongside the variable facts.
     *
     * The domain walk is deferred to materialise(); this just captures the
     * variable scope. `state` is unused and retained only for call-site
     * compatibility while the migration is in progress.
     */
    [[nodiscard]] auto generic_reason(const State & state, const std::vector<IntegerVariableID> & vars,
        const std::optional<Literal> & extra_lit = std::nullopt) -> Reason;

    /**
     * \brief Like generic_reason but records only the lower and upper bounds of
     * each variable, omitting any holes in the domain.
     */
    [[nodiscard]] auto bounds_reason(const State & state, const std::vector<IntegerVariableID> & vars,
        const std::optional<Literal> & extra_lit = std::nullopt) -> Reason;

    [[nodiscard]] auto singleton_reason(const ProofLiteralOrFlag & lit) -> Reason;

    /**
     * \brief Eagerly materialise a reason into its literal conjunction against
     * the current state.
     *
     * For the handful of proof-only consumers that build a reason and hand it
     * straight to the ProofLogger (bypassing the inference tracker, which
     * normally does this conversion). The domain walk happens now, so call this
     * at the point the old eager `*_reason()` factory would have run. This is
     * just a convenience spelling of materialise() for those call sites.
     */
    [[nodiscard]] auto eager_reason(const Reason & reason, const State & state) -> ReasonLiterals;
}

#endif
