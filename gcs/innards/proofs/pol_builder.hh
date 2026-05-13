#ifndef GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_INNARDS_PROOFS_POL_BUILDER_HH
#define GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_INNARDS_PROOFS_POL_BUILDER_HH

#include <gcs/innards/proofs/names_and_ids_tracker-fwd.hh>
#include <gcs/innards/proofs/proof_line.hh>
#include <gcs/innards/proofs/proof_logger-fwd.hh>
#include <gcs/integer.hh>
#include <gcs/variable_condition.hh>

#include <sstream>
#include <string>

namespace gcs::innards
{
    struct XLiteral;

    /**
     * \brief Reverse-polish-notation accumulator for VeriPB `pol` proof lines.
     *
     * VeriPB's `pol` rule combines existing constraint lines via stack operations:
     * push a constraint (by line number, optionally weighted), add (`+`), saturate
     * (`s`), divide (`d`), and so on. Hand-written `stringstream pol; pol << "pol "
     * << L1 << " " << L2 << " +";` chains are repetitive and easy to get subtly
     * wrong (a missing space, a stray `1 *`, a wrongly-placed `+`).
     *
     * `PolBuilder` builds up such a line atom-by-atom. Each `add(...)` pushes one
     * term (and, after the first push, automatically inserts the `+` to combine
     * it with the running stack top). Stack-top modifiers (`saturate`,
     * `multiply_by`, `divide_by`) cover the patterns that the codebase's two
     * private `PLine` helpers (in `mult_bc.cc` and `circuit_scc.cc`) had to
     * reinvent.
     *
     * Saturation: call `saturate()` once at the end (or wherever in the build
     * is semantically right) rather than after each `add(...)`. The codebase's
     * existing running-saturate sites all sum clause-shaped reified lines
     * where saturate-every-step, saturate-once, and don't-saturate yield
     * equivalent reasoning; an `add_and_saturate(...)` convenience is
     * deliberately not provided. Saturating *before* combining (`add(L);
     * saturate(); add(L); saturate();`) is almost always a bug — the running
     * stack-top gets saturated standalone, which is rarely what you want.
     *
     * Usage:
     * \code
     * PolBuilder b;
     * b.add(C_t_line);
     * for (auto & [k_active_line, k_height] : contributors)
     *     b.add(k_active_line, k_height);
     * b.emit(*logger, ProofLevel::Temporary);
     * \endcode
     *
     * The builder is reusable: after `emit(...)` it is cleared automatically.
     * Call `clear()` to reuse without emitting, or just construct a new builder.
     * `str()` is non-mutating and may be called multiple times; it returns the
     * full `"pol ... ;"` text for the line as it stands.
     *
     * Coefficient handling: passing `coeff == 1_i` elides the `1 *` (matching
     * the codebase's existing convention for stable proof-file output).
     * Passing `coeff == 0_i` is rejected with an exception, since a zero
     * coefficient is almost always a caller bug.
     *
     * Not thread-safe; use one builder per emit.
     *
     * \ingroup Innards
     */
    class PolBuilder
    {
    private:
        std::stringstream _s;
        bool _empty;

        auto separator_if_not_first() -> void;

    public:
        PolBuilder();
        ~PolBuilder();

        PolBuilder(const PolBuilder &) = delete;
        auto operator=(const PolBuilder &) -> PolBuilder & = delete;

        PolBuilder(PolBuilder &&) noexcept;
        auto operator=(PolBuilder &&) noexcept -> PolBuilder &;

        /**
         * Push a constraint line (coefficient 1).
         */
        auto add(ProofLine line) -> PolBuilder &;

        /**
         * Push a constraint line weighted by `coeff` (i.e. `<line> <coeff> *`).
         * `coeff == 1_i` is the same as `add(line)` with no `1 *`.
         * `coeff == 0_i` throws.
         */
        auto add(ProofLine line, Integer coeff) -> PolBuilder &;

        /**
         * Push a raw PB literal (coefficient 1), resolved to its file-format
         * string via the tracker.
         */
        auto add(const XLiteral & lit, const NamesAndIDsTracker & tracker) -> PolBuilder &;

        /**
         * Push a raw PB literal weighted by `coeff`. `coeff == 1_i` elides the
         * `1 *`; `coeff == 0_i` throws.
         */
        auto add(const XLiteral & lit, Integer coeff, const NamesAndIDsTracker & tracker) -> PolBuilder &;

        /**
         * Push the `pol`-side defining item for a literal, dispatching on the
         * `variant<ProofLine, XLiteral>` that
         * `NamesAndIDsTracker::need_pol_item_defining_literal` returns.
         * Replaces the duplicated overloaded-visit blocks in `plus.cc`,
         * `among.cc`, `linear/justify.cc`, and friends.
         */
        auto add_for_literal(NamesAndIDsTracker & tracker, const IntegerVariableCondition & lit) -> PolBuilder &;

        /**
         * Same as `add_for_literal` but weighted by `coeff`.
         */
        auto add_for_literal(NamesAndIDsTracker & tracker, const IntegerVariableCondition & lit, Integer coeff) -> PolBuilder &;

        /**
         * Apply `s` to the stack top.
         */
        auto saturate() -> PolBuilder &;

        /**
         * Apply `<n> *` to the stack top (multiply the running result by `n`).
         */
        auto multiply_by(Integer n) -> PolBuilder &;

        /**
         * Apply `<n> d` to the stack top (divide the running result by `n`).
         */
        auto divide_by(Integer n) -> PolBuilder &;

        /**
         * Has anything been pushed?
         *
         * Callers that conditionally emit (e.g. only when the loop body
         * pushed at least one term) should guard with `if (! b.empty())`
         * before calling `emit` — calling `emit` on an empty builder
         * produces a malformed `pol ;` line.
         */
        [[nodiscard]] auto empty() const -> bool;

        /**
         * Render the accumulated expression as `"pol ... ;"`. Non-mutating;
         * may be called any number of times.
         */
        [[nodiscard]] auto str() const -> std::string;

        /**
         * Equivalent to `logger.emit_proof_line(str(), level)`, then `clear()`.
         * Returns the emitted line's number.
         */
        auto emit(ProofLogger & logger, ProofLevel level) -> ProofLine;

        /**
         * Reset to a fresh, empty builder. Cheaper than constructing anew.
         */
        auto clear() -> void;
    };
}

#endif
