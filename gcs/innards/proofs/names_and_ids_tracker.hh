#ifndef GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_PROOFS_PROOF_VARIABLE_CONSTRAINTS_TRACKER_HH
#define GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_PROOFS_PROOF_VARIABLE_CONSTRAINTS_TRACKER_HH

#include <gcs/innards/proofs/names_and_ids_tracker-fwd.hh>
#include <gcs/innards/proofs/proof_logger-fwd.hh>
#include <gcs/innards/proofs/proof_model-fwd.hh>
#include <gcs/innards/proofs/proof_only_variables.hh>
#include <gcs/innards/proofs/pseudo_boolean.hh>
#include <gcs/innards/proofs/reification.hh>
#include <gcs/innards/reason.hh>
#include <gcs/innards/s_expr.hh>
#include <gcs/proof.hh>
#include <gcs/reification.hh>
#include <gcs/variable_condition.hh>
#include <gcs/variable_id.hh>

#include <memory>
#include <optional>
#include <string>
#include <utility>
#include <variant>
#include <version>

#ifdef __cpp_lib_generator
#include <generator>
#else
#include <__generator.hpp>
#endif

namespace gcs::innards
{
    /**
     * Represents the lowest level of a raw PB literal that appears in an OPB file
     * or proof log.
     *
     * \ingroup Innards
     */
    struct XLiteral
    {
        long long id;
        bool negated;

        [[nodiscard]] auto operator<=>(const XLiteral &) const noexcept = default;
    };

    [[nodiscard]] inline auto operator!(const XLiteral & lit) -> XLiteral
    {
        return XLiteral{lit.id, ! lit.negated};
    }

    enum class EqualsOrGreaterEqual
    {
        Equals,
        GreaterEqual
    };

    /**
     * Provides access to information about flags and variables being used in a proof.
     *
     * This is for information that is shared between a ProofModel and a ProofLogger,
     * because the lazy encoding can be introduced either in the model or inside a
     * log using extension variables.
     *
     * \ingroup Innards
     */
    class NamesAndIDsTracker
    {
    private:
        struct Imp;
        std::unique_ptr<Imp> _imp;

        [[nodiscard]] auto allocate_flag_index() -> unsigned long long;

        auto emit_proof_line_now_or_at_start(const std::function<auto(ProofLogger * const)->void> &) -> void;

        // Emit laminar containment edges between a newly-introduced literal [lo, hi] (a range
        // flag, or an eq atom passed as its Integer value) and the IMMEDIATE neighbours in the
        // containment order among existing range/eq literals on `id`: minimal range containers
        // above (self -> parent) and, when self is a range, maximal contained literals below
        // (child -> self). Skip-level edges are left to transitivity. Each edge is a rup line.
        auto link_immediate_containment(SimpleOrProofOnlyIntegerVariableID id, Integer lo, Integer hi,
            const std::variant<ProofFlag, Integer> & self_term) -> void;

        // Mint the bare range flag [lo, hi] (lo < hi): the red reification pair against the
        // variable's two order cuts, plus containment edges, registered in the range-literal
        // map. No partition maintenance and no covering — this is the building block that
        // need_invar and the partition-split path share; everyone else goes through need_invar.
        [[nodiscard]] auto mint_plain_invar(SimpleOrProofOnlyIntegerVariableID id, Integer lo, Integer hi) -> ProofFlag;

        // Append the positive literal for the partition cell [lo, hi] to a sum being built
        // (a covering or the root covering): the eq atom for a width-1 cell, the range flag
        // otherwise. The cell's literal must already exist.
        auto append_cell_literal_to(WPBSum & sum, SimpleOrProofOnlyIntegerVariableID id, Integer lo, Integer hi) -> void;

        // Make `p` a cell boundary in id's interval partition, splitting the cell it falls
        // strictly inside (no-op if already a boundary): mint the two halves and emit the
        // split covering `cell -> left OR right` at ProofLevel::Top. Requires the partition
        // to exist and lb <= p <= ub+1.
        auto ensure_partition_cut(SimpleOrProofOnlyIntegerVariableID id, Integer p) -> void;

        // First interval request for `id`: set up the always-covered partition (spec §3).
        // Boundaries are the variable's definition bounds, a singleton cell for every
        // pre-existing eq atom (per-value conclusions may already have been logged over
        // them, so coverings must be able to ground out there), and the request's two
        // cuts. Mints a literal for every cell, then emits the root covering — one clause
        // over the top-level partition, RUP from the bound axioms; the whole-variable
        // literal itself is never materialised (decided 2026-06-11).
        auto init_interval_partition(SimpleOrProofOnlyIntegerVariableID id, Integer request_lo, Integer request_hi) -> void;

    public:
        /**
         * \name Constructors, destructors, and the like.
         */
        ///@{

        explicit NamesAndIDsTracker(const ProofOptions &);
        ~NamesAndIDsTracker();

        /**
         * Must be called after all proof writing is complete to flush and
         * close any supplementary output files (e.g. the variables map).
         * Must not be called from a destructor.
         */
        auto finalise() -> void;

        auto operator=(const NamesAndIDsTracker &) -> NamesAndIDsTracker & = delete;
        NamesAndIDsTracker(const NamesAndIDsTracker &) = delete;

        NamesAndIDsTracker(NamesAndIDsTracker &&) noexcept;
        auto operator=(NamesAndIDsTracker &&) noexcept -> NamesAndIDsTracker &;

        ///@}

        /**
         * Must be called after initialisation, before anything is done using the ProofModel,
         * to direct output to the model.
         */
        auto start_writing_model(ProofModel * const) -> void;

        /**
         * Must be called after the model is finalised and before the proof logging starts,
         * to direct output to the proof.
         */
        auto switch_from_model_to_proof(ProofLogger * const) -> void;

        /**
         * Must be called after the proof header has been written, to write out any delayed
         * proof steps that were generated during model creation.
         */
        auto emit_delayed_proof_steps() -> void;

        /**
         * Say that we will need the greater-than-or-equal literal for a given variable.
         */
        auto need_gevar(SimpleOrProofOnlyIntegerVariableID id, Integer v) -> void;

        /**
         * Ensure a proof-only binary-encoded variable exists for a given view.
         *
         * Returns the `ProofOnlySimpleIntegerVariableID` representing
         * `BinEnc(view)`. On first reference to a view during model writing,
         * this allocates a fresh proof-only integer variable sized to the
         * view's visible domain, emits its bound axioms, and emits the
         * linking constraint `BinEnc(view) = s*BinEnc(view.actual_variable) + c`
         * tying it back to the underlying. Repeated calls with the same view
         * return the same id (canonicalised on the `(actual_variable,
         * negate_first, then_add)` triple).
         *
         * Throws `UnimplementedException` if called during the proof-logging
         * phase for a view that wasn't registered during model writing; this
         * case is left unimplemented until empirical failures show it needed.
         */
        [[nodiscard]] auto need_view(const ViewOfIntegerVariableID & view) -> ProofOnlySimpleIntegerVariableID;

        /**
         * Look up an already-registered view's proof-only variable, or return
         * `std::nullopt` if no entry exists. Never triggers introduction;
         * never throws. Used by `emit_inequality_to` to decide whether to
         * emit in V's bits (registered) or fall back to deviewing through
         * the underlying (not registered — only happens for views first seen
         * during proof logging, which `need_view` doesn't yet support).
         */
        [[nodiscard]] auto find_view(const ViewOfIntegerVariableID & view) const -> std::optional<ProofOnlySimpleIntegerVariableID>;

        /**
         * Record that `deviewed_line` is the deview-form of `v_form_line`.
         * Lookup is via `deviewed_line_for`.
         */
        auto register_deviewed_line(const ProofLine & v_form_line, const ProofLine & deviewed_line) -> void;

        /**
         * Return the deview-form line for `line` if one has been registered,
         * otherwise `line` itself. Non-view-using constraints always return
         * the input unchanged. Used by `PolBuilder` in deview mode.
         */
        [[nodiscard]] auto deviewed_line_for(const ProofLine & line) const -> ProofLine;

        /**
         * The (LE-half, GE-half) proof-line IDs of the bit-vector link for a
         * registered view (allocated in `need_view`). Used by the
         * deview-derivation helper.
         */
        [[nodiscard]] auto view_link_lines_for(const ProofOnlySimpleIntegerVariableID & view_proof_id) const -> std::pair<ProofLine, ProofLine>;

        /**
         * Derive and register a deview-form for the constraint at
         * `v_form_line`. Walks the WPBSum's lhs for view terms; if any are
         * found, queues a `pol` line that substitutes each `BinEnc(V)` term
         * for `s*BinEnc(X) + c` (using the appropriate link half), emits at
         * the top of the proof, and records the line in the deviewed-form
         * registry so `deviewed_line_for(v_form_line)` returns it. No-op
         * if the constraint has no view terms.
         *
         * `le_half` indicates whether the OPB-form coefficients are
         * sign-flipped from the WPBSum's `lhs` (true for the LE half of an
         * equality, or any `<=` constraint that emit_inequality_to flips to
         * a `>=`). This is needed to pick the right link half for the
         * cancellation.
         */
        auto derive_deviewed_form_for(const ProofLine & v_form_line,
            const SumOf<Weighted<PseudoBooleanTerm>> & lhs,
            bool le_half) -> void;

        /**
         * Say that we will need the diect encoding to exist for a given variable.
         */
        auto need_direct_encoding_for(SimpleOrProofOnlyIntegerVariableID, Integer) -> void;

        /**
         * Say that we will need the range ("in") literal [lo, hi] for a variable,
         * meaning `lo <= var <= hi`. Returns that literal, idempotent on (id, lo, hi)
         * after clamping [lo, hi] to the variable's definition bounds (the clamped
         * literal is the same solver fact, given the bound axioms). A width-1 interval
         * IS the eq atom: `need_invar(id, v, v)` returns the direct-encoding literal
         * `id == v`, never a separate flag (spec §2, witness W1); wider intervals
         * return a ProofFlag.
         *
         * A range literal is a "wide equality literal", defined as
         * `flag <=> (var >= lo) AND NOT (var >= hi+1)`, reified against the variable's
         * own two order-encoding cuts (need_gevar threads them into the Inv1 chain).
         * The reification alone is NOT enough for replay-completeness (P2; see
         * dev_docs/range_literals_spec.md §1 and Appendix B): this call also maintains
         * the always-covered partition invariant of spec §3 — the request's endpoints
         * split existing cells (emitting split coverings), the requested literal gets a
         * covering over the cells it spans, containment edges link it to its immediate
         * neighbours, and the variable's first request sets up the partition and emits
         * the root covering. All of that linking is state-independent and emitted at
         * ProofLevel::Top.
         *
         * Requires a bits-encoded variable. Currently only implemented during the
         * proof-logging phase; throws UnimplementedException if called during model
         * writing, until a caller needs it (see spec §9.3's open decision).
         */
        [[nodiscard]] auto need_invar(SimpleOrProofOnlyIntegerVariableID id, Integer lo, Integer hi) -> ProofLiteralOrFlag;

        /**
         * Does this variable have a bits encoding? Zero-one variables default to the
         * direct-only encoding, which cannot support order cuts or range literals;
         * callers minting range literals must fall back to per-value reasoning when
         * this is false.
         */
        [[nodiscard]] auto has_bit_representation(const SimpleOrProofOnlyIntegerVariableID &) const -> bool;

        /**
         * Resolve a propagator-supplied Reason into the conjunction of proof literals
         * it reifies on. Plain literals and flags pass through; a VariableNotInRange
         * element becomes the negated range ("in") literal, minted via need_invar
         * (with everything that entails: partition splits, coverings, containment).
         * Views, constants and direct-only-encoded variables take the per-value
         * fallback `var != v`. The part of an element's range outside the variable's
         * definition bounds is dropped: it is unit-propagation-given by the bound
         * axioms, so the reified inference stays RUP without it.
         *
         * This is THE reason-vocabulary resolution point; every proof-logging site
         * that turns a ReasonFunction's result into emitted literals must go through
         * it (spec §9.2 — missing a site no-ops silently).
         */
        [[nodiscard]] auto resolve_reason(const Reason &) -> HalfReifyOnConjunctionOf;

        /**
         * Say that we are going to need an at-least-one constraint for a
         * variable.
         */
        [[nodiscard]] auto need_constraint_saying_variable_takes_at_least_one_value(IntegerVariableID) -> ProofLine;

        /**
         * Give the proof line specifying the definition of this literal in terms of its bit
         * representation. Will emit the reification, if it does not already exist. If this
         * is a zero-one variable, returns an actual literal.
         */
        [[nodiscard]] auto need_pol_item_defining_literal(const IntegerVariableCondition &) -> std::variant<ProofLine, XLiteral>;

        /**
         * Set things up internally as if the specified variable was a real
         * variable, so that proof_name() etc will work with it.
         */
        auto create_literals_for_introduced_variable_value(
            SimpleIntegerVariableID, Integer, const std::string &) -> void;

        /**
         * Ensure that a name exists for a given variable condition.
         */
        auto need_proof_name(const VariableConditionFrom<SimpleOrProofOnlyIntegerVariableID> &) -> void;

        /**
         * Ensure that need_proof_name() has been called for everything in a given sum.
         */
        auto need_all_proof_names_in(const SumOf<Weighted<PseudoBooleanTerm>> & sum) -> void;

        /**
         * Ensure that need_proof_name() has been called for everything in a given Literals.
         */
        auto need_all_proof_names_in(const Literals &) -> void;

        /**
         * Ensure that need_proof_name() has been called for everything in a given HalfReifyOnConjunctionOf.
         */
        auto need_all_proof_names_in(const HalfReifyOnConjunctionOf &) -> void;

        /**
         * Return the string used in PB files for a given XLiteral.
         */
        [[nodiscard]] auto pb_file_string_for(const XLiteral &) const -> std::string;

        /**
         * Return the raw proof literal representing a variable condition, for writing to a model or log.
         */
        [[nodiscard]] auto xliteral_for(const VariableConditionFrom<SimpleOrProofOnlyIntegerVariableID> &) const -> const XLiteral;

        /**
         * Return a string form of a raw proof literal, for writing to a model or log.
         */
        [[nodiscard]] auto pb_file_string_for(const VariableConditionFrom<SimpleOrProofOnlyIntegerVariableID> &) const -> std::string;

        /**
         * Return the raw proof literal representing a proof flag, for writing to a model or log.
         */
        [[nodiscard]] auto xliteral_for(const ProofFlag &) const -> const XLiteral;

        /**
         * Return a string form of a proof flag, for writing to a model or log. Same as calling
         * raw_literal_as_string(raw_proof_literal(flag)).
         */
        [[nodiscard]] auto pb_file_string_for(const ProofFlag &) const -> std::string;

        /**
         * Call the supplied function for each bit making up the given variable, specifying
         * its raw PB literal and coefficient.
         */
        auto each_bit(const SimpleOrProofOnlyIntegerVariableID &)
            -> std::generator<std::pair<Integer, XLiteral>>;

        /**
         * Get the name and coefficient for the bit position in the representation of the given var.
         */
        [[nodiscard]] auto get_bit(const SimpleOrProofOnlyIntegerVariableID & var, Integer position) -> std::pair<Integer, XLiteral>;

        /**
         * Get the name and coefficient for the bit position in the representation of the given var.
         */
        [[nodiscard]] auto get_bit(const ProofBitVariable & bit) -> std::pair<Integer, XLiteral>;

        /**
         * How many bits are used to represent this variable, including the negative bit if there is one?
         */
        [[nodiscard]] auto num_bits(const SimpleOrProofOnlyIntegerVariableID & var) -> Integer;

        /**
         * If there is a negative bit for this variable, return its coefficient, otherwise
         * return zero.
         */
        [[nodiscard]] auto negative_bit_coefficient(const SimpleOrProofOnlyIntegerVariableID &) -> Integer;

        /**
         * Track that the associated literal exists, and has a string name.
         */
        auto associate_condition_with_xliteral(const VariableConditionFrom<SimpleOrProofOnlyIntegerVariableID> &, const XLiteral &) -> void;

        /**
         * Track that a given variable's bits exist.
         */
        auto track_bits(const SimpleOrProofOnlyIntegerVariableID & id, Integer negative_coeff,
            const std::vector<std::pair<Integer, XLiteral>> & bit_vars) -> void;

        /**
         * Track that a given equality variable exists, and has a string name
         * and associated defining constraints.
         */
        auto track_eqvar(SimpleIntegerVariableID, Integer,
            const std::pair<std::variant<ProofLine, XLiteral>, std::variant<ProofLine, XLiteral>> &) -> void;

        /**
         * Track that a given greater-or-equal variable exists, and has a string name
         * and associated defining constraints.
         */
        auto track_gevar(SimpleIntegerVariableID, Integer,
            const std::pair<std::variant<ProofLine, XLiteral>, std::variant<ProofLine, XLiteral>> &) -> void;

        /**
         * Track that an at-least-one constraint exists for a given variable.
         */
        auto track_variable_takes_at_least_one_value(const SimpleOrProofOnlyIntegerVariableID &, ProofLine) -> void;

        /**
         * Track that a given proof flag exists with this name.
         */
        auto track_flag(const ProofFlag &, const std::string &) -> void;

        /**
         * Track the lower and upper bounds for a given variable.
         */
        auto track_bounds(const SimpleOrProofOnlyIntegerVariableID & id, Integer, Integer) -> void;

        /**
         * Create a proof flag with a new identifier.
         */
        [[nodiscard]] auto create_proof_flag(const std::string &) -> ProofFlag;

        /**
         * Reify a PB constraint on a conjunction of ProofFlags or ProofLiterals
         */
        [[nodiscard]] auto reify(const WPBSumLE &, const HalfReifyOnConjunctionOf &) -> WPBSumLE;

        /*
         * Allocate an XLiteral with the given semantic meaning.
         */
        [[nodiscard]] auto allocate_xliteral_meaning(SimpleOrProofOnlyIntegerVariableID id, const EqualsOrGreaterEqual & op, Integer value) -> XLiteral;

        /**
         * Allocate an XLiteral with the given semantic meaning.
         */
        [[nodiscard]] auto allocate_xliteral_meaning(ProofFlag flag) -> XLiteral;

        /**
         * Allocate an XLiteral with the given semantic meaning.
         */
        [[nodiscard]] auto allocate_xliteral_meaning_negative_bit_of(SimpleOrProofOnlyIntegerVariableID flag, Integer power) -> XLiteral;

        /**
         * Allocate an XLiteral with the given semantic meaning.
         */
        [[nodiscard]] auto allocate_xliteral_meaning_bit_of(SimpleOrProofOnlyIntegerVariableID flag, Integer power) -> XLiteral;

        /**
         * Track a human-readable name for a variable.
         */
        auto track_variable_name(SimpleOrProofOnlyIntegerVariableID id, const std::string &) -> void;

        /**
         * Track a human-readable name for a variable.
         */
        auto track_variable_name(ProofFlag id, const std::string &) -> void;

        /**
         * Get the human-readable / s-expr name for a variable. Currently throws on views.
         */
        [[nodiscard]] auto s_expr_name_of(IntegerVariableID id) const -> std::string;

        /**
         * Get the human-readable / s-expr name for a literal. Currently not sure about VariableConditionFrom<IntegerVariableID>
         */
        [[nodiscard]] auto s_expr_name_of(Literal lit) const -> std::string;

        /**
         * Get the human-readable / s-expr name for a reification condition
         */
        [[nodiscard]] auto s_expr_name_of(ReificationCondition cond) const -> std::string;

        /**
         * Get the human-readable / s-expr name for a condition operator
         */
        [[nodiscard]] auto s_expr_name_of(VariableConditionOperator op) const -> std::string;

        /**
         * Render an objective variable as the final `.scp` element:
         * `(minimize <name>)` or `(maximize <name>)`, matching cake_pb_cp's
         * spelling (a view that negates its variable becomes a maximize).
         */
        [[nodiscard]] auto s_expr_render_of(IntegerVariableID id) const -> std::string;

        /**
         * Get the s-expr *term* for a variable: s_expr_name_of() parsed into an
         * SExpr, so a view like `(-_1 + 17)` becomes a list rather than an atom.
         * Prefer this over `parse_s_expr(s_expr_name_of(...))` at call sites so
         * the wrap can't be forgotten.
         */
        [[nodiscard]] auto s_expr_term_of(IntegerVariableID id) const -> SExpr;

        /**
         * Get the s-expr term for a reification condition, or nullopt when the
         * condition is unconditional (MustHold / MustNotHold). Keeps the
         * "no condition" case explicit rather than leaking the empty string that
         * the s_expr_name_of(ReificationCondition) overload returns.
         */
        [[nodiscard]] auto s_expr_term_of(ReificationCondition cond) const -> std::optional<SExpr>;

        /**
         * Get the human-readable name for a variable.
         */
        [[nodiscard]] auto name_of(SimpleOrProofOnlyIntegerVariableID id) const -> const std::string &;

        /**
         * Get the human-readable name for a variable.
         */
        [[nodiscard]] auto name_of(ProofFlag id) const -> const std::string &;
    };
}

#endif
