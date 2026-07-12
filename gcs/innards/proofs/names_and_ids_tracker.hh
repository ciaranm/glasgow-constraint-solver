#ifndef GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_PROOFS_PROOF_VARIABLE_CONSTRAINTS_TRACKER_HH
#define GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_PROOFS_PROOF_VARIABLE_CONSTRAINTS_TRACKER_HH

#include <gcs/constraint_id.hh>
#include <gcs/innards/proofs/names_and_ids_tracker-fwd.hh>
#include <gcs/innards/proofs/proof_logger-fwd.hh>
#include <gcs/innards/proofs/proof_model-fwd.hh>
#include <gcs/innards/proofs/proof_only_variables-fwd.hh>
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
#include <vector>
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

        // Allocate the XLiteral backing a flag, registering `verbose_name` (and
        // its negation) as the PB-file rendering. Shared by create_proof_flag
        // (which passes the `f[index][stem]` form) and make_proof_flag_named
        // (which passes a fully-formed two-level name verbatim).
        [[nodiscard]] auto allocate_flag_xliteral(ProofFlag flag, const std::string & verbose_name) -> XLiteral;

        // Create a flag whose PB-file variable name is `full_name` verbatim
        // (rather than wrapped in `f[index][...]`). The cake-conforming
        // create_proof_flag overloads build cake's `x[...]` (etc.) names and call this.
        [[nodiscard]] auto make_proof_flag_named(const std::string & full_name) -> ProofFlag;

        auto emit_proof_line_now_or_at_start(const std::function<auto(ProofLogger * const)->void> &) -> void;

        // The @label base for a variable's encoding definitions (bounds, ge/eq
        // atom reifications): `i[name]` for a real variable (matching cake_pb_cp,
        // including vector names like `i[scene[0]]` -- veripb's @label parser
        // accepts the nested brackets), `po[index]` for a proof-only variable
        // (which cake never sees, so the invented index-keyed base just has to be
        // unique -- proof-only names are not). Callers append `[role]`.
        [[nodiscard]] auto definitional_label_base(const SimpleOrProofOnlyIntegerVariableID & id) const -> std::string;

        // Emit containment edges between a newly-introduced literal [lo, hi] and its
        // immediate neighbours in the containment order among the existing range and eq
        // literals on `id`: minimal containers above (self -> parent) and, when self is
        // wider than one value, maximal contained literals below (child -> self).
        // Skip-level edges are left to transitivity. Each edge is a rup line.
        auto link_immediate_containment(SimpleOrProofOnlyIntegerVariableID id, Integer lo, Integer hi) -> void;

        // Define the bare range literal [lo, hi] (lo < hi): allocate its xliteral,
        // register the InRange / NotInRange condition pair, emit the red reification pair
        // against the variable's two order cuts, and add containment edges. No partition
        // maintenance and no covering; everyone other than the partition machinery goes
        // through need_invar.
        auto define_plain_invar(SimpleOrProofOnlyIntegerVariableID id, Integer lo, Integer hi) -> void;

        // Append the positive literal for the partition cell [lo, hi] to a covering
        // being built: the eq atom for a width-1 cell, the range literal otherwise.
        auto append_cell_literal_to(WPBSum & sum, SimpleOrProofOnlyIntegerVariableID id, Integer lo, Integer hi) -> void;

        // Make `p` a cell boundary in id's interval partition, splitting the cell it
        // falls strictly inside (no-op if already a boundary): define the two halves and
        // emit the split covering `cell -> left OR right`. Requires the partition to
        // exist and lb <= p <= ub+1.
        auto ensure_partition_cut(SimpleOrProofOnlyIntegerVariableID id, Integer p) -> void;

        // First interval request for `id`: set up the always-covered partition, with a
        // singleton cell for every pre-existing eq atom (earlier per-value conclusions
        // must be reachable from later coverings), define a literal for every cell, and
        // emit the at-least-one clause over the top-level partition.
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
        auto derive_deviewed_form_for(const ProofLine & v_form_line, const SumOf<Weighted<PseudoBooleanTerm>> & lhs, bool le_half) -> void;

        /**
         * Say that we will need the diect encoding to exist for a given variable.
         */
        auto need_direct_encoding_for(SimpleOrProofOnlyIntegerVariableID, Integer) -> void;

        /**
         * Say that we will need the range ("in") literal [lo, hi] for a variable,
         * meaning `lo <= var <= hi`, and return it. Idempotent on (id, lo, hi). A
         * width-1 interval IS the eq atom: `need_invar(id, v, v)` returns the
         * direct-encoding literal `id == v`, never a separate literal.
         *
         * A range literal is reified against the variable's own two order-encoding
         * cuts, `lit <=> (var >= lo) AND NOT (var >= hi+1)`. The reification alone
         * does not keep unit propagation strong enough for later proof steps (see
         * dev_docs/range_literals_spec.md): this call also maintains the
         * always-covered partition — the request's endpoints split existing cells,
         * the requested literal gets a covering over the cells it spans, containment
         * edges link it to its immediate neighbours, and the variable's first request
         * sets up the partition. All linking is state-independent, at
         * ProofLevel::Top.
         *
         * Requires a bits-encoded variable, and currently the proof-logging phase
         * (throws UnimplementedException during model writing).
         */
        [[nodiscard]] auto need_invar(SimpleOrProofOnlyIntegerVariableID id, Integer lo, Integer hi) -> ProofLiteral;

        /**
         * Does this variable have a bits encoding? Zero-one variables default to the
         * direct-only encoding, which cannot support order cuts or range literals;
         * callers wanting range literals must fall back to per-value reasoning when
         * this is false.
         */
        [[nodiscard]] auto has_bit_representation(const SimpleOrProofOnlyIntegerVariableID &) const -> bool;

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
         * Append, to \p out, the ProofLines of the order-chain ("ladder") rung
         * clauses `[id>=u] -> [id>=u']` for every existing gevar threshold `u`
         * in the half-open range `(lo, hi]`. Chained, these carry unit
         * propagation from `[id>=hi]` down to `[id>=lo]` across non-adjacent
         * order atoms (which a hinted RUP cannot bridge through the bit
         * definitions alone). Only rungs whose ProofLine has been recorded (the
         * normal full-proof path) are appended; assertion-mode links contribute
         * nothing. Ensure the two endpoint gevars exist first (e.g. via
         * need_pol_item_defining_literal) so the chain between them is present.
         */
        auto chain_lines_between(const SimpleOrProofOnlyIntegerVariableID & id, Integer lo, Integer hi, std::vector<ProofLine> & out) const -> void;

        /**
         * Set things up internally as if the specified variable was a real
         * variable, so that proof_name() etc will work with it.
         */
        auto create_literals_for_introduced_variable_value(SimpleIntegerVariableID, Integer, const std::string &) -> void;

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
         * Return a string form of the exact literals specifying a bit assignment for var == val, an alternative way to witness solutions.
         */
        [[nodiscard]] auto bit_assignment_string_for(const SimpleOrProofOnlyIntegerVariableID & var, const Integer & value) const -> std::string;

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
        auto each_bit(const SimpleOrProofOnlyIntegerVariableID &) -> std::generator<std::pair<Integer, XLiteral>>;

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
        auto track_eqvar(SimpleIntegerVariableID, Integer, const std::pair<std::variant<ProofLine, XLiteral>, std::variant<ProofLine, XLiteral>> &)
            -> void;

        /**
         * Track that a given greater-or-equal variable exists, and has a string name
         * and associated defining constraints.
         */
        auto track_gevar(SimpleIntegerVariableID, Integer, const std::pair<std::variant<ProofLine, XLiteral>, std::variant<ProofLine, XLiteral>> &)
            -> void;

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
         * The bounds recorded by track_bounds. For a model variable these are its
         * initial-domain bounds, letting a constraint's s_expr recover
         * domain-derived data (e.g. Regular's regex alphabet) at scp-writing
         * time, when no State is in reach.
         */
        [[nodiscard]] auto tracked_bounds(const SimpleOrProofOnlyIntegerVariableID & id) const -> std::pair<Integer, Integer>;

        /**
         * Note that this variable's [lo, hi] bounds are not a trivial consequence of
         * the OPB (cake emits no bound line for it, and its bounds are only entailed
         * through conditional channels), so need_gevar must not pin its boundary order
         * literals as top-of-proof RUP lines. The owning constraint is responsible for
         * establishing the bounds explicitly. Used for ArgSort's cake-named free-bit-sum
         * sorted-value variables.
         */
        auto note_bounds_not_trivially_derivable(const SimpleOrProofOnlyIntegerVariableID & id) -> void;

        /**
         * Note that this variable's order-encoding (ge) atom definitions carry @i[..][ge]
         * labels that a cake_pb_cp OPB does not create (it reifies each atom per value
         * under its own @c[peq..] labels). need_gevar then recovers those labels
         * in-proof: when it creates such a gevar it queues an `ia` (implies-add) line
         * re-declaring each half's reification under our @i label at proof start, checked
         * implied against whatever reifies the atom in the OPB (our own @i line in
         * workflow 1, cake's @c[peq..] in workflow 2). The order-chain `pol`s then resolve
         * against the recovered labels either way. Used for ArgSort's permutation
         * variables, whose eq atoms are OPB constraint terms/guards (matching cake) and so
         * are forced model-time under @i labels.
         */
        auto note_recover_atom_labels_in_proof(const SimpleOrProofOnlyIntegerVariableID & id) -> void;

        /**
         * Create a proof flag with a new identifier, named `f[index][stem]`.
         */
        [[nodiscard]] auto create_proof_flag(const std::string & stem) -> ProofFlag;

        /**
         * Create a position-indexed flag named `x[id][i1_i2..][annotation?]`,
         * conforming to cake_pb_cp's naming for verified encodings (workflow 2)
         * rather than the solver's default `f[index][stem]`.
         *
         * This mirrors cake's `Indices (num list) (annotation option)` flag
         * constructor (cp_to_ilpScript.sml `format_flag`): the indices are the
         * array positions the auxiliary ranges over, joined by `_`, and the
         * optional annotation is appended in its own brackets. So an
         * all_different pair selector is `create_proof_flag(id, {i, j})` ->
         * `x[id][i_j]`, and a count per-position flag is
         * `create_proof_flag(id, {i}, "eq")` -> `x[id][i][eq]`.
         *
         * cake's prefix encodes what the auxiliary is indexed by, not whether it
         * is reified: `x` = array positions (this method), `b` = a scalar flag
         * with only an annotation (`Flag`), `v` = values (`Values`). The `b` / `v`
         * families get their own entry points when their first consumers land.
         * Because VeriPB binds variables by name, a flag the solver's proof shares
         * with cake's re-derived OPB must be defined under cake's name. See #354.
         */
        [[nodiscard]] auto create_proof_flag(const ConstraintID & id, const std::vector<long long> & indices,
            const std::optional<std::string> & annotation = std::nullopt) -> ProofFlag;

        /**
         * Create a scalar flag named `b[id][annotation]`, conforming to
         * cake_pb_cp's naming for verified encodings (workflow 2). This mirrors
         * cake's `Flag annotation` constructor (cp_to_ilpScript.sml `format_flag`):
         * a per-constraint auxiliary carrying only an annotation, with no index
         * list -- in contrast to the position-indexed `x[id][...]` overload above.
         * not_equals' single selector is `create_proof_flag(id, "ne")` ->
         * `b[id][ne]`. See #354 for the `x` / `b` / `v` family split.
         */
        [[nodiscard]] auto create_proof_flag(const ConstraintID & id, const std::string & annotation) -> ProofFlag;

        /**
         * Create a value-indexed flag named `v[id][v1_v2..][annotation?]`,
         * conforming to cake_pb_cp's `Values` flag constructor
         * (cp_to_ilpScript.sml `format_flag`). The list holds domain values
         * (joined by '_'), in contrast to the array positions of the `x[...]`
         * overload above. nvalue's per-value occurrence flag is
         * `create_proof_flag_values(id, {v})` -> `v[id][v]`. A distinct name (not
         * an overload of create_proof_flag) because the value-list signature
         * would otherwise be indistinguishable from the `x[...]` one. Negative
         * values render as `-N`, matching cake (and the solver's eq/ge literals,
         * e.g. `i[X][eq-N]`); '-' is legal in both VeriPB variable names and
         * @labels (VeriPB-dev #191). See #354.
         */
        [[nodiscard]] auto create_proof_flag_values(const ConstraintID & id, const std::vector<long long> & values,
            const std::optional<std::string> & annotation = std::nullopt) -> ProofFlag;

        /**
         * Create a flag named `n[k][atom]`, conforming to cake_pb_cp's rendering
         * of a reified atom over a CONSTANT operand (cp_encScript.sml format_var
         * for `Ge`/`Eq` over a constant): e.g. `n[3][ge0]`, `n[-2][eq0]`. cake
         * reifies every operand's atoms uniformly, so a constant slot's atoms
         * exist by name, pinned to their truth values; the pin rows are the
         * ProofModel's job (cake_constant_atoms). See issue #483.
         */
        [[nodiscard]] auto create_proof_flag_for_constant(Integer k, const std::string & atom) -> ProofFlag;

        /**
         * Reify a PB constraint on a conjunction of ProofFlags or ProofLiterals
         */
        [[nodiscard]] auto reify(const WPBSumLE &, const HalfReifyOnConjunctionOf &) -> WPBSumLE;

        /*
         * Allocate an XLiteral with the given semantic meaning.
         */
        [[nodiscard]] auto allocate_xliteral_meaning(SimpleOrProofOnlyIntegerVariableID id, const EqualsOrGreaterEqual & op, Integer value)
            -> XLiteral;

        /**
         * Allocate an XLiteral meaning `lo <= id <= hi`.
         */
        [[nodiscard]] auto allocate_xliteral_meaning(SimpleOrProofOnlyIntegerVariableID id, Integer lo, Integer hi) -> XLiteral;

        /**
         * Allocate an XLiteral with the given semantic meaning.
         */
        [[nodiscard]] auto allocate_xliteral_meaning(ProofFlag flag) -> XLiteral;

        /**
         * Allocate an XLiteral with the given semantic meaning.
         */
        [[nodiscard]] auto allocate_xliteral_meaning_negative_bit_of(
            SimpleOrProofOnlyIntegerVariableID flag, Integer power, const std::optional<std::string> & name_override = std::nullopt) -> XLiteral;

        /**
         * Allocate an XLiteral with the given semantic meaning.
         */
        [[nodiscard]] auto allocate_xliteral_meaning_bit_of(
            SimpleOrProofOnlyIntegerVariableID flag, Integer power, const std::optional<std::string> & name_override = std::nullopt) -> XLiteral;

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
         * Get the s-expr *term* for a literal: s_expr_name_of() parsed into an
         * SExpr (a bare atom like `_1` or `1`, or a list for a view literal).
         * The literal-list constraints (and / or / parity) write their inputs
         * with this. Prefer it over `parse_s_expr(s_expr_name_of(...))`.
         */
        [[nodiscard]] auto s_expr_term_of(Literal lit) const -> SExpr;

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
