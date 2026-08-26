#ifndef GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_PROOFS_PROOF_VARIABLE_CONSTRAINTS_TRACKER_HH
#define GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_PROOFS_PROOF_VARIABLE_CONSTRAINTS_TRACKER_HH

#include <gcs/constraint_id.hh>
#include <gcs/innards/proofs/constraint_proof_model_data.hh>
#include <gcs/innards/proofs/names_and_ids_tracker-fwd.hh>
#include <gcs/innards/proofs/proof_line.hh>
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

#include <functional>
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

        // Record the PB-file rendering of a freshly-allocated XLiteral (and its
        // negation, as `~name`). Every allocate_* path calls this exactly once,
        // in both naming modes, so pb_file_string_for is a plain index.
        auto store_xlit_names(const XLiteral &, std::string name) -> void;

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
         * The [lo, hi] a view's visible values span, from the underlying
         * variable's registered definition bounds. What need_view sizes a
         * view's proof-only bit vector by; exposed so the objective path can
         * first ask whether that bit vector is representable at all
         * (bits_encoding_fits) before registering the view.
         */
        [[nodiscard]] auto view_bounds(const ViewOfIntegerVariableID & view) const -> std::pair<Integer, Integer>;

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
         * The line pinning the order atom `id >= v` to the value the variable's
         * declared bounds already force, if there is one.
         *
         * need_gevar pins the boundary atoms --- `id >= v` for a `v` at or
         * below the declared lower bound, `!(id >= v)` for a `v` above the
         * declared upper --- once, as a persistent top-of-proof line, precisely
         * so that a step wanting the fact can cite it. Ask for it rather than
         * emitting the same unit again: a `pol` that needs it needs it once per
         * use, and re-deriving it per use is what the pin exists to avoid.
         *
         * Nullopt when there is no such fact (a `v` strictly inside the
         * declared bounds), when the pin was suppressed (see
         * note_bounds_not_trivially_derivable), when assertions are on above
         * AssertionLevel::Links, and while the pin is still queued for proof
         * start --- so a caller during model building gets nothing and must
         * derive the fact itself. Call this after whatever made the atom
         * exist, since a pin for an atom nobody has asked for has not been
         * emitted.
         */
        [[nodiscard]] auto boundary_pin_line(const SimpleOrProofOnlyIntegerVariableID & id, Integer v) const -> std::optional<ProofLine>;

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
        [[nodiscard]] auto pb_file_string_for(const XLiteral &) const -> const std::string &;

        /**
         * Return the raw proof literal representing a variable condition, for writing to a model or log.
         */
        [[nodiscard]] auto xliteral_for(const VariableConditionFrom<SimpleOrProofOnlyIntegerVariableID> &) const -> const XLiteral;

        /**
         * Like xliteral_for, but returns nullopt instead of throwing when the
         * condition has no registered XLiteral. A condition is registered iff it
         * (or its negation) has been introduced --- so "not found" means the
         * literal is fresh/unaliased, which callers can use to reason about
         * whether two atoms could be the same underlying bit.
         */
        [[nodiscard]] auto find_xliteral_for(const VariableConditionFrom<SimpleOrProofOnlyIntegerVariableID> &) const -> std::optional<XLiteral>;

        /**
         * Return a string form of a raw proof literal, for writing to a model or log.
         */
        [[nodiscard]] auto pb_file_string_for(const VariableConditionFrom<SimpleOrProofOnlyIntegerVariableID> &) const -> const std::string &;

        /**
         * As pb_file_string_for, but introduce the condition's proof name
         * first if it does not exist yet (need_proof_name), in one lookup for
         * the common already-known case. Only for use while assembling a
         * proof line in a buffer: an introduction emits definition lines.
         */
        [[nodiscard]] auto pb_file_string_for_ensuring(const VariableConditionFrom<SimpleOrProofOnlyIntegerVariableID> &) -> const std::string &;

        /**
         * As xliteral_for, but introduce the condition's proof name first if
         * it does not exist yet, like pb_file_string_for_ensuring. Both
         * polarities are always introduced together, so negating the result
         * is the negated condition's literal; the reified-line renderer uses
         * this to avoid negating whole condition objects.
         */
        [[nodiscard]] auto xliteral_for_ensuring(const VariableConditionFrom<SimpleOrProofOnlyIntegerVariableID> &) -> XLiteral;

        /**
         * Return a string form of the exact literals specifying a bit assignment for var == val, an alternative way to witness solutions.
         */
        [[nodiscard]] auto bit_assignment_string_for(const SimpleOrProofOnlyIntegerVariableID & var, const Integer & value) const -> std::string;

        /**
         * Return the raw proof literal representing a proof flag, for writing to a model or log.
         */
        [[nodiscard]] auto xliteral_for(const ProofFlag &) const -> const XLiteral;

        /**
         * Like xliteral_for, but returns nullopt instead of throwing when the flag
         * has no registered XLiteral.
         */
        [[nodiscard]] auto find_xliteral_for(const ProofFlag &) const -> std::optional<XLiteral>;

        /**
         * Return a string form of a proof flag, for writing to a model or log. Same as calling
         * raw_literal_as_string(raw_proof_literal(flag)).
         */
        [[nodiscard]] auto pb_file_string_for(const ProofFlag &) const -> const std::string &;

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
         * Track the OPB bound-row references (lower row, upper row) for a
         * bits-encoded variable, so that proof steps can combine them by pol
         * (ProofLogger::introduce_bits_of derives a linear form's own bound
         * lines this way). A state variable's rows are referenced by their
         * `i[name][lb]` / `i[name][ub]` labels (count-robust under
         * cake_pb_cp's re-derived OPB); a proof-only variable's unlabelled
         * rows by constraint number (it never appears in a cake chain).
         */
        auto track_bound_rows(const SimpleOrProofOnlyIntegerVariableID & id, ProofLine lower_row, ProofLine upper_row) -> void;

        /**
         * The bound-row references recorded by track_bound_rows, or nullopt
         * for a variable with no OPB bound rows (one made by
         * ProofModel::create_proof_only_integer_variable_in_proof, whose
         * meaning lives entirely inside the proof).
         */
        [[nodiscard]] auto bound_rows(const SimpleOrProofOnlyIntegerVariableID & id) const -> std::optional<std::pair<ProofLine, ProofLine>>;

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
         * \brief Claim each of these `c[id][role]` labels for rows about to be
         * emitted, throwing ProofError if any is already taken or if the pack
         * repeats one.
         *
         * Called only by ProofModel::add_labelled_constraint's ConstraintID
         * overloads, which is what confines the set to the `c[id][role]`
         * namespace; the variable-encoding namespaces are deliberately out of
         * scope, because those rows may be deleted and re-emitted. It lives here
         * rather than in ProofModel because \ref constraint_row_label reads it,
         * and its reader is a presolver, which holds a ProofLogger and no
         * ProofModel --- and both are constructed with this same tracker.
         */
        auto claim_constraint_row_labels(const std::vector<std::string> & labels) -> void;

        /**
         * \brief The label of the row this constraint emitted under this role,
         * or nullopt if it emitted none.
         *
         * Answers "can I cite this?", not "what does it say". A label is a pure
         * function of `(id, role)`, so this needs no per-solve state beyond the
         * claimed set, and every clone of a constraint in every thread computes
         * the same answer.
         *
         * A `yes` always names exactly one row:
         * \ref claim_constraint_row_labels rejects two rows under one label at
         * emission time (#613), so the ambiguity a "look it up" answer would
         * otherwise have to worry about cannot exist by the time this is asked.
         *
         * Pair it with innards::ConstraintProofModelData, which is how a
         * constraint publishes *which* role names the row a citer wants;
         * constructing a role string here instead would be guessing at another
         * constraint's naming scheme.
         */
        [[nodiscard]] auto constraint_row_label(const ConstraintID & id, const std::string & role) const -> std::optional<ProofLineLabel>;

        /**
         * \brief The flag a constraint created under this key, if it created
         * one.
         *
         * The flag-side counterpart of \ref constraint_row_label, and the same
         * shape of answer: "may I cite this?", not "what does it say". A flag's
         * name is a pure function of `(id, values, annotation)` --- the same
         * function \ref create_proof_flag_values applies --- so this finds the
         * flag whichever clone of the constraint created it, and stores nothing
         * a solve depends on beyond the name index the flags already need.
         *
         * nullopt means no flag went out under that key: the constraint was
         * never installed, or proofs are off, or the key names a
         * (task, time) pair outside the window the constraint encoded. All of
         * those mean the same thing to a caller --- there is nothing to cite,
         * so do not do the thing that would need citing.
         *
         * Pair it with innards::ConstraintProofModelData, which is how a
         * constraint publishes the *keys* it uses; building one here instead
         * would be guessing at another constraint's naming scheme.
         *
         * Only the ConstraintID-keyed flag namespaces are indexed, matching
         * what \ref claim_constraint_row_labels covers on the row side: an
         * `f[index][stem]` flag is anonymous by construction and has no key to
         * look up.
         */
        [[nodiscard]] auto find_proof_flag_values(const ConstraintID & id, const ProofFlagKey & key) const -> std::optional<ProofFlag>;

        /**
         * \brief Record a line this constraint established *inside the proof*,
         * under a role, so that another constraint may build on it.
         *
         * The third kind of citable thing, beside a labelled OPB row
         * (\ref constraint_row_label) and a flag (\ref find_proof_flag_values),
         * and the one neither of those can express: a line an install
         * initialiser derived, which has no OPB row to label and no reification
         * to key. Cumulative's proof-only `end >= start + length` is the
         * motivating case.
         *
         * A line number rather than a label, because there is no label: what
         * comes back is a position in one particular proof file, so unlike the
         * other two this is per-solve state --- the same state
         * \ref boundary_pin_line already keeps, and kept for the same reason,
         * that a caller wanting the fact should cite the line rather than derive
         * it again.
         *
         * The role is in a namespace of its own, so it neither collides with a
         * `c[id][role]` label nor makes one; that a constraint uses the same
         * word for both is the constraint's business.
         *
         * \throws ProofError if this `(id, role)` has already published a line,
         * which means a role that does not name everything the emitting loop
         * varies over (#613, one namespace over).
         */
        auto publish_derived_line(const ConstraintID & id, const std::string & role, ProofLine line) -> void;

        /**
         * \brief Record that a flag's reification was emitted *inside the
         * proof*, and under which two lines.
         *
         * A flag defined by ProofModel carries `[r]` and `[f]` labels on its
         * two halves, and every citer references them by name. A flag defined
         * by ProofLogger::emit_red_proof_lines_reifying has no labels at all,
         * only line numbers, so a citer has to be told them --- which is what
         * this is for, and what \ref reification_half then hides.
         *
         * The halves are in the order the labels read: `implies` is the `[r]`
         * half, `flag -> ineq`, and `implied_by` is `[f]`, `ineq -> flag`.
         *
         * Per-solve state, like \ref publish_derived_line and for the same
         * reason: a proof line number is meaningless outside the proof file it
         * indexes. Registered per install, so it never outlives that.
         *
         * \throws ProofError if this flag has already been registered, which
         * means its definition went out twice.
         */
        auto register_in_proof_reification(const ProofFlag & flag, ProofLine implies, ProofLine implied_by) -> void;

        /**
         * \brief The two halves of a flag reified inside the proof, if it was
         * reified inside the proof.
         *
         * nullopt means it was not, which for a fully reified flag means its
         * halves are OPB rows and carry labels. Prefer \ref reification_half,
         * which answers "how do I cite this half" without the caller having to
         * know which of the two it is.
         */
        [[nodiscard]] auto in_proof_reification(const ProofFlag & flag) const -> std::optional<std::pair<ProofLine, ProofLine>>;

        /**
         * \brief The line a constraint published under this role, if it
         * published one.
         *
         * The same "may I cite this?" answer \ref constraint_row_label and
         * \ref find_proof_flag_values give, and nullopt means the same thing it
         * means there: the constraint was never installed, or proofs are off,
         * or it had nothing to publish under that role --- and in each case
         * there is nothing to cite, so do not do the thing that would need
         * citing.
         *
         * The one extra way of getting nullopt is *timing*: this is filled in by
         * an install initialiser, so a caller running before initialisers do
         * gets nothing. Presolvers run after (#658), which is what makes this
         * reachable for them at all.
         *
         * Pair it with innards::ConstraintProofModelData, which is how a
         * constraint publishes which role names the line a citer wants.
         */
        [[nodiscard]] auto find_derived_line(const ConstraintID & id, const std::string & role) const -> std::optional<ProofLine>;

        /**
         * \brief How to cite the row a constraint published under this role,
         * however it was written.
         *
         * The row-side counterpart of \ref reification_half, and the same
         * answer for the same reason: an OPB row gives its label, a row an
         * install initialiser derived inside the proof gives its line, and
         * ProofLine is already the variant of the two, so a citer needs to know
         * neither. #780 moves Cumulative's per-(task, time) contribution rows
         * from the first kind to the second under one encoding and not the
         * others.
         *
         * nullopt means the same thing it means in both halves of that: there
         * is nothing to cite, so do not do the thing that would need citing.
         */
        [[nodiscard]] auto constraint_row(const ConstraintID & id, const std::string & role) const -> std::optional<ProofLine>;

        /**
         * \brief A constraint's promise that it can derive, on demand, any line
         * in an integer-indexed family --- rather than publishing them all up
         * front.
         *
         * \ref publish_derived_line is for a fact a constraint decides to
         * establish once, whatever anyone does with it. This is for a family
         * whose members are too numerous to derive speculatively and whose
         * consumers are known only later: Cumulative's per-time capacity rows
         * under the start-checkpoint encoding (#780) are the first, where each
         * member costs `O(n^3)` proof lines and a horizon's worth of them would
         * dwarf the OPB block the encoding exists to delete.
         *
         * The deriver is called at most once per `(id, family, index)` and the
         * result memoised, so a second consumer of the same member pays
         * nothing. It may return nullopt, meaning this constraint cannot speak
         * about that member --- read exactly as nullopt from
         * \ref find_derived_line: there is nothing to cite, so do not do the
         * thing that would need citing.
         *
         * \warning **Whatever the deriver emits must live at ProofLevel::Top.**
         * The memo hands the same line number out for the rest of the proof,
         * and a line emitted at any lower level is deleted on backtracking ---
         * after which the memo is a dangling reference and nothing here can
         * tell. This is a promise the publisher makes and that nothing checks.
         *
         * Registered per install, like everything else that holds proof line
         * numbers, so it never outlives the proof whose lines it hands out.
         *
         * \todo This, \ref publish_derived_line and \ref boundary_pin_line are
         * three variations on "a per-solve, constraint-keyed memo of proof
         * lines", and each arrived for one caller. The tracker is meant to
         * provide general facilities rather than a drawer of specific ones, and
         * this is the third; #780's step 10 wants a fourth, the same thing for
         * *flags* rather than lines. Once that one exists there should be
         * enough examples to see the general requirement, and these should
         * collapse into it. Deliberately not generalised before then, on the
         * grounds that three examples are what tells you what the fourth needs.
         */
        auto publish_derived_line_family(const ConstraintID & id, const std::string & family,
            std::function<auto(ProofLogger &, Integer index)->std::optional<ProofLine>> deriver) -> void;

        /**
         * \brief The line for one member of a family published by
         * \ref publish_derived_line_family, deriving it if this is the first
         * ask.
         *
         * Nullopt when no deriver was published for `(id, family)` --- the
         * constraint was not installed, or proofs are off, or it does not have
         * this family --- or when the deriver itself declines.
         */
        [[nodiscard]] auto find_or_derive_line_in_family(const ConstraintID & id, const std::string & family, Integer index, ProofLogger & logger)
            -> std::optional<ProofLine>;

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
         * The numbers that determine a half-reification of a PB constraint:
         * the (negative) coefficient each negated reifying term is given, and
         * the constraint's effective right-hand side (adjusted if the
         * conjunction contains a statically-false literal). The reified
         * constraint is `lhs + reif_coefficient * (each ~term) <=
         * effective_rhs`; reify() materialises exactly that, and
         * emit_reified_inequality_to renders it directly.
         */
        struct ReificationShape
        {
            Integer reif_coefficient;
            Integer effective_rhs;
        };

        [[nodiscard]] auto reification_shape(const WPBSumLE &, const HalfReifyOnConjunctionOf &) -> ReificationShape;

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
         * Render an objective variable as the `.scp` `prob_type` spec:
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
