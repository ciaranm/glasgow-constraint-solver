#ifndef GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_PROOFS_PROOF_MODEL_HH
#define GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_PROOFS_PROOF_MODEL_HH

#include <gcs/constraint_id.hh>
#include <gcs/expression.hh>
#include <gcs/innards/proofs/names_and_ids_tracker-fwd.hh>
#include <gcs/innards/proofs/proof_logger-fwd.hh>
#include <gcs/innards/proofs/proof_model-fwd.hh>
#include <gcs/innards/proofs/pseudo_boolean.hh>
#include <gcs/innards/proofs/reification.hh>
#include <gcs/proof.hh>

#include <memory>
#include <optional>
#include <type_traits>
#include <vector>

namespace gcs::innards
{
    struct StringLiteral
    {
        template <typename T_, std::size_t n_, std::enable_if_t<std::is_same_v<T_, const char>>...>
        consteval StringLiteral(T_ (&s)[n_]) : value(s)
        {
        }

        char const * value;
    };

    /**
     * \brief How to name a proof-only integer variable's bit literals to match
     * cake_pb_cp's value-flag scheme, instead of the default `p[index_name][b]`:
     * value bit b becomes `v[id][indices..._b][value_annotation]` and a
     * two's-complement variable's sign bit becomes `v[id][indices...][sign_annotation]`
     * (required when the range is negative, or when the sign bit is forced below). The bits are still the variable's bits;
     * only their names change. Passing one to create_proof_only_integer_variable also
     * makes the variable a free bit-sum (no OPB bound lines), matching how cake encodes
     * these auxiliaries. Mirrors NamesAndIDsTracker::create_proof_flag_values.
     */
    struct CakeBitNaming
    {
        ConstraintID id;
        std::vector<long long> indices;
        std::string value_annotation;
        std::optional<std::string> sign_annotation;

        // cake's arg_sort encodes its sorted-value variables in two's complement
        // *unconditionally*, emitting a sign bit even when the value can never be
        // negative -- so to match it here we have to add a redundant sign bit for a
        // non-negative variable too. This exists only to reproduce that; the right
        // fix is for cake's arg_sort encoder to drop the sign bit when the range is
        // non-negative, after which this flag (and its embarrassing name) can go.
        bool add_a_pointless_sign_bit_only_because_cake_argsort_wastefully_always_does = false;

        // Which flag family the bits render in: the default `v[id][...]` (Values,
        // matching create_proof_flag_values, e.g. arg_sort/sort/value_precede) or
        // cake's `x[id][...]` (Indices, matching create_proof_flag). cake's
        // multiply/divide/modulus encoders name their magnitude bits
        // x[id][axis_i][bin], so those magnitude variables set this to true so the
        // bit-product cutting-planes resolve against cake's flags unchanged.
        bool use_indices_family = false;
    };

    class ProofModel
    {
    private:
        struct Imp;
        std::unique_ptr<Imp> _imp;

        auto advance_constraint_counter() -> ProofLineNumber;

        // Build the constraint label `c[constraint_id][role]` (printed with a
        // leading @). Returns a ProofLineLabel (not a ProofLine): the result is
        // streamed as a definition prefix and used as a count-robust reference;
        // it is never a numeric line.
        auto emit_constraint_label(const std::string & constraint_id, const std::string & role) -> ProofLineLabel;

        // Register a bits encoding (allocate/name the bit literals, track bounds)
        // without emitting anything to the OPB. The shared "register" half of
        // set_up_bits_variable_encoding and create_proof_only_integer_variable_in_proof;
        // the registered bits are then readable via the tracker's each_bit. With a
        // CakeBitNaming the bit literals are named in cake's value-flag scheme.
        auto register_bits_variable_encoding(
            SimpleOrProofOnlyIntegerVariableID, Integer, Integer, const std::string &, const std::optional<CakeBitNaming> & = std::nullopt) -> void;

        auto set_up_bits_variable_encoding(
            SimpleOrProofOnlyIntegerVariableID, Integer, Integer, const std::string &, const std::optional<CakeBitNaming> & = std::nullopt) -> void;

        auto set_up_direct_only_variable_encoding(SimpleOrProofOnlyIntegerVariableID, Integer, Integer, const std::string &) -> void;

    public:
        /**
         * \name Constructors, destructors, and the like.
         */
        ///@{
        explicit ProofModel(const ProofOptions &, NamesAndIDsTracker &);
        ~ProofModel();

        auto operator=(const ProofModel &) -> ProofModel & = delete;
        ProofModel(const ProofModel &) = delete;

        ProofModel(ProofModel &&) noexcept;
        auto operator=(ProofModel &&) noexcept -> ProofModel &;
        ///@}

        /**
         * \name Definitions, for proofs.
         */
        ///@{

        /**
         * Add a pseudo-Boolean constraint to a Proof model. Returns void: to
         * reference the constraint later, add it by @label (add_labelled_constraint),
         * never by line number.
         */
        auto add_constraint(const WPBSumLE & ineq, const std::optional<HalfReifyOnConjunctionOf> & half_reif = std::nullopt) -> void;

        /**
         * Add a pair of pseudo-Boolean constraints representing an equality to a
         * Proof model. Returns void --- see the inequality overload above.
         */
        auto add_constraint(const WPBSumEq & eq, const std::optional<HalfReifyOnConjunctionOf> & half_reif = std::nullopt) -> void;

        /**
         * Add a CNF definition to a Proof model.
         */
        auto add_constraint(const Literals & lits) -> void;

        /**
         * Add a pseudo-Boolean constraint to a Proof model.
         */
        auto add_constraint(const StringLiteral & constraint_name, const StringLiteral & rule, const WPBSumLE & ineq,
            const std::optional<HalfReifyOnConjunctionOf> & half_reif = std::nullopt) -> void;

        /**
         * Add a pair of pseudo-Boolean constraints representing an equality to a Proof model.
         */
        auto add_constraint(const StringLiteral & constraint_name, const StringLiteral & rule, const WPBSumEq & eq,
            const std::optional<HalfReifyOnConjunctionOf> & half_reif = std::nullopt) -> void;

        /**
         * \brief Like add_constraint for an equality, but emits an @label on each
         * half --- \c c[constraint_id][role_le] on the LE half and \c [role_ge]
         * on the GE half --- and returns those labels, so the proof references
         * the halves by label rather than by line number. The labels must match
         * what \c cake_pb_cp emits for this constraint.
         *
         * Returns `{LE-half, GE-half}`, as the unlabelled overload does.
         *
         * Part of moving every constraint reference off line numbers and onto
         * labels.
         */
        auto add_labelled_constraint(const std::string & constraint_id, const std::string & role_le, const std::string & role_ge,
            const StringLiteral & constraint_name, const StringLiteral & rule, const WPBSumEq & eq,
            const std::optional<HalfReifyOnConjunctionOf> & half_reif = std::nullopt) -> std::pair<ProofLine, ProofLine>;

        /**
         * \brief Add a single inequality under a caller-supplied @label, returning
         * that label as the ProofLine. `label` is the full label body (e.g.
         * \c i[X][ge0][f]); used for the variable-encoding @i labels, whose shape
         * (\c i[name][...][f|r]) the caller builds rather than the c[id][role] form.
         */
        auto add_labelled_constraint(
            const std::string & label, const WPBSumLE & ineq, const std::optional<HalfReifyOnConjunctionOf> & half_reif = std::nullopt) -> ProofLine;

        /**
         * \brief Add a CNF clause under a caller-supplied @label, returning that
         * label as the ProofLine, so a later proof step references the clause by
         * name. A clause whose only content is a statically-true literal collapses
         * to the trivially-true `sum >= 0`. The labelled counterpart of the plain
         * \c add_constraint(Literals) (which, returning void, cannot be referenced).
         */
        auto add_labelled_constraint(const std::string & label, const Literals & lits) -> ProofLine;

        /**
         * \brief Like add_constraint for a single inequality, but emits @c[id][role]
         * and returns that label as the ProofLine, so the proof references it by
         * label. The role must match what \c cake_pb_cp emits.
         */
        auto add_labelled_constraint(const std::string & constraint_id, const std::string & role, const StringLiteral & constraint_name,
            const StringLiteral & rule, const WPBSumLE & ineq, const std::optional<HalfReifyOnConjunctionOf> & half_reif = std::nullopt) -> ProofLine;

        /**
         * Add a CNF definition to a Proof model.
         */
        auto add_constraint(const StringLiteral & constraint_name, const StringLiteral & rule, const Literals & lits) -> void;

        /**
         * \brief Encode `flag ⇔ ineq` in OPB by emitting both halves of the equivalence:
         * the forward implication `flag → ineq` and the reverse `¬flag → ¬ineq`. The
         * reverse half is the integer negation of `ineq`.
         *
         * Replaces the common pattern of writing the two halves by hand, which makes
         * it easy to forget one direction (leaving the flag UP-free under solution
         * extension) or to compute the negation incorrectly.
         */
        auto add_two_way_reified_constraint(const StringLiteral & constraint_name, const StringLiteral & rule, const WPBSumLE & ineq,
            const ProofFlag & flag) -> std::pair<ProofLine, ProofLine>;

        /**
         * \brief Create a fresh proof flag and fully reify it against `ineq` in one
         * go: equivalent to `create_proof_flag` followed by
         * `add_two_way_reified_constraint`.
         */
        [[nodiscard]] auto create_proof_flag_fully_reifying(
            const std::string & flag_name, const StringLiteral & constraint_name, const StringLiteral & rule, const WPBSumLE & ineq) -> ProofFlag;

        /**
         * \brief As create_proof_flag_fully_reifying, but names the flag cake's
         * position-indexed `x[id][i1_i2..][annotation?]` (see create_proof_flag with
         * an index list) and emits the two implication halves under the labels
         * `x[..][r]` (flag -> ineq) and `x[..][f]` (~flag -> ~ineq), matching cake.
         *
         * The `x` prefix reflects that the flag is position-indexed, not that it is
         * reified: cake names count's fully-reified flags `x[...]` (scalar flags would
         * be `b[...]`). The halves carry raw `@` labels and no `* constraint` comment,
         * matching cake (and the variable-encoding @i labels). See issue #354.
         */
        [[nodiscard]] auto create_proof_flag_fully_reifying(const ConstraintID & id, const std::vector<long long> & indices,
            const std::optional<std::string> & annotation, const WPBSumLE & ineq) -> ProofFlag;

        /**
         * \brief As the position-indexed create_proof_flag_fully_reifying above, but
         * names the flag cake's value-indexed `v[id][v1_v2..][annotation?]` (see
         * create_proof_flag_values), with halves under `v[..][r]` / `v[..][f]`.
         * nvalue's per-value occurrence flag is the first consumer. See #354.
         */
        [[nodiscard]] auto create_proof_flag_values_fully_reifying(const ConstraintID & id, const std::vector<long long> & values,
            const std::optional<std::string> & annotation, const WPBSumLE & ineq) -> ProofFlag;

        ///@}

        /**
         * \name Support variables and flags.
         */
        ///@{

        /**
         * Create a variable ID that is used only in proof definitions, not state.
         *
         * With a CakeBitNaming, the variable's bits are named in cake_pb_cp's
         * value-flag scheme (see CakeBitNaming) and nothing is emitted to the OPB
         * (the variable is a free bit-sum, matching how cake encodes such an
         * auxiliary); its eq/ge atoms are then introduced lazily in the proof when
         * first used. Without one, the encoding (with OPB bound constraints) is
         * written as usual under the default `p[index_name][b]` names.
         */
        [[nodiscard]] auto create_proof_only_integer_variable(Integer, Integer, const std::string &, const IntegerVariableProofRepresentation enc,
            const std::optional<CakeBitNaming> & = std::nullopt) -> ProofOnlySimpleIntegerVariableID;

        /**
         * Create a bits-encoded proof-only variable whose encoding is NOT emitted
         * to the OPB. The bits are registered (named, usable in proof expressions)
         * but the model asserts nothing about them; the caller introduces the
         * variable's meaning inside the proof (see ProofLogger::introduce_bits_of).
         * The bits analogue of NamesAndIDsTracker::create_literals_for_introduced_variable_value.
         */
        [[nodiscard]] auto create_proof_only_integer_variable_in_proof(Integer, Integer, const std::string &) -> ProofOnlySimpleIntegerVariableID;

        /**
         * Register a bits encoding for an already-state-allocated integer variable
         * WITHOUT emitting anything to the OPB, so the caller can define the
         * variable's meaning inside the proof (ProofLogger::introduce_bits_of).
         * Unlike set_up_integer_variable (which asserts the bound constraints in the
         * OPB), this keeps the variable a free bit-sum, so a proof that introduces it
         * as a conservative extension stays chain-portable against cake_pb_cp's OPB.
         * The variable keeps its solver state, so it can still drive propagation ---
         * the combination the pure proof-only
         * create_proof_only_integer_variable_in_proof cannot provide.
         */
        auto register_state_variable_bits_in_proof(const SimpleIntegerVariableID &, Integer, Integer, const std::string &) -> void;

        [[nodiscard]] auto create_proof_flag(const std::string & stem) -> ProofFlag;

        /**
         * Create a position-indexed flag named `x[id][i1_i2..][annotation?]`,
         * conforming to cake_pb_cp's naming for verified encodings. See
         * NamesAndIDsTracker::create_proof_flag(const ConstraintID &, const std::vector<long long> &, ...).
         */
        [[nodiscard]] auto create_proof_flag(const ConstraintID & id, const std::vector<long long> & indices,
            const std::optional<std::string> & annotation = std::nullopt) -> ProofFlag;

        /**
         * Create a scalar flag named `b[id][annotation]`, conforming to cake_pb_cp's
         * naming for verified encodings. See
         * NamesAndIDsTracker::create_proof_flag(const ConstraintID &, const std::string &).
         */
        [[nodiscard]] auto create_proof_flag(const ConstraintID & id, const std::string & annotation) -> ProofFlag;

        /**
         * Create a value-indexed flag named `v[id][v1_v2..][annotation?]`,
         * conforming to cake_pb_cp's naming. See
         * NamesAndIDsTracker::create_proof_flag_values.
         */
        [[nodiscard]] auto create_proof_flag_values(const ConstraintID & id, const std::vector<long long> & values,
            const std::optional<std::string> & annotation = std::nullopt) -> ProofFlag;

        /**
         * Set up proof logging for an integer variable with the specified bounds,
         * that is being tracked inside State.
         *
         * With a CakeBitNaming the bits are named in cake's value-flag scheme and no
         * OPB bound lines are emitted (a free bit-sum), as for
         * create_proof_only_integer_variable --- for a State variable that is internal
         * to a constraint and that cake encodes as a proof-only auxiliary (e.g.
         * ArgSort's sorted-value variables). The atoms are then introduced lazily in
         * the proof. Without one, the usual `i[name][b]` bits and @i[name][lb]/[ub]
         * bounds are written.
         */
        auto set_up_integer_variable(SimpleIntegerVariableID, Integer, Integer, const std::string &,
            const std::optional<IntegerVariableProofRepresentation> &, const std::optional<CakeBitNaming> & = std::nullopt) -> void;

        /**
         * State that we are solving an optimisation problem, minimising the specified variable.
         */
        auto minimise(const IntegerVariableID &) -> void;

        /**
         * State that we might be enumerating, and specify the variables to preserve.
         */
        auto preserve(std::vector<IntegerVariableID> vars) -> void;

        ///@}

        /**
         * Finish writing the model. Must be called once, immediately before
         * proof writing starts.
         */
        auto finalise() -> void;

        /**
         * How many constraints do we have? Used to generate the proof header
         * inside a proof log.
         */
        [[nodiscard]] auto number_of_constraints() const -> ProofLineNumber;

        /**
         * Provide access to information about variables.
         */
        [[nodiscard]] auto names_and_ids_tracker() -> NamesAndIDsTracker &;

        /**
         * Provide access to information about variables.
         */
        [[nodiscard]] auto names_and_ids_tracker() const -> const NamesAndIDsTracker &;
    };
}

#endif
