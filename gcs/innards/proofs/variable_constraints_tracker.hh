#ifndef GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_PROOFS_PROOF_VARIABLE_CONSTRAINTS_TRACKER_HH
#define GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_PROOFS_PROOF_VARIABLE_CONSTRAINTS_TRACKER_HH

#include <gcs/innards/proofs/proof_logger-fwd.hh>
#include <gcs/innards/proofs/proof_model-fwd.hh>
#include <gcs/innards/proofs/proof_only_variables.hh>
#include <gcs/innards/proofs/pseudo_boolean.hh>
#include <gcs/innards/proofs/reification.hh>
#include <gcs/innards/proofs/variable_constraints_tracker-fwd.hh>
#include <gcs/proof.hh>
#include <gcs/variable_condition.hh>
#include <gcs/variable_id.hh>

#include <memory>
#include <optional>
#include <string>
#include <variant>

namespace gcs::innards
{
    /**
     * Provides access to information about flags and variables being used in a proof.
     *
     * This is for information that is shared between a ProofModel and a ProofLogger,
     * because the lazy encoding can be introduced either in the model or inside a
     * log using extension variables.
     *
     * \ingroup Innards
     */
    class VariableConstraintsTracker
    {
    private:
        struct Imp;
        std::unique_ptr<Imp> _imp;

        [[nodiscard]] auto allocate_flag_index() -> unsigned long long;

    public:
        /**
         * \name Constructors, destructors, and the like.
         */
        ///@{

        explicit VariableConstraintsTracker(const ProofOptions &);
        ~VariableConstraintsTracker();

        auto operator=(const VariableConstraintsTracker &) -> VariableConstraintsTracker & = delete;
        VariableConstraintsTracker(const VariableConstraintsTracker &) = delete;

        VariableConstraintsTracker(VariableConstraintsTracker &&) noexcept;
        auto operator=(VariableConstraintsTracker &&) noexcept -> VariableConstraintsTracker &;

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
         * Say that we will need the greater-than-or-equal literal for a given variable.
         */
        auto need_gevar(SimpleOrProofOnlyIntegerVariableID id, Integer v) -> void;

        /**
         * Say that we will need the diect encoding to exist for a given variable.
         */
        auto need_direct_encoding_for(SimpleOrProofOnlyIntegerVariableID, Integer) -> void;

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
        [[nodiscard]] auto need_pol_item_defining_literal(const IntegerVariableCondition &) -> std::variant<ProofLine, std::string>;

        /**
         * Set things up internally as if the specified variable was a real
         * variable, so that proof_name() etc will work with it.
         */
        auto create_literals_for_introduced_variable_value(
            SimpleIntegerVariableID, Integer, const std::optional<std::string> &) -> void;

        /**
         * Ensure that a name exists for a given variable condition.
         */
        auto need_proof_name(const VariableConditionFrom<SimpleOrProofOnlyIntegerVariableID> &) -> void;

        /**
         * Ensure that need_proof_name() has been called for everything in a given sum.
         */
        auto need_all_proof_names_in(const SumOf<Weighted<PseudoBooleanTerm>> & sum) -> void;

        /**
         * Return a string form of a variable condition, for writing to a model or log.
         */
        [[nodiscard]] auto proof_name(const VariableConditionFrom<SimpleOrProofOnlyIntegerVariableID> &) const -> const std::string &;

        /**
         * Return a string form of a proof flag, for writing to a model or log.
         */
        [[nodiscard]] auto proof_name(const ProofFlag &) const -> const std::string &;

        /**
         * Call the supplied function for each bit making up the given variable, specifying
         * its string name and coefficient.
         */
        auto for_each_bit(const SimpleOrProofOnlyIntegerVariableID &,
            const std::function<auto(Integer, const std::string &)->void> &) -> void;

        /**
         * Get the name and coefficient for the bit position in the representation of the given var.
         */
        auto get_bit(const SimpleOrProofOnlyIntegerVariableID & var, unsigned long position) -> std::pair<Integer, std::string>;

        /**
         * Get the name and coefficient for the bit position in the representation of the given var.
         */
        auto get_bit(const ProofBitVariable & bit) -> std::pair<Integer, std::string>;

        auto num_bits(const SimpleOrProofOnlyIntegerVariableID & var) -> unsigned long long;
        /**
         * If there is a negative bit for this variable, return its coefficient, otherwise
         * return zero.
         */
        [[nodiscard]] auto negative_bit_coefficient(const SimpleOrProofOnlyIntegerVariableID &) -> Integer;

        /**
         * Given a desired variable name, turn it into something suitable for use
         * in a model or log.
         */
        [[nodiscard]] auto rewrite_variable_name(std::string &&) -> std::string;

        /**
         * Track that the associated literal exists, and has a string name.
         */
        auto track_condition_name(const VariableConditionFrom<SimpleOrProofOnlyIntegerVariableID> &, const std::string &) -> void;

        /**
         * Track that a given variable's bits exist.
         */
        auto track_bits(const SimpleOrProofOnlyIntegerVariableID & id, Integer negative_coeff,
            const std::vector<std::pair<Integer, std::string>> & bit_vars) -> void;

        /**
         * Track that a given greater-or-equal variable exists, and has a string name
         * and associated defining constraints.
         */
        auto track_gevar(SimpleIntegerVariableID, Integer,
            const std::pair<std::variant<ProofLine, std::string>, std::variant<ProofLine, std::string>> &) -> void;

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
        [[nodiscard]] auto reify(const WeightedPseudoBooleanLessEqual &, const HalfReifyOnConjunctionOf &) -> WeightedPseudoBooleanLessEqual;
    };
}

#endif
