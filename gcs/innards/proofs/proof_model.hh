#ifndef GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_PROOFS_PROOF_MODEL_HH
#define GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_PROOFS_PROOF_MODEL_HH

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
#include <variant>
#include <vector>

namespace gcs::innards
{
    struct StringLiteral
    {
        template <typename T_, std::size_t n_, std::enable_if_t<std::is_same_v<T_, const char>>...>
        consteval StringLiteral(T_ (&s)[n_]) :
            value(s)
        {
        }

        char const * value;
    };

    class ProofModel
    {
    private:
        struct Imp;
        std::unique_ptr<Imp> _imp;

        auto set_up_bits_variable_encoding(SimpleOrProofOnlyIntegerVariableID, Integer, Integer, const std::optional<std::string> &) -> void;

        auto set_up_direct_only_variable_encoding(SimpleOrProofOnlyIntegerVariableID, Integer, Integer, const std::optional<std::string> &) -> void;

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
         * Add a pseudo-Boolean constraint to a Proof model.
         */
        auto add_constraint(
            const WeightedPseudoBooleanLessEqual & ineq,
            const std::optional<HalfReifyOnConjunctionOf> & half_reif = std::nullopt) -> std::optional<ProofLine>;

        /**
         * Add a pair of pseudo-Boolean constraints representing an equality to a Proof model.
         */
        auto add_constraint(
            const WeightedPseudoBooleanEquality & eq,
            const std::optional<HalfReifyOnConjunctionOf> & half_reif = std::nullopt) -> std::pair<std::optional<ProofLine>, std::optional<ProofLine>>;

        /**
         * Add a CNF definition to a Proof model.
         */
        auto add_constraint(
            const Literals & lits) -> std::optional<ProofLine>;

        /**
         * Add a pseudo-Boolean constraint to a Proof model.
         */
        auto add_constraint(
            const StringLiteral & constraint_name,
            const StringLiteral & rule,
            const WeightedPseudoBooleanLessEqual & ineq,
            const std::optional<HalfReifyOnConjunctionOf> & half_reif = std::nullopt) -> std::optional<ProofLine>;

        /**
         * Add a pair of pseudo-Boolean constraints representing an equality to a Proof model.
         */
        auto add_constraint(
            const StringLiteral & constraint_name,
            const StringLiteral & rule,
            const WeightedPseudoBooleanEquality & eq,
            const std::optional<HalfReifyOnConjunctionOf> & half_reif = std::nullopt) -> std::pair<std::optional<ProofLine>, std::optional<ProofLine>>;

        /**
         * Add a CNF definition to a Proof model.
         */
        auto add_constraint(
            const StringLiteral & constraint_name,
            const StringLiteral & rule,
            const Literals & lits) -> std::optional<ProofLine>;

        ///@}

        /**
         * \name Support variables and flags.
         */
        ///@{

        /**
         * Create a variable ID that is used only in proof definitions, not state.
         */
        [[nodiscard]] auto create_proof_only_integer_variable(Integer, Integer, const std::optional<std::string> &,
            const IntegerVariableProofRepresentation enc) -> ProofOnlySimpleIntegerVariableID;

        [[nodiscard]] auto create_proof_flag(const std::string &) -> ProofFlag;

        /**
         * Set up proof logging for an integer variable with the specified bounds,
         * that is being tracked inside State.
         */
        auto set_up_integer_variable(SimpleIntegerVariableID, Integer, Integer, const std::optional<std::string> &,
            const std::optional<IntegerVariableProofRepresentation> &) -> void;

        /**
         * State that we are solving an optimisation problem, minimising the specified variable.
         */
        auto minimise(const IntegerVariableID &) -> void;

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
        [[nodiscard]] auto number_of_constraints() const -> ProofLine;

        /**
         * Provide access to information about variables.
         */
        [[nodiscard]] auto names_and_ids_tracker() -> NamesAndIDsTracker &;
    };
}

#endif
