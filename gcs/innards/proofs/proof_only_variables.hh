#ifndef GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_INNARDS_PROOFS_PROOF_ONLY_VARIABLES_HH
#define GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_INNARDS_PROOFS_PROOF_ONLY_VARIABLES_HH

#include <gcs/innards/literal.hh>
#include <gcs/innards/proofs/proof_only_variables-fwd.hh>
#include <gcs/variable_condition.hh>
#include <gcs/variable_id.hh>

#include <string>
#include <variant>

namespace gcs::innards
{

    /**
     * Behaves similar to a SimpleIntegerVariableID, except only appears
     * in a Proof, with no associated State.
     *
     * \ingroup Innards
     */
    struct ProofOnlySimpleIntegerVariableID
    {
        unsigned long long index;

        explicit ProofOnlySimpleIntegerVariableID(unsigned long long x) :
            index(x)
        {
        }

        [[nodiscard]] auto operator<=>(const ProofOnlySimpleIntegerVariableID &) const = default;
    };

    [[nodiscard]] auto debug_string(const ProofOnlySimpleIntegerVariableID &) -> std::string;

    using SimpleOrProofOnlyIntegerVariableID = std::variant<SimpleIntegerVariableID, ProofOnlySimpleIntegerVariableID>;

    struct ProofBitVariable
    {
        SimpleOrProofOnlyIntegerVariableID for_var;
        Integer position;
        bool positive;

        [[nodiscard]] auto operator<=>(const ProofBitVariable &) const = default;
    };

    /**
     * \brief Negate a ProofBitVariable.
     *
     * \ingroup Innards
     * \sa ProofFlag
     */
    [[nodiscard]] auto operator!(const ProofBitVariable &) -> ProofBitVariable;

    using ProofVariableCondition = VariableConditionFrom<ProofOnlySimpleIntegerVariableID>;

    using ProofLiteral = std::variant<Literal, ProofVariableCondition>;

    using ProofLiteralOrFlag = std::variant<ProofLiteral, ProofFlag, ProofBitVariable>;

    /**
     * \brief A Boolean flag that is used inside proofs like a variable, but
     * that does not appear in the constraint programming model.
     *
     * \ingroup Innards
     */
    struct ProofFlag
    {
        unsigned long long index;
        bool positive = true;

        [[nodiscard]] auto operator<=>(const ProofFlag &) const = default;
    };

    /**
     * \brief Negate a ProofFlag.
     *
     * \ingroup Innards
     * \sa ProofFlag
     */
    [[nodiscard]] auto operator!(const ProofFlag &) -> ProofFlag;

    /**
     * \brief Negate a ProofLiteral.
     *
     * \ingroup Innards
     * \sa ProofFlag
     */
    [[nodiscard]] auto operator!(const ProofLiteral &) -> ProofLiteral;

    /**
     * \brief Negate a ProofLiteralOrFlag.
     *
     * \ingroup Innards
     * \sa ProofFlag
     */
    [[nodiscard]] auto operator!(const ProofLiteralOrFlag &) -> ProofLiteralOrFlag;
}

namespace gcs
{
    template <>
    constexpr auto enable_conditional_variable_operators<innards::ProofOnlySimpleIntegerVariableID>() -> bool
    {
        return true;
    }

    template <>
    constexpr auto enable_conditional_variable_operators<innards::SimpleOrProofOnlyIntegerVariableID>() -> bool
    {
        return true;
    }
}

#endif
