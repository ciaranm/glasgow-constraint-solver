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
        unsigned long long position;
        bool is_neg_bit;

        explicit ProofBitVariable(SimpleOrProofOnlyIntegerVariableID v, unsigned long long n, bool neg = false) :
            for_var(v),
            position(n),
            is_neg_bit(neg)
        {
        }

#if (_LIBCPP_VERSION)
        // again need workaround for clang/libcpp on MacOS
        [[nodiscard]] inline auto operator<(const ProofBitVariable & other) const -> bool
        {
            return std::tuple{for_var, position, is_neg_bit} < std::tuple{other.for_var, other.position, other.is_neg_bit};
        }
#endif

        [[nodiscard]] auto operator<=>(const ProofBitVariable &) const = default;
    };
    using ProofVariableCondition = VariableConditionFrom<ProofOnlySimpleIntegerVariableID>;

    using ProofLiteral = std::variant<Literal, ProofVariableCondition>;

    using ProofLiteralOrFlag = std::variant<ProofLiteral, ProofFlag>;

    /**
     * \brief A Boolean flag that is used inside proofs like a variable, but
     * that does not appear in the constraint programming model.
     *
     * \ingroup Innards
     */
    struct ProofFlag
    {
        unsigned long long index;
        bool positive;

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
