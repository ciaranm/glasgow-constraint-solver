#ifndef GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_CONSTRAINTS_PARITY_PARITY_SYSTEM_HH
#define GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_CONSTRAINTS_PARITY_PARITY_SYSTEM_HH 1

#include <gcs/constraint.hh>
#include <gcs/constraints/parity/parity_chain.hh>
#include <gcs/innards/literal.hh>
#include <gcs/variable_condition.hh>
#include <gcs/variable_id.hh>

#include <vector>

namespace gcs
{
    /**
     * \brief Propagation strength for the ParitySystem constraint.
     *
     * Neither setting changes the OPB encoding: define_proof_model is identical
     * for both.
     *
     * - \c CheckOnly acts only once every literal of a row is assigned, and
     *   then only to refute a wrong parity. That is no stronger than posting
     *   each row as its own ParityOdd and rather slower, so it is not a
     *   strength anyone wants --- it is the encoding's standing regression
     *   test, kept because the encoding is what everything else here is built
     *   on. \c MinDistance keeps its check-only mode for the same reason.
     * - \c GaussJordan is the real thing: eliminate over the whole system at
     *   every wake and read off every literal it implies.
     *
     * \ingroup Constraints
     */
    enum class ParitySystemPropagation
    {
        CheckOnly,
        GaussJordan
    };

    /**
     * \brief Constrain that an odd number of literals is true in each of
     * several rows, reasoning about the rows together rather than one at a
     * time.
     *
     * A single ParityOdd is already GAC --- unit propagation on one parity
     * constraint *is* GAC, because any value has a support while two of its
     * literals are still free --- so all of the inference a system of them
     * offers lives in the conjunction. Over GF(2) that conjunction is one of
     * the rare tractable cases: Gauss-Jordan exposes every literal the system
     * implies, and implied literals are exactly what GAC on the system means.
     *
     * Every row is *odd* parity, as ParityOdd's name says; an even row is
     * written with one of its literals negated, which is what this constraint
     * does with it internally anyway.
     *
     * See dev_docs/parity-system.md, and ParitySystemGathering, which builds
     * one of these out of the ParityOdd constraints a model has already posted
     * --- which is how a model reaching us through a frontend will get here,
     * since XOR structure survives MiniZinc flattening as individual
     * `array_bool_xor` constraints.
     *
     * \ingroup Constraints
     */
    class ParitySystem : public Constraint
    {
    private:
        const std::vector<innards::Literals> _rows;
        ParitySystemPropagation _propagation;

        // Filled in by define_proof_model, read by install_propagators, which
        // runs next on the same object. Empty when proofs are off, which is
        // also when nothing reads it.
        std::vector<innards::ParityChainRows> _chains;

        virtual auto define_proof_model(innards::ProofModel &, const innards::State &) -> void override;
        virtual auto install_propagators(innards::Propagators &) -> void override;

        auto install_check_only_propagator(innards::Propagators &) -> void;
        auto install_gauss_jordan_propagator(innards::Propagators &) -> void;

    public:
        // Equivalent to ParitySystem([[var != 0 : var in row] : row in rows])
        explicit ParitySystem(
            const std::vector<std::vector<IntegerVariableID>> & rows, ParitySystemPropagation = ParitySystemPropagation::GaussJordan);

        explicit ParitySystem(std::vector<innards::Literals>, ParitySystemPropagation = ParitySystemPropagation::GaussJordan);

        virtual auto clone() const -> std::unique_ptr<Constraint> override;

        /**
         * \brief The rows, as posted.
         *
         * \sa ParitySystemGathering
         */
        [[nodiscard]] auto rows() const GCS_LIFETIME_BOUND -> const std::vector<innards::Literals> &
        {
            return _rows;
        }

        /**
         * \brief `(id parity_system ((lits...) ...))`.
         *
         * Not part of the CakePB workflow --- cake has `parity` for one row and
         * nothing for a system of them --- but a `.scp` is written on every
         * proof-logged run that asks for one, so this has to produce valid
         * output rather than throw. Nogoods is the precedent, and as there, our
         * own `.scp` reader round-trips it.
         */
        [[nodiscard]] virtual auto s_expr(const innards::ProofModel * const) const -> innards::SExpr override;
        [[nodiscard]] virtual auto constraint_type() const -> std::string override;
    };
}

#endif
