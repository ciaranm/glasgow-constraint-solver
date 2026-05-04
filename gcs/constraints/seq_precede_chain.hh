#ifndef GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_CONSTRAINTS_SEQ_PRECEDE_CHAIN_HH
#define GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_CONSTRAINTS_SEQ_PRECEDE_CHAIN_HH

#include <gcs/constraint.hh>
#include <gcs/variable_id.hh>

#include <vector>

namespace gcs
{
    /**
     * \brief For every positive value v that appears in `vars`, the value
     * v-1 must appear at a strictly earlier position.
     *
     * Equivalent to `ValuePrecede` with the implicit chain
     * `[1, 2, ..., max_possible]`. Non-positive values (zero and negatives)
     * are unconstrained — they may appear at any position.
     *
     * In an array of length n, no element can take a value greater than n,
     * because the chain forces v distinct earlier positions to host
     * 1, 2, ..., v-1 before any v can appear. To exploit this, the
     * implementation clamps the chain at min(max_possible_value, n) and
     * adds explicit upper-bound enforcement on each variable when the
     * declared domains exceed n. The resulting OPB encoding is bounded
     * purely by array length, independent of how loose the declared
     * variable domains are.
     *
     * \ingroup Constraints
     */
    class SeqPrecedeChain : public Constraint
    {
    private:
        std::vector<IntegerVariableID> _vars;

    public:
        /**
         * \brief Construct from an array of variables.
         *
         * \param vars the array to constrain. The implicit chain
         *   `[1, 2, ..., max]` is derived from the variables' declared
         *   upper bounds at install time.
         */
        explicit SeqPrecedeChain(std::vector<IntegerVariableID> vars);

        virtual auto install(innards::Propagators &, innards::State &,
            innards::ProofModel * const) && -> void override;
        virtual auto clone() const -> std::unique_ptr<Constraint> override;
        [[nodiscard]] virtual auto s_exprify(const std::string & name, const innards::ProofModel * const) const -> std::string override;
    };
}

#endif
