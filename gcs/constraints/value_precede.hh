#ifndef GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_CONSTRAINTS_VALUE_PRECEDE_HH
#define GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_CONSTRAINTS_VALUE_PRECEDE_HH

#include <gcs/constraint.hh>
#include <gcs/integer.hh>
#include <gcs/variable_id.hh>

#include <vector>

namespace gcs
{
    /**
     * \brief Constrain that the values in `chain` appear in `vars` in chain
     * order: for each consecutive pair (chain[j-1], chain[j]), every
     * occurrence of chain[j] in `vars` must have an earlier occurrence of
     * chain[j-1].
     *
     * For a length-2 chain `{s, t}`, this is the basic value_precede
     * constraint: if any element of `vars` equals `t`, then a strictly
     * earlier element must equal `s`. For longer chains, this is the
     * value_precede_chain constraint: each consecutive pair must satisfy
     * value_precede on the same array.
     *
     * Chains of length less than 2 install nothing (trivially satisfied).
     * Repeated values in the chain are accepted; the conjunction of pairwise
     * constraints can be infeasible (e.g., `{1, 2, 1}` requires both
     * 1 ≺ 2 and 2 ≺ 1).
     *
     * \ingroup Constraints
     */
    class ValuePrecede : public Constraint
    {
    private:
        std::vector<Integer> _chain;
        std::vector<IntegerVariableID> _vars;

        virtual auto prepare(innards::Propagators &, innards::State &, innards::ProofModel * const) -> bool override;
        virtual auto define_proof_model(innards::ProofModel &) -> void override;
        virtual auto install_propagators(innards::Propagators &) -> void override;

    public:
        /**
         * \brief Construct from a chain of values and an array of variables.
         *
         * For each consecutive pair `(chain[j-1], chain[j])`, every
         * occurrence of `chain[j]` in `vars` must have a strictly earlier
         * occurrence of `chain[j-1]`. A chain of length less than 2 imposes
         * no constraint.
         *
         * \param chain the sequence of values whose first occurrences in
         *   `vars` must respect the chain order.
         * \param vars the array of variables to constrain.
         */
        explicit ValuePrecede(std::vector<Integer> chain, std::vector<IntegerVariableID> vars);

        /**
         * \brief Convenience constructor for the length-2 case.
         *
         * Equivalent to `ValuePrecede({s, t}, vars)`. If any element of
         * `vars` equals `t`, then a strictly earlier element must equal `s`.
         *
         * \param s the value that must precede.
         * \param t the value whose first occurrence must come after `s`'s
         *   first occurrence.
         * \param vars the array of variables to constrain.
         */
        explicit ValuePrecede(Integer s, Integer t, std::vector<IntegerVariableID> vars);

        virtual auto install(innards::Propagators &, innards::State &,
            innards::ProofModel * const) && -> void override;
        virtual auto clone() const -> std::unique_ptr<Constraint> override;
        [[nodiscard]] virtual auto s_exprify(const std::string & name, const innards::ProofModel * const) const -> std::string override;
    };
}

#endif
