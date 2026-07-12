#ifndef GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_CONSTRAINTS_KNAPSACK_KNAPSACK_HH
#define GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_CONSTRAINTS_KNAPSACK_KNAPSACK_HH

#include <gcs/constraint.hh>
#include <gcs/proof_strategy.hh>
#include <gcs/variable_id.hh>

#include <variant>
#include <vector>

namespace gcs
{
    /**
     * \brief The proof-logging strategies Knapsack supports:
     * proof_strategy::PerCall (the default) or proof_strategy::Upfront.
     *
     * PerCall rebuilds the DP table and proof scaffolding from scratch on
     * every propagation call, at ProofLevel::Temporary; Upfront emits
     * paper-style scaffolding once at the search root, at ProofLevel::Top.
     * Both draw the same inferences and find the same solutions; PerCall's
     * proofs verify 3.6–18× faster (so it is the default), Upfront's are
     * 3–6× smaller. See dev_docs/knapsack.md.
     *
     * \ingroup ProofStrategy
     */
    using KnapsackProofStrategy = std::variant<proof_strategy::PerCall, proof_strategy::Upfront>;

    /**
     * \brief Knapsack constraint:
     * <code>sum(coefficients[x][i] * vars[i]) = totals[x]</code> for
     * each <code>x</code>. Coefficients and item domains must be
     * non-negative.
     *
     * By default the proof is logged per propagation call
     * (proof_strategy::PerCall), which verifies substantially faster. Request
     * proof_strategy::Upfront via with_proof_strategy() for the opt-in
     * upfront-DAG scaffolding, which produces smaller but slower-to-verify
     * proofs; it draws the same inferences and finds the same solutions, and
     * never changes the OPB encoding. See <code>dev_docs/knapsack.md</code>
     * for the measured rationale.
     *
     * \ingroup Constraints
     */
    class Knapsack : public Constraint
    {
    private:
        std::vector<std::vector<Integer>> _coeffs;
        std::vector<IntegerVariableID> _vars;
        std::vector<IntegerVariableID> _totals;
        KnapsackProofStrategy _proof_strategy = proof_strategy::PerCall{};

    public:
        explicit Knapsack(std::vector<Integer> weights, std::vector<Integer> profits, std::vector<IntegerVariableID> vars, IntegerVariableID weight,
            IntegerVariableID profit);

        explicit Knapsack(std::vector<std::vector<Integer>> coefficients, std::vector<IntegerVariableID> vars, std::vector<IntegerVariableID> totals);

        /// Select the proof-logging strategy: proof_strategy::PerCall (the
        /// default, fastest to verify) or proof_strategy::Upfront (smaller
        /// proofs). Proof-only: it never changes the inferences drawn, the
        /// solutions found, or the OPB encoding.
        auto with_proof_strategy(KnapsackProofStrategy strategy) -> Knapsack &;

        virtual auto install(innards::Propagators &, innards::State &, innards::ProofModel * const) && -> void override;
        virtual auto clone() const -> std::unique_ptr<Constraint> override;
        [[nodiscard]] virtual auto s_expr(const innards::ProofModel * const) const -> innards::SExpr override;
        [[nodiscard]] virtual auto constraint_type() const -> std::string override;
    };
}

#endif
