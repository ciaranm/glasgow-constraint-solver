#ifndef GLASGOW_CONSTRAINT_SOLVER_LP_JUSTIFIER_HH
#define GLASGOW_CONSTRAINT_SOLVER_LP_JUSTIFIER_HH

#include <gcs/innards/justification.hh>
#include <gcs/innards/proofs/proof_logger-fwd.hh>
#include <gcs/innards/proofs/pseudo_boolean.hh>
#include <gcs/innards/state.hh>
#include <map>

struct LPJustificationOptions final
{
    // Will put configuration options here.
};

namespace gcs::lp_innards
{
    using DerivationFunction = std::function<auto(gcs::innards::ProofLogger & logger, const gcs::innards::State & state)->gcs::innards::ProofLine>;
}

namespace gcs::innards
{
    class LPJustifier
    {
    private:
        struct Imp;
        std::unique_ptr<Imp> _imp;
        void _add_pb_constraint_to_lp(const WeightedPseudoBooleanLessEqual & pb_constraint);

    public:
        explicit LPJustifier(const LPJustificationOptions &);
        ~LPJustifier();

        auto operator=(const LPJustifier &) -> LPJustifier & = delete;
        LPJustifier(const LPJustifier &) = delete;

        LPJustifier(LPJustifier &&) noexcept;

        auto operator=(LPJustifier &&) noexcept -> LPJustifier &;

        void initialise_with_vars(State & state, std::vector<IntegerVariableID> dom_vars, std::vector<IntegerVariableID> bound_vars);

        void add_pb_constraint(const WeightedPseudoBooleanLessEqual & pb_constraint, ProofLine line);

        void add_pb_constraint(const WeightedPseudoBooleanLessEqual & pb_constraint, gcs::lp_innards::DerivationFunction how_to_derive);

        auto compute_justification(const State & state, ProofLogger & logger, const WeightedPseudoBooleanLessEqual & inference, const bool compute_bounds = false) -> ExplicitJustificationFunction;

        auto compute_bounds_and_justifications(const State & state, ProofLogger & logger, const PseudoBooleanTerm bounds_var) -> std::tuple<Integer, ExplicitJustificationFunction, Integer, ExplicitJustificationFunction>
    };
}

#endif // GLASGOW_CONSTRAINT_SOLVER_LP_JUSTIFIER_HH
