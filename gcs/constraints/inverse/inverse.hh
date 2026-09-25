#ifndef GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_CONSTRAINTS_INVERSE_INVERSE_HH
#define GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_CONSTRAINTS_INVERSE_INVERSE_HH

#include <gcs/constraint.hh>
#include <gcs/innards/proofs/proof_logger.hh>
#include <gcs/variable_id.hh>

#include <map>
#include <memory>
#include <vector>

namespace gcs
{
    /**
     * \brief Constrain that `x[i] = j <-> y[j] = i`. By default the arrays
     * are zero-indexed, but the x_start and y_start arguments can be used
     * to specify a different starting index.
     *
     * The first array may be shorter than the second, which is XCSP3's
     * `channel` over lists of different lengths. Then only `x[i] = j -> y[j] = i`
     * holds: x is an injection into y's indices, and an entry of y that no
     * entry of x names is unconstrained, whatever its value. With equal lengths
     * the two readings coincide. A first array longer than the second is
     * rejected.
     *
     * The same variable twice in the first array, or twice in the second when
     * the lengths are equal, makes the model unsatisfiable, and is answered
     * with a contradiction at the root. In the injection form, the same
     * variable twice in the second array is satisfiable, since at most one of
     * the two entries need be named.
     *
     * \ingroup Constraints
     */
    class Inverse : public Constraint
    {
    private:
        const std::vector<IntegerVariableID> _x, _y;
        const Integer _x_start, _y_start;
        bool _has_duplicate_vars = false;
        std::shared_ptr<std::map<Integer, innards::ProofLine>> _x_value_am1s;

        [[nodiscard]] auto is_injection() const -> bool;

        virtual auto prepare(innards::Propagators &, innards::State &, innards::ProofModel * const) -> bool override;
        virtual auto define_proof_model(innards::ProofModel &, const innards::State &) -> void override;
        virtual auto install_propagators(innards::Propagators &) -> void override;

    public:
        explicit Inverse(std::vector<IntegerVariableID> x, std::vector<IntegerVariableID> y, Integer x_start = 0_i, Integer y_start = 0_i);

        virtual auto clone() const -> std::unique_ptr<Constraint> override;
        [[nodiscard]] virtual auto s_expr(const innards::ProofModel * const) const -> innards::SExpr override;
        [[nodiscard]] virtual auto constraint_type() const -> std::string override;
    };
}

#endif
