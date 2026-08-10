#ifndef GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_CONSTRAINTS_IN_IN_HH
#define GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_CONSTRAINTS_IN_IN_HH

#include <gcs/constraint.hh>
#include <gcs/innards/proofs/proof_only_variables.hh>
#include <gcs/variable_id.hh>

#include <vector>

namespace gcs
{
    /**
     * \brief Constrain that `var` is equal to one of the specified values, or to
     * one of the specified variables.
     *
     * The value list and variable list are unioned: the constraint is satisfied
     * iff `var` equals at least one constant in the value list, or equals at
     * least one variable in the variable list.
     *
     * \ingroup Constraints
     */
    class In : public Constraint
    {
    private:
        IntegerVariableID _var;
        std::vector<IntegerVariableID> _var_vals;
        std::vector<Integer> _val_vals;
        std::vector<innards::ProofFlag> _selectors;
        std::string _proof_role_prefix;
        bool _has_no_values = false;

        virtual auto prepare(innards::Propagators &, innards::State &, innards::ProofModel * const) -> bool override;
        virtual auto define_proof_model(innards::ProofModel &, const innards::State &) -> void override;
        virtual auto install_propagators(innards::Propagators &) -> void override;

    public:
        explicit In(IntegerVariableID var, std::vector<IntegerVariableID> vars, std::vector<Integer> vals);
        explicit In(IntegerVariableID var, std::vector<IntegerVariableID> vals);
        explicit In(IntegerVariableID var, std::vector<Integer> vals);

        /**
         * \brief Prefix this instance's OPB roles, for a parent installing more
         * than one In under its own identity.
         *
         * A child takes its parent's ConstraintID (so its rows are attributed to
         * the constraint the user posted), which means several children would
         * otherwise emit `@c[id][al1]` twice over -- ProofModel rejects that, and
         * rightly: a role has to name everything that varies. GlobalCardinality's
         * closed restriction is one In per variable, and passes `"<i>_"`, giving
         * `@c[id][<i>_al1]` -- which is exactly the label cake_pb_cp's
         * cencode_global_cardinality_aux emits for the same row.
         *
         * A single-child parent (SeqPrecedeChain's ValuePrecede) needs none of
         * this and leaves the prefix empty.
         */
        auto with_proof_role_prefix(std::string prefix) -> In &;

        virtual auto clone() const -> std::unique_ptr<Constraint> override;
        [[nodiscard]] virtual auto s_expr(const innards::ProofModel * const) const -> innards::SExpr override;
        [[nodiscard]] virtual auto constraint_type() const -> std::string override;
    };
}

#endif
