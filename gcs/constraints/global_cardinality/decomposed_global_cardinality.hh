#ifndef GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_CONSTRAINTS_GLOBAL_CARDINALITY_DECOMPOSED_GLOBAL_CARDINALITY_HH
#define GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_CONSTRAINTS_GLOBAL_CARDINALITY_DECOMPOSED_GLOBAL_CARDINALITY_HH

#include <gcs/constraint.hh>
#include <gcs/integer.hh>
#include <gcs/variable_id.hh>

#include <vector>

namespace gcs
{
    /**
     * \brief The Global Cardinality Constraint: constrain how many of the
     * variables in `vars` take each of the cover values in `values`.
     *
     * For each `i`, the number of variables in `vars` equal to `values[i]` is
     * constrained to equal the count variable `counts[i]`. A bounded number of
     * occurrences (the "low/up" form found in MiniZinc and XCSP3) is expressed
     * by giving the corresponding count variable the domain `low..up`; an exact
     * occurrence count by giving it a singleton domain.
     *
     * If `closed` is true, every variable in `vars` is additionally constrained
     * to take one of the cover values (so values outside `values` are
     * forbidden). If `closed` is false (the default, the "open" form), variables
     * may take values outside `values`; such values simply are not counted.
     *
     * The cover `values` are constants. The (rare) XCSP3 form with the cover
     * itself given as variables, and the MiniZinc `opt`/`set` overloads, are not
     * handled here and are expected to be decomposed by the frontend.
     *
     * This is the decomposition baseline: it is implemented as one Among
     * constraint per cover value (plus an In constraint per variable when
     * closed), so it reuses their proof logging directly. It is correct but does
     * not achieve generalised arc consistency on the conjunction.
     *
     * \ingroup Constraints
     */
    class GlobalCardinalityDecomposition : public Constraint
    {
    private:
        std::vector<IntegerVariableID> _vars;
        std::vector<Integer> _values;
        std::vector<IntegerVariableID> _counts;
        bool _closed;

    public:
        explicit GlobalCardinalityDecomposition(std::vector<IntegerVariableID> vars, std::vector<Integer> values,
            std::vector<IntegerVariableID> counts, bool closed = false);

        virtual auto install(innards::Propagators &, innards::State &,
            innards::ProofModel * const) && -> void override;
        virtual auto clone() const -> std::unique_ptr<Constraint> override;
        [[nodiscard]] virtual auto s_exprify(const innards::ProofModel * const) const -> std::string override;
    };
}

#endif
