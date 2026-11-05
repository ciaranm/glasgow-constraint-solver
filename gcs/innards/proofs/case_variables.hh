#ifndef GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_INNARDS_PROOFS_CASE_VARIABLES_HH
#define GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_INNARDS_PROOFS_CASE_VARIABLES_HH

#include <gcs/innards/literal.hh>
#include <gcs/innards/proofs/proof_only_variables.hh>
#include <gcs/integer.hh>
#include <gcs/interval_set.hh>
#include <gcs/variable_condition.hh>
#include <gcs/variable_id.hh>

#include <vector>

namespace gcs::innards
{
    /**
     * \brief Case variables for a `cases` step that splits on the values of an
     * integer variable: one equality atom per value.
     *
     * For a conclusion that holds whichever of \c values the variable takes.
     * The branch where every atom is false must be closed by the reason (or
     * the database) excluding everything outside \c values, which is how the
     * per-value loops this replaces were closed too.
     *
     * \c values is any range of Integer: a domain snapshot, an IntervalSet's
     * `each()`, or a plain vector. Build it from the domain the reason was
     * built from, not the live one, when the inference being justified can
     * change it (see the aliasing notes in min_max and element).
     *
     * \ingroup Innards
     * \sa JustifyUsingCases, ProofLogger::emit_cases_proof_line_under_reason
     */
    template <typename Values_>
    [[nodiscard]] auto case_variables_over_values(const IntegerVariableID & var, Values_ && values) -> std::vector<ProofLiteralOrFlag>
    {
        std::vector<ProofLiteralOrFlag> result;
        for (Integer v : values)
            result.emplace_back(ProofLiteral{Literal{var == v}});
        return result;
    }

    /**
     * \brief Case variables for a `cases` step that splits on which interval of
     * \c intervals an integer variable lies in: one range literal per interval,
     * which is the equality atom for an interval of width one.
     *
     * For a conclusion whose branches only need to know the interval, not the
     * value, so the split costs one case per interval rather than one per
     * value.
     *
     * \ingroup Innards
     * \sa case_variables_over_values
     */
    [[nodiscard]] inline auto case_variables_over_intervals(const IntegerVariableID & var, const IntervalSet<Integer> & intervals)
        -> std::vector<ProofLiteralOrFlag>
    {
        std::vector<ProofLiteralOrFlag> result;
        for (auto [lo, hi] : intervals.each_interval())
            result.emplace_back(ProofLiteral{Literal{in_range(var, lo, hi)}});
        return result;
    }
}

#endif
