#ifndef GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_CONSTRAINTS_ALL_DIFFERENT_JUSTIFY_HH
#define GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_CONSTRAINTS_ALL_DIFFERENT_JUSTIFY_HH

#include <gcs/innards/proofs/proof_logger.hh>
#include <gcs/innards/state.hh>
#include <gcs/integer.hh>
#include <gcs/variable_id.hh>

#include <map>
#include <vector>

namespace gcs::innards
{
    auto justify_all_different_hall_set_or_violator(ProofLogger &, const State &, const std::vector<IntegerVariableID> & all_variables,
        const std::vector<IntegerVariableID> & hall_variables, const std::vector<Integer> & hall_values,
        std::map<Integer, ProofLine> & constraint_numbers) -> void;

    /**
     * \brief The bounds form of justify_all_different_hall_set_or_violator():
     * every one of \p hall_variables has its bounds inside `[lo, hi]`, and
     * there are at least `hi - lo + 1` of them, so no other variable can take a
     * value in `[lo, hi]` (or, if there are more, nothing can).
     *
     * The difference is what each Hall variable's at-least-one names. The set
     * form names the values still in its domain, so the reason has to state its
     * holes; this names every value between its bounds, holes included, so the
     * reason need only state the bounds of each Hall variable, which is all a
     * bounds consistent propagator knows. The holes cost nothing: they are
     * inside `[lo, hi]`, where the at-most-ones cancel them.
     *
     * Emits the summed line at the current level; the caller's RUP step closes
     * the inference against it and the reason.
     */
    auto justify_all_different_hall_interval(ProofLogger &, const State &, const std::vector<IntegerVariableID> & all_variables,
        const std::vector<IntegerVariableID> & hall_variables, Integer lo, Integer hi, std::map<Integer, ProofLine> & constraint_numbers) -> void;
}

#endif
