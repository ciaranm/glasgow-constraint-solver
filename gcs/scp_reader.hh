#ifndef GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_SCP_READER_HH
#define GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_SCP_READER_HH

#include <gcs/exception.hh>
#include <gcs/problem-fwd.hh>
#include <gcs/variable_id.hh>

#include <map>
#include <optional>
#include <string>
#include <string_view>

namespace gcs
{
    /**
     * \brief Thrown when a `.scp` (s-expression CP) description cannot be turned
     * into a Problem: malformed structure, an unsupported format version, an
     * unknown constraint, or a constraint this reader does not yet support.
     *
     * \ingroup Core
     */
    class ScpReadError : public MessageException
    {
    public:
        explicit ScpReadError(const std::string &);
    };

    /**
     * \brief What read_scp recovered from a `.scp` beyond the Problem it built:
     * the variables by name, and the objective if the document had one.
     *
     * \ingroup Core
     */
    struct ScpModel
    {
        /**
         * \brief A map from each variable's `.scp` name to its IntegerVariableID,
         * so a caller can report solution values by name.
         */
        std::map<std::string, IntegerVariableID> variables;

        /**
         * \brief The objective variable, to minimise, or nullopt for a `decide`
         * or `enumerate` document.
         *
         * This mirrors Problem::optional_minimise_variable(), so that reader and
         * writer are inverses: a `(maximize V)` spec gives back the negated view
         * of V, exactly what Problem::maximise() would have stored, and feeding
         * it to Problem::minimise() reinstates the original objective. A
         * constant objective (the writer renders one as `(minimize 3)`) comes
         * back as a constant variable.
         */
        std::optional<IntegerVariableID> minimise_variable;
    };

    /**
     * \brief Populate `problem` from the `.scp` (s-expression CP) description in
     * `text`: create its variables and post its constraints.
     *
     * This is the inverse of the `.scp` the solver writes under `--prove`, and
     * the basis of the "trusted producer" workflow (a `.scp` is the input). A
     * `.scp` written by the solver and read back here re-creates an equivalent
     * Problem; constraint labels are preserved via Problem::post_named.
     *
     * The document is the four-section version-1 form `( (version 1) (variables
     * ...) (constraints ...) (prob_type ...) )`. All four sections are required,
     * in that order, and the version must be exactly 1 — anything else is
     * rejected rather than guessed at.
     *
     * An objective in the `prob_type` section is resolved and returned, but is
     * deliberately *not* posted to `problem`: setting it would commit the caller
     * to optimising, and there is no way to unset it afterwards, so a caller who
     * wants to enumerate an optimisation instance (as the workflow-2 chain
     * harness does) could not. Call Problem::minimise() with
     * ScpModel::minimise_variable to honour it.
     *
     * Only a subset of constraints is supported so far (`abs`, `all_different`,
     * `in`, the comparisons, the linear forms, `equals`/`not_equals`, `element`
     * and `count`); an unsupported operator raises ScpReadError rather than
     * being silently dropped. Throws ScpReadError (or SExprParseError) on
     * malformed input.
     *
     * \returns The variables by name, and the objective if there was one.
     */
    auto read_scp(Problem & problem, std::string_view text) -> ScpModel;
}

#endif
