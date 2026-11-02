#ifndef GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_SCP_READER_HH
#define GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_SCP_READER_HH

#include <gcs/exception.hh>
#include <gcs/objective.hh>
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
     * \brief The specific ScpReadError for a constraint keyword this reader has
     * no case for at all, as opposed to a keyword it knows whose arguments were
     * malformed or use a shape it cannot rebuild.
     *
     * The distinction is what lets the constraint tests assert writer/reader
     * *symmetry* — that every keyword Constraint::s_expr() can emit is one
     * read_scp accepts. See also ScpUnrebuildableShapeError, the one other
     * failure those tests expect.
     *
     * \ingroup Core
     */
    class ScpUnsupportedConstraintError : public ScpReadError
    {
    private:
        std::string _operator_name;

    public:
        explicit ScpUnsupportedConstraintError(const std::string & op);

        /// The keyword that had no case, for a caller that wants to classify it.
        [[nodiscard]] auto operator_name() const -> const std::string &
        {
            return _operator_name;
        }
    };

    /**
     * \brief The specific ScpReadError for a well-formed instance of a keyword
     * this reader knows, in a shape the public constructors cannot rebuild.
     *
     * There is one such shape: a non-deterministic automaton, which cake_pb_cp
     * accepts but Regular has no public constructor for. It is a known reader
     * limitation rather than a malformed document, and the constraint tests'
     * writer/reader symmetry check tolerates it and nothing else. Add a shape
     * here only for the same reason; a shape that could be rebuilt is a missing
     * reader case instead.
     *
     * \ingroup Core
     */
    class ScpUnrebuildableShapeError : public ScpReadError
    {
    public:
        explicit ScpUnrebuildableShapeError(const std::string &);
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
         * \brief The objective, or nullopt for a `decide` or `enumerate`
         * document.
         *
         * This mirrors Problem::optional_objective(), so that reader and writer
         * are inverses: a `(maximize V)` spec gives back V with
         * ObjectiveDirection::Maximise, and handing that to Problem::maximise()
         * reinstates the original objective. A constant objective (the writer
         * renders one as `(minimize 3)`) comes back as a constant variable, and a
         * view (`(maximize (-X + 2))`) as the view.
         */
        std::optional<Objective> objective;
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
     * harness does) could not. Call Problem::minimise() or Problem::maximise()
     * with ScpModel::objective to honour it.
     *
     * The reader is expected to accept **every** keyword Constraint::s_expr()
     * can write: the workflow-2 chain harness re-solves the `.scp` as its first
     * step, so a keyword with no case here fails the chain before the verified
     * encoder is reached. The constraint tests enforce that (see
     * test_innards::check_scp_writer_reader_symmetry), so adding a constraint
     * means adding its case below. An unknown keyword raises
     * ScpUnsupportedConstraintError rather than being silently dropped.
     *
     * Anywhere a variable may appear, so may an integer constant or a view,
     * written as NamesAndIDsTracker::s_expr_name_of renders one: `(X + c)` or
     * `(-X + c)`, with the offset always written. A reification condition takes
     * all six of cake_pb_cp's comparison symbols, `=`, `!=`, `>=`, `>`, `<=` and
     * `<`, although the writer only uses `=`, `!=`, `>=` and `<`.
     *
     * What the reader does *not* promise is that every *instance* round-trips:
     * a non-deterministic automaton is a shape the public constructors cannot
     * rebuild, and raises ScpUnrebuildableShapeError.
     * Throws SExprParseError on malformed input.
     *
     * \returns The variables by name, and the objective if there was one.
     */
    auto read_scp(Problem & problem, std::string_view text) -> ScpModel;
}

#endif
