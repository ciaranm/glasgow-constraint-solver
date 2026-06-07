#ifndef GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_SCP_READER_HH
#define GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_SCP_READER_HH

#include <gcs/problem-fwd.hh>
#include <gcs/variable_id.hh>

#include <exception>
#include <map>
#include <string>
#include <string_view>

namespace gcs
{
    /**
     * \brief Thrown when a `.scp` (s-expression CP) description cannot be turned
     * into a Problem: malformed structure, an unknown constraint, or a
     * constraint this reader does not yet support.
     *
     * \ingroup Core
     */
    class ScpReadError : public std::exception
    {
    private:
        std::string _wat;

    public:
        explicit ScpReadError(const std::string &);

        [[nodiscard]] virtual auto what() const noexcept -> const char * override;
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
     * Only a subset of constraints is supported so far (`abs`, `all_different`,
     * `in`, the comparisons, the linear forms, `equals`/`not_equals`, `element`
     * and `count`); an unsupported operator raises ScpReadError rather than
     * being silently dropped. Throws ScpReadError (or SExprParseError) on
     * malformed input.
     *
     * \returns A map from each variable's `.scp` name to its IntegerVariableID,
     * so a caller can report solution values by name.
     */
    auto read_scp(Problem & problem, std::string_view text) -> std::map<std::string, IntegerVariableID>;
}

#endif
