#ifndef GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_INNARDS_S_EXPR_HH
#define GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_INNARDS_S_EXPR_HH

#include <exception>
#include <string>
#include <string_view>
#include <variant>
#include <vector>

namespace gcs::innards
{
    /**
     * \brief Thrown when text cannot be parsed as an s-expression, or when an
     * SExpr is inspected as the wrong kind (atom vs list).
     *
     * \ingroup Innards
     */
    class SExprParseError : public std::exception
    {
    private:
        std::string _wat;

    public:
        explicit SExprParseError(const std::string &);

        [[nodiscard]] virtual auto what() const noexcept -> const char * override;
    };

    /**
     * \brief A term in the `.scp` s-expression grammar: either an *atom* (an
     * indivisible token, stored verbatim) or a *list* of sub-terms.
     *
     * The `.scp` files the solver writes (and, in the verified-encoding
     * workflows, reads back) are plain s-expressions: whitespace and
     * parentheses are the only delimiters, and every other maximal run of
     * characters is an atom. Atoms therefore uniformly cover variable names
     * (`_1`), integers (`-3`), operator keywords (`all_different`) and
     * comparison symbols (`>=`); a view such as `(-_1 + 17)` is a three-element
     * list. The model carries no further type information — meaning is imposed
     * by whoever consumes the term.
     *
     * The point of routing both the writer (`Constraint::s_exprify`) and any
     * reader through this one type is that `to_string(parse_s_expr(s)) == s`
     * holds for every `s` already in the canonical form `to_string` emits, so
     * "write an `.scp`, read it back, write it again" is identity by
     * construction rather than by careful hand-formatting.
     */
    class SExpr final
    {
    private:
        std::variant<std::string, std::vector<SExpr>> _value;

    public:
        explicit SExpr(std::string atom);
        explicit SExpr(std::vector<SExpr> list);

        [[nodiscard]] static auto atom(std::string) -> SExpr;
        [[nodiscard]] static auto list(std::vector<SExpr>) -> SExpr;

        [[nodiscard]] auto is_atom() const -> bool;
        [[nodiscard]] auto is_list() const -> bool;

        /// The atom's text. Throws SExprParseError if this is a list.
        [[nodiscard]] auto as_atom() const -> const std::string &;
        /// The list's children. Throws SExprParseError if this is an atom.
        [[nodiscard]] auto as_list() const -> const std::vector<SExpr> &;

        [[nodiscard]] auto operator==(const SExpr &) const -> bool = default;
    };

    /**
     * \brief Parse exactly one s-expression from `text`, ignoring leading and
     * trailing whitespace.
     *
     * Throws SExprParseError if `text` is empty, malformed (e.g. unbalanced
     * parentheses), or contains more than one top-level term. A bare name such
     * as `_1` parses as an atom; a parenthesised name such as a view or a
     * reification condition `(_2 neq 1)` parses as the corresponding list, so
     * this is also the right way to turn a rendered variable / literal name
     * (from NamesAndIDsTracker::s_expr_name_of) into a term.
     */
    [[nodiscard]] auto parse_s_expr(std::string_view text) -> SExpr;

    /// \brief Parse zero or more whitespace-separated top-level s-expressions.
    [[nodiscard]] auto parse_s_expr_seq(std::string_view text) -> std::vector<SExpr>;

    /**
     * \brief Render `expr` canonically on a single line: an atom verbatim, a
     * list as `(` followed by its space-separated children followed by `)`,
     * with no padding next to the parentheses (so `()` for the empty list).
     */
    [[nodiscard]] auto to_string(const SExpr & expr) -> std::string;

    /**
     * \brief Render a sequence of terms as the space-separated body of a
     * constraint line — each term via `to_string`, joined by single spaces,
     * with no enclosing parentheses. This is what `Constraint::s_exprify`
     * returns; `solve()` adds the surrounding `( ... )`.
     */
    [[nodiscard]] auto to_string(const std::vector<SExpr> & terms) -> std::string;
}

#endif
