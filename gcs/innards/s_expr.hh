#ifndef GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_INNARDS_S_EXPR_HH
#define GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_INNARDS_S_EXPR_HH

#include <gcs/innards/s_expr-fwd.hh>

#include <exception>
#include <string>
#include <string_view>
#include <variant>
#include <vector>
#include <version>

#if defined(__cpp_lib_print) && defined(__cpp_lib_format)
#include <format>
#else
#include <fmt/format.h>
#endif

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
     * An SExpr is rendered with `std::format` / `fmt::format`: `format("{}", e)`
     * gives the canonical single-line form (an atom verbatim; a list as `(`, its
     * space-separated children, `)`, with no padding, so `()` for the empty
     * list). The alternate form `format("{:#}", e)` renders a *list* without its
     * enclosing parentheses — the body of a constraint's `.scp` line. Because
     * the writer and any reader share this one type, `format("{}",
     * parse_s_expr(s)) == s` for every `s` already in canonical form, so "write
     * an `.scp`, read it back, write it again" is identity by construction.
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
}

// SExpr is rendered through the formatting machinery rather than a free
// to_string(), both because that is how the rest of the codebase formats and to
// avoid a to_string() overload in gcs::innards shadowing std::to_string. The
// optional '#' flag drops a list's enclosing parentheses (the constraint body).
#if defined(__cpp_lib_print) && defined(__cpp_lib_format)
template <>
struct std::formatter<gcs::innards::SExpr>
{
    bool bare = false;

    constexpr auto parse(std::format_parse_context & ctx)
    {
        auto it = ctx.begin();
        if (it != ctx.end() && *it == '#') {
            bare = true;
            ++it;
        }
        if (it != ctx.end() && *it != '}')
            throw std::format_error{"invalid format spec for SExpr (only '#' is accepted)"};
        return it;
    }

    auto format(const gcs::innards::SExpr & expr, std::format_context & ctx) const
    {
        auto out = ctx.out();
        if (expr.is_atom())
            return std::format_to(out, "{}", expr.as_atom());
        if (! bare)
            *out++ = '(';
        bool first = true;
        for (const auto & child : expr.as_list()) {
            if (! first)
                *out++ = ' ';
            first = false;
            out = std::format_to(out, "{}", child);
        }
        if (! bare)
            *out++ = ')';
        return out;
    }
};
#else
template <>
struct fmt::formatter<gcs::innards::SExpr>
{
    bool bare = false;

    constexpr auto parse(fmt::format_parse_context & ctx) -> decltype(ctx.begin())
    {
        auto it = ctx.begin();
        if (it != ctx.end() && *it == '#') {
            bare = true;
            ++it;
        }
        if (it != ctx.end() && *it != '}')
            throw fmt::format_error{"invalid format spec for SExpr (only '#' is accepted)"};
        return it;
    }

    auto format(const gcs::innards::SExpr & expr, fmt::format_context & ctx) const -> decltype(ctx.out())
    {
        auto out = ctx.out();
        if (expr.is_atom())
            return fmt::format_to(out, "{}", expr.as_atom());
        if (! bare)
            *out++ = '(';
        bool first = true;
        for (const auto & child : expr.as_list()) {
            if (! first)
                *out++ = ' ';
            first = false;
            out = fmt::format_to(out, "{}", child);
        }
        if (! bare)
            *out++ = ')';
        return out;
    }
};
#endif

#endif
