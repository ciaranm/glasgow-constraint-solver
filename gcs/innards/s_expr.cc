#include <gcs/innards/s_expr.hh>

#include <utility>

using std::get;
using std::holds_alternative;
using std::move;
using std::string;
using std::string_view;
using std::vector;

using namespace gcs::innards;

SExprParseError::SExprParseError(const string & w) :
    _wat("S-expression error: " + w)
{
}

auto SExprParseError::what() const noexcept -> const char *
{
    return _wat.c_str();
}

SExpr::SExpr(string atom) :
    _value(move(atom))
{
}

SExpr::SExpr(vector<SExpr> list) :
    _value(move(list))
{
}

auto SExpr::atom(string a) -> SExpr
{
    return SExpr{move(a)};
}

auto SExpr::list(vector<SExpr> l) -> SExpr
{
    return SExpr{move(l)};
}

auto SExpr::is_atom() const -> bool
{
    return holds_alternative<string>(_value);
}

auto SExpr::is_list() const -> bool
{
    return holds_alternative<vector<SExpr>>(_value);
}

auto SExpr::as_atom() const -> const string &
{
    if (! is_atom())
        throw SExprParseError{"expected an atom, found a list"};
    return get<string>(_value);
}

auto SExpr::as_list() const -> const vector<SExpr> &
{
    if (! is_list())
        throw SExprParseError{"expected a list, found an atom"};
    return get<vector<SExpr>>(_value);
}

namespace
{
    auto is_space(char c) -> bool
    {
        return c == ' ' || c == '\t' || c == '\n' || c == '\r' || c == '\f' || c == '\v';
    }

    // A whitespace- and parenthesis-delimited recursive-descent reader over a
    // string_view. Everything that is neither whitespace nor a parenthesis is
    // an atom character, so commas, comparison symbols, signs and underscores
    // all fall inside atoms without special handling.
    struct Reader final
    {
        string_view text;
        string_view::size_type pos = 0;

        auto skip_whitespace() -> void
        {
            while (pos < text.size() && is_space(text[pos]))
                ++pos;
        }

        // True once only whitespace remains.
        auto at_end() -> bool
        {
            skip_whitespace();
            return pos >= text.size();
        }

        auto read_one() -> SExpr
        {
            skip_whitespace();
            if (pos >= text.size())
                throw SExprParseError{"unexpected end of input while expecting a term"};
            if (text[pos] == ')')
                throw SExprParseError{"unexpected ')'"};

            if (text[pos] == '(') {
                ++pos; // consume '('
                vector<SExpr> children;
                while (true) {
                    skip_whitespace();
                    if (pos >= text.size())
                        throw SExprParseError{"unexpected end of input: unclosed '('"};
                    if (text[pos] == ')') {
                        ++pos; // consume ')'
                        break;
                    }
                    children.push_back(read_one());
                }
                return SExpr::list(move(children));
            }

            auto start = pos;
            while (pos < text.size() && ! is_space(text[pos]) && text[pos] != '(' && text[pos] != ')')
                ++pos;
            return SExpr::atom(string{text.substr(start, pos - start)});
        }
    };
}

auto gcs::innards::parse_s_expr(string_view text) -> SExpr
{
    Reader reader{text};
    if (reader.at_end())
        throw SExprParseError{"empty input"};
    auto result = reader.read_one();
    if (! reader.at_end())
        throw SExprParseError{"trailing characters after a single top-level term"};
    return result;
}

auto gcs::innards::parse_s_expr_seq(string_view text) -> vector<SExpr>
{
    Reader reader{text};
    vector<SExpr> result;
    while (! reader.at_end())
        result.push_back(reader.read_one());
    return result;
}

// Rendering is provided by the std::formatter / fmt::formatter specialisation in
// s_expr.hh, so there is no to_string() here (which would shadow std::to_string
// inside gcs::innards).
