#include <gcs/constraints/regular_regex.hh>
#include <gcs/exception.hh>

#include <cstddef>
#include <map>
#include <memory>
#include <queue>
#include <set>
#include <string>
#include <unordered_map>
#include <utility>
#include <vector>

using gcs::Integer;
using gcs::InvalidProblemDefinitionException;

using std::make_unique;
using std::map;
using std::move;
using std::pair;
using std::queue;
using std::set;
using std::size_t;
using std::string;
using std::unique_ptr;
using std::unordered_map;
using std::vector;

namespace
{
    // ---- Lexer -------------------------------------------------------------
    //
    // Tokens mirror libminizinc's regex lexer (lib/support/regex/lexer.lxx)
    // exactly: whitespace is ignored, a run of digits is one integer symbol,
    // and every other recognised character is a single token. Anything else is
    // a hard error.
    enum class Tok
    {
        Integer,
        Union,      // |
        Plus,       // +
        Star,       // *
        GroupOpen,  // (
        GroupClose, // )
        Optional,   // ?
        QuantOpen,  // {
        QuantClose, // }
        Comma,      // ,
        Any,        // .
        ClassOpen,  // [
        ClassClose, // ]
        ClassRange, // -
        ClassNeg,   // ^
        End
    };

    struct Token
    {
        Tok kind;
        Integer value = Integer{0};
    };

    auto tokenize(const string & s) -> vector<Token>
    {
        vector<Token> tokens;
        for (size_t i = 0; i < s.size();) {
            char c = s[i];
            if (c == ' ' || c == '\t' || c == '\n') {
                ++i;
                continue;
            }
            if (c >= '0' && c <= '9') {
                long long value = 0;
                while (i < s.size() && s[i] >= '0' && s[i] <= '9') {
                    value = value * 10 + (s[i] - '0');
                    ++i;
                }
                tokens.push_back({Tok::Integer, Integer{value}});
                continue;
            }
            switch (c) {
            case '|': tokens.push_back({Tok::Union}); break;
            case '+': tokens.push_back({Tok::Plus}); break;
            case '*': tokens.push_back({Tok::Star}); break;
            case '(': tokens.push_back({Tok::GroupOpen}); break;
            case ')': tokens.push_back({Tok::GroupClose}); break;
            case '?': tokens.push_back({Tok::Optional}); break;
            case '{': tokens.push_back({Tok::QuantOpen}); break;
            case '}': tokens.push_back({Tok::QuantClose}); break;
            case ',': tokens.push_back({Tok::Comma}); break;
            case '.': tokens.push_back({Tok::Any}); break;
            case '[': tokens.push_back({Tok::ClassOpen}); break;
            case ']': tokens.push_back({Tok::ClassClose}); break;
            case '-': tokens.push_back({Tok::ClassRange}); break;
            case '^': tokens.push_back({Tok::ClassNeg}); break;
            default:
                throw InvalidProblemDefinitionException(
                    string{"Illegal token in regular expression: '"} + c + "'");
            }
            ++i;
        }
        tokens.push_back({Tok::End});
        return tokens;
    }

    // ---- Core AST ----------------------------------------------------------
    //
    // The grammar is normalised down to a tiny core: a symbol set (matches one
    // value from the set), the empty word, concatenation, union, and Kleene
    // star. Quantifiers and "?" are desugared into these during parsing, so
    // both the automaton builder and the reference matcher stay small.
    enum class Core
    {
        Empty,
        Symbols,
        Concat,
        Union,
        Star
    };

    struct CoreNode
    {
        Core op;
        set<Integer> symbols;
        vector<unique_ptr<CoreNode>> children;
    };

    using NodePtr = unique_ptr<CoreNode>;

    auto make_empty() -> NodePtr
    {
        return make_unique<CoreNode>(Core::Empty);
    }

    auto make_symbols(set<Integer> symbols) -> NodePtr
    {
        auto n = make_unique<CoreNode>(Core::Symbols);
        n->symbols = move(symbols);
        return n;
    }

    auto make_binary(Core op, NodePtr a, NodePtr b) -> NodePtr
    {
        auto n = make_unique<CoreNode>(op);
        n->children.push_back(move(a));
        n->children.push_back(move(b));
        return n;
    }

    auto make_concat(NodePtr a, NodePtr b) -> NodePtr
    {
        return make_binary(Core::Concat, move(a), move(b));
    }

    auto make_union(NodePtr a, NodePtr b) -> NodePtr
    {
        return make_binary(Core::Union, move(a), move(b));
    }

    auto make_star(NodePtr a) -> NodePtr
    {
        auto n = make_unique<CoreNode>(Core::Star);
        n->children.push_back(move(a));
        return n;
    }

    auto clone(const CoreNode & n) -> NodePtr
    {
        auto c = make_unique<CoreNode>(n.op);
        c->symbols = n.symbols;
        for (const auto & child : n.children)
            c->children.push_back(clone(*child));
        return c;
    }

    // n copies of atom concatenated; n == 0 is the empty word.
    auto repeat_exact(const CoreNode & atom, long long n) -> NodePtr
    {
        if (n <= 0)
            return make_empty();
        auto result = clone(atom);
        for (long long i = 1; i < n; ++i)
            result = make_concat(move(result), clone(atom));
        return result;
    }

    // atom repeated n or more times: atom^n followed by atom*.
    auto repeat_at_least(const CoreNode & atom, long long n) -> NodePtr
    {
        return make_concat(repeat_exact(atom, n), make_star(clone(atom)));
    }

    // atom repeated between n and m times: atom^n followed by (m - n) optional atoms.
    auto repeat_between(const CoreNode & atom, long long n, long long m) -> NodePtr
    {
        auto result = repeat_exact(atom, n);
        for (long long i = n; i < m; ++i)
            result = make_concat(move(result), make_union(clone(atom), make_empty()));
        return result;
    }

    // ---- Parser ------------------------------------------------------------
    //
    // Recursive descent following the libminizinc grammar verbatim, with
    // precedence quantifier > concatenation > union.
    struct Parser
    {
        const vector<Token> & tokens;
        const set<Integer> & alphabet;
        size_t pos = 0;

        [[nodiscard]] auto peek() const -> Tok
        {
            return tokens[pos].kind;
        }

        auto advance() -> Token
        {
            return tokens[pos++];
        }

        [[noreturn]] static auto fail(const string & message) -> void
        {
            throw InvalidProblemDefinitionException("Cannot parse regular expression: " + message);
        }

        auto expect(Tok kind, const string & what) -> Token
        {
            if (peek() != kind)
                fail("expected " + what);
            return advance();
        }

        static auto starts_atom(Tok kind) -> bool
        {
            return kind == Tok::Integer || kind == Tok::Any || kind == Tok::ClassOpen || kind == Tok::GroupOpen;
        }

        // expression : term | term "|" expression
        auto parse_expression() -> NodePtr
        {
            auto term = parse_term();
            if (peek() == Tok::Union) {
                advance();
                return make_union(move(term), parse_expression());
            }
            return term;
        }

        // term : factor | factor term
        auto parse_term() -> NodePtr
        {
            auto factor = parse_factor();
            if (starts_atom(peek()))
                return make_concat(move(factor), parse_term());
            return factor;
        }

        // factor : atom | atom "*" | atom "+" | atom "?" | atom "{" ... "}"
        auto parse_factor() -> NodePtr
        {
            auto atom = parse_atom();
            switch (peek()) {
                using enum Tok;
            case Star:
                advance();
                return make_star(move(atom));
            case Plus: {
                advance();
                auto star = make_star(clone(*atom));
                return make_concat(move(atom), move(star));
            }
            case Optional:
                advance();
                return make_union(move(atom), make_empty());
            case QuantOpen:
                advance();
                return parse_quantifier(*atom);
            default:
                return atom;
            }
        }

        // The "{" has already been consumed: "{" n "}" | "{" n "," "}" | "{" n "," m "}"
        auto parse_quantifier(const CoreNode & atom) -> NodePtr
        {
            auto n = expect(Tok::Integer, "an integer after '{'").value.raw_value;
            if (peek() == Tok::QuantClose) {
                advance();
                return repeat_exact(atom, n);
            }
            expect(Tok::Comma, "',' or '}' in quantifier");
            if (peek() == Tok::QuantClose) {
                advance();
                return repeat_at_least(atom, n);
            }
            auto m = expect(Tok::Integer, "an integer after ',' in quantifier").value.raw_value;
            expect(Tok::QuantClose, "'}' to close quantifier");
            if (m < n)
                fail("quantifier upper bound is below its lower bound");
            return repeat_between(atom, n, m);
        }

        // atom : INTEGER | "." | "[" ... "]" | "(" expression ")"
        auto parse_atom() -> NodePtr
        {
            switch (peek()) {
                using enum Tok;
            case Integer:
                return make_symbols({advance().value});
            case Any:
                advance();
                return make_symbols(alphabet);
            case ClassOpen:
                return parse_class();
            case GroupOpen: {
                advance();
                auto inner = parse_expression();
                expect(GroupClose, "')' to close group");
                return inner;
            }
            default:
                fail("expected a symbol, '.', '[' or '('");
            }
        }

        // "[" set_items "]" or "[" "^" set_items "]"
        auto parse_class() -> NodePtr
        {
            expect(Tok::ClassOpen, "'['");
            bool negated = false;
            if (peek() == Tok::ClassNeg) {
                advance();
                negated = true;
            }
            auto items = parse_set_items();
            expect(Tok::ClassClose, "']' to close class");
            if (! negated)
                return make_symbols(move(items));

            set<Integer> complement;
            for (const auto & val : alphabet)
                if (! items.contains(val))
                    complement.insert(val);
            return make_symbols(move(complement));
        }

        // set_items : set_item | set_item set_items ; set_item : INTEGER | INTEGER "-" INTEGER
        auto parse_set_items() -> set<Integer>
        {
            set<Integer> items;
            if (peek() != Tok::Integer)
                fail("expected at least one value in a class");
            while (peek() == Tok::Integer) {
                auto from = advance().value;
                if (peek() == Tok::ClassRange) {
                    advance();
                    auto to = expect(Tok::Integer, "an integer after '-' in a class").value;
                    if (to < from)
                        std::swap(from, to);
                    for (auto val = from; val <= to; ++val)
                        items.insert(val);
                }
                else
                    items.insert(from);
            }
            return items;
        }
    };

    auto parse_regex(const string & regex, const set<Integer> & alphabet) -> NodePtr
    {
        auto tokens = tokenize(regex);
        Parser parser{tokens, alphabet};
        auto node = parser.parse_expression();
        parser.expect(Tok::End, "end of regular expression");
        return node;
    }

    // ---- Thompson construction --------------------------------------------
    //
    // Builds an epsilon-NFA fragment-wise; each fragment has a single start and
    // a single accept state.
    struct ThompsonBuilder
    {
        vector<vector<long>> eps;
        vector<vector<pair<Integer, long>>> sym;

        auto add_state() -> long
        {
            eps.emplace_back();
            sym.emplace_back();
            return static_cast<long>(eps.size()) - 1;
        }

        struct Fragment
        {
            long start;
            long accept;
        };

        auto build(const CoreNode & n) -> Fragment
        {
            switch (n.op) {
                using enum Core;
            case Empty: {
                auto s = add_state(), a = add_state();
                eps[s].push_back(a);
                return {s, a};
            }
            case Symbols: {
                auto s = add_state(), a = add_state();
                for (const auto & symbol : n.symbols)
                    sym[s].push_back({symbol, a});
                return {s, a};
            }
            case Concat: {
                auto x = build(*n.children[0]);
                auto y = build(*n.children[1]);
                eps[x.accept].push_back(y.start);
                return {x.start, y.accept};
            }
            case Union: {
                auto s = add_state(), a = add_state();
                auto x = build(*n.children[0]);
                auto y = build(*n.children[1]);
                eps[s].push_back(x.start);
                eps[s].push_back(y.start);
                eps[x.accept].push_back(a);
                eps[y.accept].push_back(a);
                return {s, a};
            }
            case Star: {
                auto s = add_state(), a = add_state();
                auto x = build(*n.children[0]);
                eps[s].push_back(x.start);
                eps[s].push_back(a);
                eps[x.accept].push_back(x.start);
                eps[x.accept].push_back(a);
                return {s, a};
            }
            }
            throw gcs::NonExhaustiveSwitch{};
        }
    };

    // Epsilon-elimination: keep transitions on the source's epsilon-closure and
    // mark a state accepting if its closure contains the single accept state.
    // Then keep only the states reachable from the start, renumbered with the
    // start as 0.
    auto build_nfa(const CoreNode & root) -> gcs::innards::RegexNfa
    {
        ThompsonBuilder builder;
        auto fragment = builder.build(root);
        auto start = fragment.start, accept = fragment.accept;

        auto closure = [&](long q) -> set<long> {
            set<long> seen{q};
            vector<long> stack{q};
            while (! stack.empty()) {
                auto x = stack.back();
                stack.pop_back();
                for (auto y : builder.eps[x])
                    if (seen.insert(y).second)
                        stack.push_back(y);
            }
            return seen;
        };

        unordered_map<long, long> old_to_new;
        vector<map<Integer, set<long>>> raw_transitions; // indexed by new id, targets are old ids
        vector<char> is_final;
        queue<long> to_visit;

        old_to_new.emplace(start, 0);
        to_visit.push(start);
        while (! to_visit.empty()) {
            auto q = to_visit.front();
            to_visit.pop();

            auto cl = closure(q);
            map<Integer, set<long>> transitions;
            for (auto p : cl)
                for (const auto & [symbol, target] : builder.sym[p]) {
                    transitions[symbol].insert(target);
                    if (old_to_new.emplace(target, static_cast<long>(old_to_new.size())).second)
                        to_visit.push(target);
                }
            raw_transitions.push_back(move(transitions));
            is_final.push_back(cl.contains(accept) ? 1 : 0);
        }

        gcs::innards::RegexNfa nfa;
        nfa.num_states = static_cast<long>(raw_transitions.size());
        nfa.transitions.resize(raw_transitions.size());
        for (size_t i = 0; i < raw_transitions.size(); ++i) {
            for (const auto & [symbol, targets] : raw_transitions[i]) {
                auto & destination = nfa.transitions[i][symbol];
                for (auto target : targets)
                    destination.insert(old_to_new.at(target));
            }
            if (is_final[i])
                nfa.final_states.push_back(static_cast<long>(i));
        }
        return nfa;
    }

    // ---- Reference matcher -------------------------------------------------
    //
    // Returns every index j such that node matches sequence[start, j).
    auto match_ends(const CoreNode & node, const vector<Integer> & sequence, size_t start) -> set<size_t>
    {
        switch (node.op) {
            using enum Core;
        case Empty:
            return {start};
        case Symbols:
            if (start < sequence.size() && node.symbols.contains(sequence[start]))
                return {start + 1};
            return {};
        case Concat: {
            set<size_t> ends;
            for (auto mid : match_ends(*node.children[0], sequence, start))
                for (auto end : match_ends(*node.children[1], sequence, mid))
                    ends.insert(end);
            return ends;
        }
        case Union: {
            auto ends = match_ends(*node.children[0], sequence, start);
            for (auto end : match_ends(*node.children[1], sequence, start))
                ends.insert(end);
            return ends;
        }
        case Star: {
            set<size_t> reachable{start};
            vector<size_t> stack{start};
            while (! stack.empty()) {
                auto i = stack.back();
                stack.pop_back();
                for (auto j : match_ends(*node.children[0], sequence, i))
                    if (reachable.insert(j).second)
                        stack.push_back(j);
            }
            return reachable;
        }
        }
        throw gcs::NonExhaustiveSwitch{};
    }
}

auto gcs::innards::regex_to_nfa(const string & regex, const vector<Integer> & alphabet) -> RegexNfa
{
    set<Integer> alphabet_set(alphabet.begin(), alphabet.end());
    auto root = parse_regex(regex, alphabet_set);
    return build_nfa(*root);
}

auto gcs::innards::regex_reference_accepts(const string & regex, const vector<Integer> & alphabet,
    const vector<Integer> & sequence) -> bool
{
    set<Integer> alphabet_set(alphabet.begin(), alphabet.end());
    auto root = parse_regex(regex, alphabet_set);
    return match_ends(*root, sequence, 0).contains(sequence.size());
}
