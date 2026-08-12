#include <gcs/constraints/abs.hh>
#include <gcs/constraints/all_different.hh>
#include <gcs/constraints/all_equal.hh>
#include <gcs/constraints/among/among.hh>
#include <gcs/constraints/at_most_one/at_most_one.hh>
#include <gcs/constraints/bin_packing.hh>
#include <gcs/constraints/circuit.hh>
#include <gcs/constraints/comparison.hh>
#include <gcs/constraints/count.hh>
#include <gcs/constraints/cumulative.hh>
#include <gcs/constraints/difference/difference_constraints.hh>
#include <gcs/constraints/disjunctive.hh>
#include <gcs/constraints/disjunctive_2d.hh>
#include <gcs/constraints/divide.hh>
#include <gcs/constraints/element.hh>
#include <gcs/constraints/equals.hh>
#include <gcs/constraints/global_cardinality.hh>
#include <gcs/constraints/in.hh>
#include <gcs/constraints/increasing.hh>
#include <gcs/constraints/inverse.hh>
#include <gcs/constraints/knapsack/knapsack.hh>
#include <gcs/constraints/lex.hh>
#include <gcs/constraints/lex_smart_table.hh>
#include <gcs/constraints/linear/linear_equality.hh>
#include <gcs/constraints/linear/linear_inequality.hh>
#include <gcs/constraints/logical.hh>
#include <gcs/constraints/mdd.hh>
#include <gcs/constraints/min_distance.hh>
#include <gcs/constraints/min_max.hh>
#include <gcs/constraints/minus.hh>
#include <gcs/constraints/modulus.hh>
#include <gcs/constraints/multiply.hh>
#include <gcs/constraints/n_value.hh>
#include <gcs/constraints/nogoods/nogoods.hh>
#include <gcs/constraints/parity.hh>
#include <gcs/constraints/plus.hh>
#include <gcs/constraints/power.hh>
#include <gcs/constraints/regular/regular.hh>
#include <gcs/constraints/seq_precede_chain/seq_precede_chain.hh>
#include <gcs/constraints/smart_table/smart_table.hh>
#include <gcs/constraints/sort.hh>
#include <gcs/constraints/table/negative_table.hh>
#include <gcs/constraints/table/table.hh>
#include <gcs/constraints/value_precede/value_precede.hh>
#include <gcs/expression.hh>
#include <gcs/innards/literal.hh>
#include <gcs/innards/s_expr.hh>
#include <gcs/problem.hh>
#include <gcs/reification.hh>
#include <gcs/scp_reader.hh>
#include <gcs/variable_condition.hh>

#include <charconv>
#include <optional>
#include <span>
#include <unordered_map>
#include <utility>
#include <vector>

using std::map;
using std::move;
using std::nullopt;
using std::optional;
using std::span;
using std::string;
using std::string_view;
using std::unordered_map;
using std::vector;

using namespace gcs;
using namespace gcs::innards;

ScpReadError::ScpReadError(const string & w) : MessageException("Error reading .scp: " + w)
{
}

ScpUnsupportedConstraintError::ScpUnsupportedConstraintError(const string & op) :
    ScpReadError("unsupported constraint operator '" + op + "'"), _operator_name(op)
{
}

namespace
{
    // The atom's value if it is an integer, nullopt if it is some other atom.
    // Callers that must have an integer use as_integer; the objective needs to
    // tell "an integer constant" from "a name", without either being an error.
    auto optional_integer(const SExpr & e) -> optional<Integer>
    {
        const auto & a = e.as_atom();
        long long value;
        auto [ptr, ec] = std::from_chars(a.data(), a.data() + a.size(), value);
        if (ec != std::errc{} || ptr != a.data() + a.size())
            return nullopt;
        return Integer{value};
    }

    auto as_integer(const SExpr & e) -> Integer
    {
        if (auto value = optional_integer(e))
            return *value;
        throw ScpReadError{"expected an integer, got '" + e.as_atom() + "'"};
    }

    // The children of a list term, or a clear error if `e` is an atom. `what`
    // is taken by value (not const string &) so the -Wdangling-reference
    // heuristic doesn't flag the returned reference, which is into `e`.
    auto children_of(const SExpr & e, const char * what) -> const vector<SExpr> &
    {
        if (! e.is_list())
            throw ScpReadError{string{"expected a list for "} + what};
        return e.as_list();
    }

    // A top-level section is `(<tag> item...)`. Check the tag -- both it and the
    // section's position in the top-level list are fixed, so a missing,
    // misspelled or reordered section is an error here rather than something to
    // hunt for -- and hand back the items after it. The span points into `e`,
    // which outlives every use.
    auto section_items(const SExpr & e, const char * tag) -> span<const SExpr>
    {
        const auto & parts = children_of(e, tag);
        if (parts.empty() || ! parts[0].is_atom() || parts[0].as_atom() != tag)
            throw ScpReadError{string{"expected a ("} + tag + " ...) section"};
        return span<const SExpr>{parts}.subspan(1);
    }

    // Resolve an argument to a variable: a declared name, or an integer constant
    // mapped to a ConstantIntegerVariableID. Anywhere a variable name may appear
    // in a .scp, a constant integer may appear in its place.
    auto resolve_variable(const map<string, IntegerVariableID> & variables, const SExpr & e) -> IntegerVariableID
    {
        const auto & a = e.as_atom();
        if (auto it = variables.find(a); it != variables.end())
            return it->second;
        return constant_variable(as_integer(e));
    }

    // Resolve a list term to a vector of variables (the common case).
    auto resolve_variable_list(const map<string, IntegerVariableID> & variables, const SExpr & list, const char * what) -> vector<IntegerVariableID>
    {
        vector<IntegerVariableID> result;
        for (const auto & e : children_of(list, what))
            result.push_back(resolve_variable(variables, e));
        return result;
    }

    // Resolve a list term to a vector of integer constants.
    auto resolve_integer_list(const SExpr & list, const char * what) -> vector<Integer>
    {
        vector<Integer> result;
        for (const auto & e : children_of(list, what))
            result.push_back(as_integer(e));
        return result;
    }

    // If `s` is the form Problem auto-generates for unnamed constraints,
    // `_<digits>`, return that number; otherwise nullopt.
    auto auto_number_of(const string & s) -> std::optional<unsigned long long>
    {
        if (s.size() < 2 || s[0] != '_')
            return std::nullopt;
        for (auto i = s.begin() + 1; i != s.end(); ++i)
            if (*i < '0' || *i > '9')
                return std::nullopt;
        unsigned long long number;
        auto [ptr, ec] = std::from_chars(s.data() + 1, s.data() + s.size(), number);
        if (ec != std::errc{})
            throw ScpReadError{"constraint label '" + s + "' is out of range"};
        return number;
    }

    auto post_constraint(Problem & problem, const Constraint & constraint, const string & label) -> void
    {
        // `_N` is reserved (post_named rejects it); reproduce it via
        // post_autonumbered, which validates the number lines up. Anything else
        // is a genuine name.
        if (auto number = auto_number_of(label))
            problem.post_autonumbered(constraint, *number);
        else
            problem.post_named(constraint, label);
    }

    // A reification condition is the triple (variable op value), where op is the
    // s_expr_name_of(VariableConditionOperator) spelling.
    auto resolve_condition(const map<string, IntegerVariableID> & variables, const SExpr & triple) -> IntegerVariableCondition
    {
        const auto & parts = children_of(triple, "a reification condition");
        if (parts.size() != 3)
            throw ScpReadError{"a reification condition must be (variable op value)"};
        auto var = resolve_variable(variables, parts[0]);
        const auto & op = parts[1].as_atom();
        auto value = as_integer(parts[2]);
        using enum VariableConditionOperator;
        // cake_pb_cp's condition operators are symbols.
        if (op == "=")
            return {var, Equal, value};
        if (op == "!=")
            return {var, NotEqual, value};
        if (op == ">=")
            return {var, GreaterEqual, value};
        if (op == "<")
            return {var, Less, value};
        throw ScpReadError{"unknown reification-condition operator '" + op + "'"};
    }

    // A logical operand, as the and / or / parity forms write them: a
    // reification tuple (variable op value), which cake reads as the reified
    // test. Constants appear as a tuple over the constant (e.g. (1 >= 1)); the
    // bare atoms 1 / 0 are also accepted for the static literals. See
    // reify_tuple_term in cake_truthiness.
    auto resolve_literal(const map<string, IntegerVariableID> & variables, const SExpr & term) -> innards::Literal
    {
        if (term.is_atom()) {
            if (term.as_atom() == "1")
                return innards::TrueLiteral{};
            if (term.as_atom() == "0")
                return innards::FalseLiteral{};
            throw ScpReadError{"a literal must be 1, 0, or a (variable op value) triple"};
        }
        return resolve_condition(variables, term);
    }

    auto resolve_literal_list(const map<string, IntegerVariableID> & variables, const SExpr & list_term, const string & what) -> innards::Literals
    {
        innards::Literals result;
        for (const auto & t : children_of(list_term, what.c_str()))
            result.push_back(resolve_literal(variables, t));
        return result;
    }

    // For the equals-style families (equals / not_equals and their lin_
    // counterparts): map a keyword's reification suffix to a (condition, flipped)
    // pair. `flipped` is the cosmetic not-equals-iff flag (ReifiedEquals::_neq /
    // ReifiedLinearEquality::_flipped_cond). `cond_term` is only read when the
    // form is reified (the (variable op value) triple).
    auto equality_reification(bool not_equals, bool iff, bool half, const map<string, IntegerVariableID> & variables, const SExpr & cond_term)
        -> std::pair<ReificationCondition, bool>
    {
        // The not_equals_iff keyword carries the negation (cond <=> operands
        // differ), and the flipped representation stores the equality's
        // condition, so reading one means negating the written condition --
        // mirroring the writers, which un-negate the stored condition. The
        // half-reified NotIf stores the condition as written.
        if (iff)
            return {not_equals ? ReificationCondition{reif::Iff{! resolve_condition(variables, cond_term)}}
                               : ReificationCondition{reif::Iff{resolve_condition(variables, cond_term)}},
                not_equals};
        if (half)
            return {not_equals ? ReificationCondition{reif::NotIf{resolve_condition(variables, cond_term)}}
                               : ReificationCondition{reif::If{resolve_condition(variables, cond_term)}},
                false};
        return {not_equals ? ReificationCondition{reif::MustNotHold{}} : ReificationCondition{reif::MustHold{}}, false};
    }

    // The comparison family: (label <less|greater>_<than|equal>[_if|_iff]
    // [(cond)] v1 v2), in cake_pb_cp's names. The keyword carries the swapped /
    // or-equal / reification flags that the general
    // ReifiedCompareLessThanOrMaybeEqual constructor takes directly, so this
    // reconstructs exactly the object the writer serialised.
    auto read_comparison(Problem & problem, const map<string, IntegerVariableID> & variables, const string & op, const vector<SExpr> & terms,
        const string & label) -> void
    {
        bool vars_swapped = op.starts_with("greater_");
        string rest = op.substr(vars_swapped ? sizeof("greater_") - 1 : sizeof("less_") - 1);
        bool or_equal = rest.starts_with("equal");
        rest = rest.substr(or_equal ? sizeof("equal") - 1 : sizeof("than") - 1);
        // `rest` is now "" (unconditional), "_if" (half-reified) or "_iff".

        ReificationCondition cond = reif::MustHold{};
        std::size_t v1_index = 2;
        if (rest.empty()) {
            if (terms.size() != 4)
                throw ScpReadError{"comparison '" + op + "' is (label op v1 v2)"};
        }
        else {
            if (terms.size() != 5)
                throw ScpReadError{"reified comparison '" + op + "' is (label op (cond) v1 v2)"};
            auto condition = resolve_condition(variables, terms[2]);
            if (rest == "_if")
                cond = reif::If{condition};
            else if (rest == "_iff")
                cond = reif::Iff{condition};
            else
                throw ScpReadError{"unknown comparison '" + op + "'"};
            v1_index = 3;
        }

        // "less A B" means A <op> B; "greater A B" means A >op B, i.e. B <op A.
        // The base constructor enforces (first) <op> (second), so reverse the
        // operands for the greater form to recover that.
        auto first = resolve_variable(variables, terms[v1_index]);
        auto second = resolve_variable(variables, terms[v1_index + 1]);
        post_constraint(problem,
            ReifiedCompareLessThanOrMaybeEqual{vars_swapped ? second : first, vars_swapped ? first : second, cond, or_equal, vars_swapped}, label);
    }

    // The lexicographic family: (label lex_<less|greater>_<than|equal>[_if|_iff]
    // [(cond)] (a...) (b...)), in cake_pb_cp's names -- the same comparison
    // keywords as the scalar family, but over two lists. The keyword carries the
    // swapped / or-equal / reification flags exactly as the general
    // LexCompareGreaterThanOrMaybeEqual constructor takes them, so this
    // reconstructs the object the writer serialised. (cake supports the plain,
    // _if and _iff forms; the writer can also emit _not / _not_if for the
    // MustNotHold / NotIf reifications, which round-trip here but have no cake
    // counterpart, so they are not exercised by the verified chain.)
    auto read_lex(Problem & problem, const map<string, IntegerVariableID> & variables, const string & op, const vector<SExpr> & terms,
        const string & label) -> void
    {
        string rest = op.substr(sizeof("lex_") - 1);
        bool vars_swapped = ! rest.starts_with("greater_");
        rest = rest.substr(vars_swapped ? sizeof("less_") - 1 : sizeof("greater_") - 1);
        bool or_equal = rest.starts_with("equal");
        rest = rest.substr(or_equal ? sizeof("equal") - 1 : sizeof("than") - 1);
        // `rest` is now "" / "_not" (no condition term) or "_if" / "_iff" /
        // "_not_if" (a (cond) term at terms[2]).

        ReificationCondition cond = reif::MustHold{};
        std::size_t list1_index = 2;
        if (rest.empty()) {
            if (terms.size() != 4)
                throw ScpReadError{"lex '" + op + "' is (label op (a...) (b...))"};
        }
        else if (rest == "_not") {
            cond = reif::MustNotHold{};
            if (terms.size() != 4)
                throw ScpReadError{"lex '" + op + "' is (label op (a...) (b...))"};
        }
        else {
            if (terms.size() != 5)
                throw ScpReadError{"reified lex '" + op + "' is (label op (cond) (a...) (b...))"};
            auto condition = resolve_condition(variables, terms[2]);
            if (rest == "_if")
                cond = reif::If{condition};
            else if (rest == "_iff")
                cond = reif::Iff{condition};
            else if (rest == "_not_if")
                cond = reif::NotIf{condition};
            else
                throw ScpReadError{"unknown lex comparison '" + op + "'"};
            list1_index = 3;
        }

        // The writer emits the "greater" form unswapped (a = vars_1, b = vars_2)
        // and the "less" form swapped (a = vars_2, b = vars_1), so undo that to
        // recover the constructor's (vars_1, vars_2), mirroring read_comparison.
        auto first = resolve_variable_list(variables, terms[list1_index], "the first lex list");
        auto second = resolve_variable_list(variables, terms[list1_index + 1], "the second lex list");
        post_constraint(problem,
            LexCompareGreaterThanOrMaybeEqual{vars_swapped ? second : first, vars_swapped ? first : second, cond, or_equal, vars_swapped}, label);
    }

    // The linear family: (label lin_<equals|not_equals|lin_less_equal>[_if|_iff]
    // [(cond)] (c1 v1 c2 v2 ...) value). The keyword selects the constraint and
    // its reification, matching the general ReifiedLinear* constructors. (The
    // .scp does not record the GAC flag, so it defaults off; that affects
    // propagation strength, not the solution set or the written .scp.)
    auto read_linear(Problem & problem, const map<string, IntegerVariableID> & variables, const string & op, const vector<SExpr> & terms,
        const string & label) -> void
    {
        bool iff = op.ends_with("_iff");
        bool half = ! iff && op.ends_with("_if");
        bool reified = iff || half;

        if (terms.size() != (reified ? 5u : 4u))
            throw ScpReadError{"linear constraint '" + op + "' has the wrong number of parts"};

        const auto & pairs = children_of(terms[reified ? 3 : 2], "the linear coefficient/variable list");
        if (pairs.size() % 2 != 0)
            throw ScpReadError{"the linear coefficient/variable list must alternate coefficient and variable"};
        WeightedSum coeff_vars;
        for (std::size_t i = 0; i + 1 < pairs.size(); i += 2)
            coeff_vars += as_integer(pairs[i]) * resolve_variable(variables, pairs[i + 1]);
        auto value = as_integer(terms[reified ? 4 : 3]);

        auto condition = [&] { return resolve_condition(variables, terms[2]); };

        if (op.starts_with("lin_less_equal")) {
            ReificationCondition cond = reif::MustHold{};
            if (iff)
                cond = reif::Iff{condition()};
            else if (half)
                cond = reif::If{condition()};
            post_constraint(problem, ReifiedLinearInequality{std::move(coeff_vars), value, cond}, label);
            return;
        }

        // Equality family: lin_equals* and lin_not_equals*.
        auto [cond, flipped_cond] = equality_reification(op.starts_with("lin_not_equals"), iff, half, variables, terms[2]);
        // Consistency isn't recorded in the .scp; reconstruct with the default (BC).
        post_constraint(problem, ReifiedLinearEquality{std::move(coeff_vars), value, cond, flipped_cond}, label);
    }

    // The equals family: (label <equals|not_equals>[_if|_iff] [(cond)] v1 v2),
    // reconstructed via the general ReifiedEquals constructor.
    auto read_equals(Problem & problem, const map<string, IntegerVariableID> & variables, const string & op, const vector<SExpr> & terms,
        const string & label) -> void
    {
        bool iff = op.ends_with("_iff");
        bool half = ! iff && op.ends_with("_if");
        bool reified = iff || half;

        if (terms.size() != (reified ? 5u : 4u))
            throw ScpReadError{"equals constraint '" + op + "' is (label op [(cond)] v1 v2)"};
        std::size_t v1_index = reified ? 3 : 2;

        auto [cond, neq] = equality_reification(op.starts_with("not_equals"), iff, half, variables, terms[2]);
        post_constraint(
            problem, ReifiedEquals{resolve_variable(variables, terms[v1_index]), resolve_variable(variables, terms[v1_index + 1]), cond, neq}, label);
    }

    // (label regular (X1 ... Xn) nstates ((edges-of-0) (edges-of-1) ...)
    // (f1 ... fk)): the Xi spell a word the automaton accepts. The automaton has
    // `nstates` states (0-based, starting in state 0); the third argument lists,
    // per state in order, that state's outgoing edges, each an (symbol target)
    // pair meaning "reading `symbol` moves to state `target`"; (f1 ... fk) are
    // the accepting states. This is cake_pb_cp's shape, and the inverse of the
    // writer. cake supports non-deterministic automata, but Regular has no public
    // multi-target constructor, so the reader rebuilds deterministic automata
    // only -- two edges on the same symbol in one state are rejected.
    auto read_regular(Problem & problem, const map<string, IntegerVariableID> & variables, const vector<SExpr> & terms, const string & label) -> void
    {
        if (terms.size() != 6)
            throw ScpReadError{"regular is (label regular (vars...) nstates ((edges)...) (finals...))"};
        auto vars = resolve_variable_list(variables, terms[2], "the regular variable list");
        auto num_states = static_cast<long>(as_integer(terms[3]).raw_value);
        const auto & per_state = children_of(terms[4], "the regular per-state edge lists");
        vector<unordered_map<Integer, long>> transitions(per_state.size());
        for (std::size_t q = 0; q < per_state.size(); ++q)
            for (const auto & edge : children_of(per_state[q], "a regular state's edge list")) {
                const auto & pair = children_of(edge, "a regular edge");
                if (pair.size() != 2)
                    throw ScpReadError{"a regular edge must be (symbol target)"};
                auto target = static_cast<long>(as_integer(pair[1]).raw_value);
                if (! transitions[q].emplace(as_integer(pair[0]), target).second)
                    throw ScpReadError{"the .scp reader rebuilds deterministic automata only: a state has two edges on the same symbol"};
            }
        vector<long> finals;
        for (const auto & f : children_of(terms[5], "the regular final-state list"))
            finals.push_back(static_cast<long>(as_integer(f).raw_value));
        post_constraint(problem, Regular{move(vars), num_states, move(transitions), move(finals)}, label);
    }

    // Read a (negative_)table tuple list. An entry is an integer or `*` (a
    // wildcard matching any value), exactly cake_pb_cp's shape. A wildcard-free
    // table is built as SimpleTuples (the plain form its writer emits, so it
    // round-trips); any wildcard switches the whole table to WildcardTuples.
    auto read_extensional_tuples(const SExpr & tuple_list, bool & any_wildcard, SimpleTuples & simple_tuples, WildcardTuples & wildcard_tuples)
        -> void
    {
        for (const auto & tuple_term : children_of(tuple_list, "the table tuple list")) {
            vector<IntegerOrWildcard> wildcard_row;
            vector<Integer> simple_row;
            for (const auto & entry : children_of(tuple_term, "a table tuple")) {
                if (entry.as_atom() == "*") {
                    any_wildcard = true;
                    wildcard_row.emplace_back(Wildcard{});
                }
                else {
                    auto value = as_integer(entry);
                    wildcard_row.emplace_back(value);
                    simple_row.push_back(value);
                }
            }
            wildcard_tuples.push_back(move(wildcard_row));
            simple_tuples.push_back(move(simple_row));
        }
    }

    auto read_table(Problem & problem, const map<string, IntegerVariableID> & variables, const vector<SExpr> & terms, const string & label) -> void
    {
        // (label table ((e...) (e...) ...) (vars...)): the variables must take one
        // of the listed tuples.
        if (terms.size() != 4)
            throw ScpReadError{"table is (label table (tuples...) (vars...))"};
        bool any_wildcard = false;
        SimpleTuples simple_tuples;
        WildcardTuples wildcard_tuples;
        read_extensional_tuples(terms[2], any_wildcard, simple_tuples, wildcard_tuples);
        auto vars = resolve_variable_list(variables, terms[3], "the table variable list");
        if (any_wildcard)
            post_constraint(problem, Table{move(vars), move(wildcard_tuples)}, label);
        else
            post_constraint(problem, Table{move(vars), move(simple_tuples)}, label);
    }

    auto read_negative_table(Problem & problem, const map<string, IntegerVariableID> & variables, const vector<SExpr> & terms, const string & label)
        -> void
    {
        // (label negative_table ((e...) (e...) ...) (vars...)): the variables must
        // not take any of the listed tuples.
        if (terms.size() != 4)
            throw ScpReadError{"negative_table is (label negative_table (tuples...) (vars...))"};
        bool any_wildcard = false;
        SimpleTuples simple_tuples;
        WildcardTuples wildcard_tuples;
        read_extensional_tuples(terms[2], any_wildcard, simple_tuples, wildcard_tuples);
        auto vars = resolve_variable_list(variables, terms[3], "the negative_table variable list");
        if (any_wildcard)
            post_constraint(problem, NegativeTable{move(vars), move(wildcard_tuples)}, label);
        else
            post_constraint(problem, NegativeTable{move(vars), move(simple_tuples)}, label);
    }

    // Map a smart-table comparison op to the matching SmartTable entry. Templated
    // over the operand so it serves both binary (var op var) and unary-value
    // (var op const) entries: SmartTable's helpers are overloaded on the operand.
    template <typename Operand_>
    auto smart_table_comparison(const IntegerVariableID & var, const string & op, const Operand_ & operand) -> SmartEntry
    {
        if (op == "<")
            return SmartTable::less_than(var, operand);
        if (op == "<=")
            return SmartTable::less_than_equal(var, operand);
        if (op == "=")
            return SmartTable::equals(var, operand);
        if (op == "!=")
            return SmartTable::not_equals(var, operand);
        if (op == ">")
            return SmartTable::greater_than(var, operand);
        if (op == ">=")
            return SmartTable::greater_than_equal(var, operand);
        throw ScpReadError{"unknown smart_table comparison '" + op + "'"};
    }

    auto read_smart_table(Problem & problem, const map<string, IntegerVariableID> & variables, const vector<SExpr> & terms, const string & label)
        -> void
    {
        // (label smart_table ((entry...) (entry...) ...) (vars...)): a disjunction
        // over rows, each row a conjunction of entries. An entry is (v1 op v2)
        // (binary), (v op c) (unary value), or (v in|notin (c...)) (unary set),
        // with op one of < <= = != > >=. cake_pb_cp parses exactly this. A
        // comparison's operand is a binary entry when it names a declared variable
        // and a unary-value entry when it is an integer constant.
        if (terms.size() != 4)
            throw ScpReadError{"smart_table is (label smart_table (rows...) (vars...))"};
        SmartTuples tuples;
        for (const auto & row_term : children_of(terms[2], "the smart_table rows")) {
            vector<SmartEntry> row;
            for (const auto & entry_term : children_of(row_term, "a smart_table row")) {
                const auto & entry = children_of(entry_term, "a smart_table entry");
                if (entry.size() != 3)
                    throw ScpReadError{"a smart_table entry is (var op operand)"};
                auto var = resolve_variable(variables, entry[0]);
                const auto & op = entry[1].as_atom();
                if (op == "in" || op == "notin") {
                    vector<Integer> values;
                    for (const auto & v : children_of(entry[2], "a smart_table value set"))
                        values.push_back(as_integer(v));
                    row.push_back(op == "in" ? SmartTable::in_set(var, move(values)) : SmartTable::not_in_set(var, move(values)));
                }
                else if (auto it = variables.find(entry[2].as_atom()); it != variables.end())
                    row.push_back(smart_table_comparison(var, op, it->second));
                else
                    row.push_back(smart_table_comparison(var, op, as_integer(entry[2])));
            }
            tuples.push_back(move(row));
        }
        auto vars = resolve_variable_list(variables, terms[3], "the smart_table variable list");
        post_constraint(problem, SmartTable{move(vars), move(tuples)}, label);
    }

    auto read_all_different_except(
        Problem & problem, const map<string, IntegerVariableID> & variables, const vector<SExpr> & terms, const string & label) -> void
    {
        // (label all_different_except (vars...) (excluded...)): the variables take
        // pairwise distinct values, except that any number may take an excluded value.
        if (terms.size() != 4)
            throw ScpReadError{"all_different_except is (label all_different_except (vars...) (excluded...))"};
        auto vars = resolve_variable_list(variables, terms[2], "the all_different_except variable list");
        auto excluded = resolve_integer_list(terms[3], "the all_different_except excluded list");
        post_constraint(problem, AllDifferentExcept{move(vars), move(excluded)}, label);
    }

    auto read_symmetric_all_different(
        Problem & problem, const map<string, IntegerVariableID> & variables, const vector<SExpr> & terms, const string & label) -> void
    {
        // (label symmetric_all_different (vars...) start): an all_different whose
        // assignment is an involution -- if var i takes value start + j then var j
        // takes value start + i.
        if (terms.size() != 4)
            throw ScpReadError{"symmetric_all_different is (label symmetric_all_different (vars...) start)"};
        auto vars = resolve_variable_list(variables, terms[2], "the symmetric_all_different variable list");
        post_constraint(problem, SymmetricAllDifferent{move(vars), as_integer(terms[3])}, label);
    }

    auto read_at_most_one(Problem & problem, const map<string, IntegerVariableID> & variables, const string & op, const vector<SExpr> & terms,
        const string & label) -> void
    {
        // (label at_most_one (vars...) val): at most one of the variables takes the
        // value val (itself a variable or a constant). `at_most_one_smart_table`
        // is the same constraint reached through a SmartTable decomposition; it
        // keeps its own keyword (which is also cake's spelling) and rebuilds as
        // the matching class, so the term round-trips. It does not chain: cake's
        // rule wants an integer where this writes a variable, and the SmartTable
        // desugaring is a much larger OPB than cake's rows.
        if (terms.size() != 4)
            throw ScpReadError{op + " is (label " + op + " (vars...) val)"};
        auto vars = resolve_variable_list(variables, terms[2], ("the " + op + " variable list").c_str());
        auto val = resolve_variable(variables, terms[3]);
        if (op == "at_most_one_smart_table")
            post_constraint(problem, AtMostOneSmartTable{move(vars), val}, label);
        else
            post_constraint(problem, AtMostOne{move(vars), val}, label);
    }

    auto read_sort(Problem & problem, const map<string, IntegerVariableID> & variables, const vector<SExpr> & terms, const string & label) -> void
    {
        // (label sort (xs...) (ys...)): ys is xs sorted into non-decreasing order.
        if (terms.size() != 4)
            throw ScpReadError{"sort is (label sort (xs...) (ys...))"};
        auto xs = resolve_variable_list(variables, terms[2], "the sort input list");
        auto ys = resolve_variable_list(variables, terms[3], "the sort output list");
        post_constraint(problem, Sort{move(xs), move(ys)}, label);
    }

    auto read_arg_sort(Problem & problem, const map<string, IntegerVariableID> & variables, const vector<SExpr> & terms, const string & label) -> void
    {
        // (label arg_sort (xs...) (ps...) offset): ps is the (stable) argsort
        // permutation of xs, with positions starting from offset.
        if (terms.size() != 5)
            throw ScpReadError{"arg_sort is (label arg_sort (xs...) (ps...) offset)"};
        auto xs = resolve_variable_list(variables, terms[2], "the arg_sort input list");
        auto ps = resolve_variable_list(variables, terms[3], "the arg_sort permutation list");
        post_constraint(problem, ArgSort{move(xs), move(ps), as_integer(terms[4])}, label);
    }

    auto read_among(Problem & problem, const map<string, IntegerVariableID> & variables, const vector<SExpr> & terms, const string & label) -> void
    {
        // (label among (vars...) (values...) how_many): exactly how_many of the
        // variables take a value from the values-of-interest set.
        if (terms.size() != 5)
            throw ScpReadError{"among is (label among (vars...) (values...) how_many)"};
        auto vars = resolve_variable_list(variables, terms[2], "the among variable list");
        auto values = resolve_integer_list(terms[3], "the among values-of-interest list");
        post_constraint(problem, Among{move(vars), values, resolve_variable(variables, terms[4])}, label);
    }

    auto read_value_precede(Problem & problem, const map<string, IntegerVariableID> & variables, const vector<SExpr> & terms, const string & label)
        -> void
    {
        // (label value_precede (chain...) (vars...)): in the sequence of variables,
        // the first occurrence of chain[k] precedes the first occurrence of
        // chain[k+1], for each consecutive pair in the value chain.
        if (terms.size() != 4)
            throw ScpReadError{"value_precede is (label value_precede (chain...) (vars...))"};
        auto chain = resolve_integer_list(terms[2], "the value_precede chain");
        auto vars = resolve_variable_list(variables, terms[3], "the value_precede variable list");
        post_constraint(problem, ValuePrecede{move(chain), move(vars)}, label);
    }

    auto read_seq_precede_chain(
        Problem & problem, const map<string, IntegerVariableID> & variables, const vector<SExpr> & terms, const string & label) -> void
    {
        // (label seq_precede_chain (vars...)): the sequence-precedence chain, value
        // v + 1 may only appear after value v has already appeared.
        if (terms.size() != 3)
            throw ScpReadError{"seq_precede_chain is (label seq_precede_chain (vars...))"};
        post_constraint(problem, SeqPrecedeChain{resolve_variable_list(variables, terms[2], "the seq_precede_chain variable list")}, label);
    }

    auto read_difference(Problem & problem, const map<string, IntegerVariableID> & variables, const vector<SExpr> & terms, const string & label)
        -> void
    {
        // (label difference ((x y d [(cond op value)]) ...)): one edge per
        // difference constraint x - y <= d, propagated as a system rather than
        // edge by edge. A half-reified edge carries its condition as a fourth
        // element, which the writer omits entirely for an unconditional edge, so
        // an unreified system's term is the three-element form throughout.
        if (terms.size() != 3)
            throw ScpReadError{"difference is (label difference ((x y d [cond]) ...))"};
        vector<DifferenceEdge> edges;
        for (const auto & edge_term : children_of(terms[2], "the difference edge list")) {
            const auto & parts = children_of(edge_term, "a difference edge");
            if (parts.size() != 3 && parts.size() != 4)
                throw ScpReadError{"a difference edge must be (x y d) or (x y d cond)"};
            DifferenceEdge edge{resolve_variable(variables, parts[0]), resolve_variable(variables, parts[1]), as_integer(parts[2]), nullopt};
            if (parts.size() == 4)
                edge.cond = resolve_condition(variables, parts[3]);
            edges.push_back(move(edge));
        }
        post_constraint(problem, DifferenceConstraints{move(edges)}, label);
    }

    auto read_bin_packing(Problem & problem, const map<string, IntegerVariableID> & variables, const vector<SExpr> & terms, const string & label)
        -> void
    {
        // (label binpacking (items...) (sizes...) loads (loads...)) or
        // (label binpacking (items...) (sizes...) capacities (caps...)): item i
        // has constant size sizes[i] and goes in bin items[i]. The tagged fifth
        // term picks the form: `loads` gives one load *variable* per bin (each
        // exactly the total size in that bin), `capacities` one constant upper
        // bound per bin. cake_pb_cp has no binpacking rule, so this shape is
        // ours; the tag is what keeps the two forms apart, since both trailing
        // lists are per-bin and the same length.
        if (terms.size() != 6)
            throw ScpReadError{"binpacking is (label binpacking (items...) (sizes...) loads|capacities (per-bin...))"};
        auto items = resolve_variable_list(variables, terms[2], "the binpacking item list");
        auto sizes = resolve_integer_list(terms[3], "the binpacking size list");
        const auto & form = terms[4].as_atom();
        if (form == "loads")
            post_constraint(
                problem, BinPacking{move(items), move(sizes), resolve_variable_list(variables, terms[5], "the binpacking load list")}, label);
        else if (form == "capacities")
            post_constraint(problem, BinPacking{move(items), move(sizes), resolve_integer_list(terms[5], "the binpacking capacity list")}, label);
        else
            throw ScpReadError{"binpacking's third argument must be the tag `loads` or `capacities`, not '" + form + "'"};
    }

    // (label mdd (X1 ... Xn) (n0 n1 ... nn) ((layer-0-nodes) ...) (t1 ... tk)):
    // a layered DAG read left to right, one layer per variable. `nodes_per_layer`
    // has n + 1 entries (the node count at each layer boundary, layer 0 being the
    // single-source root layer); layer i's entry lists, per source node in node
    // order, that node's outgoing (symbol target) edges, where `target` indexes
    // into layer i + 1; the trailing list is the accepting nodes of the final
    // layer. Same edge spelling as regular, but per layer rather than shared, and
    // the writer sorts each node's edges so the .scp is byte-stable.
    auto read_mdd(Problem & problem, const map<string, IntegerVariableID> & variables, const vector<SExpr> & terms, const string & label) -> void
    {
        if (terms.size() != 6)
            throw ScpReadError{"mdd is (label mdd (vars...) (nodes-per-layer...) ((layer-edges)...) (accepting...))"};
        auto vars = resolve_variable_list(variables, terms[2], "the mdd variable list");

        vector<long> nodes_per_layer;
        for (const auto & n : children_of(terms[3], "the mdd nodes-per-layer list"))
            nodes_per_layer.push_back(static_cast<long>(as_integer(n).raw_value));

        const auto & layers = children_of(terms[4], "the mdd layer list");
        vector<vector<unordered_map<Integer, long>>> layer_transitions;
        for (const auto & layer : layers) {
            vector<unordered_map<Integer, long>> nodes;
            for (const auto & node : children_of(layer, "an mdd layer's node list")) {
                unordered_map<Integer, long> edges;
                for (const auto & edge : children_of(node, "an mdd node's edge list")) {
                    const auto & pair = children_of(edge, "an mdd edge");
                    if (pair.size() != 2)
                        throw ScpReadError{"an mdd edge must be (symbol target)"};
                    if (! edges.emplace(as_integer(pair[0]), static_cast<long>(as_integer(pair[1]).raw_value)).second)
                        throw ScpReadError{"an mdd node has two edges on the same symbol"};
                }
                nodes.push_back(move(edges));
            }
            layer_transitions.push_back(move(nodes));
        }

        vector<long> accepting;
        for (const auto & t : children_of(terms[5], "the mdd accepting-node list"))
            accepting.push_back(static_cast<long>(as_integer(t).raw_value));

        post_constraint(problem, MDD{move(vars), move(layer_transitions), move(nodes_per_layer), move(accepting)}, label);
    }

    auto resolve_matrix(const SExpr & e, const char * what) -> MinDistance::Matrix
    {
        MinDistance::Matrix matrix;
        for (const auto & row : children_of(e, what))
            matrix.push_back(resolve_integer_list(row, what));
        return matrix;
    }

    auto read_min_distance(Problem & problem, const map<string, IntegerVariableID> & variables, const vector<SExpr> & terms, const string & label)
        -> void
    {
        // (label min_distance (X1 ... Xn) Z ((d...)...) [((r...)...)]): the Xi
        // pick sites, Z is a lower bound on the pairwise distance between the
        // chosen sites, and the square matrix gives the distance between each
        // pair of sites. The optional trailing matrix is the per-pair minimum
        // *requirement*. The propagation strategy is deliberately absent: like
        // the regular variants, the .scp names the constraint, not the
        // propagator, so this reads back at the default strategy.
        if (terms.size() != 5 && terms.size() != 6)
            throw ScpReadError{"min_distance is (label min_distance (vars...) z ((distances...)...) [((requirements...)...)])"};
        auto xs = resolve_variable_list(variables, terms[2], "the min_distance variable list");
        auto z = resolve_variable(variables, terms[3]);
        auto distances = resolve_matrix(terms[4], "the min_distance distance matrix");
        if (terms.size() == 6)
            post_constraint(
                problem, MinDistance{move(xs), z, move(distances), resolve_matrix(terms[5], "the min_distance requirement matrix")}, label);
        else
            post_constraint(problem, MinDistance{move(xs), z, move(distances)}, label);
    }

    auto read_nogoods(Problem & problem, const map<string, IntegerVariableID> & variables, const vector<SExpr> & terms, const string & label) -> void
    {
        // (label nogoods (((V op v) ...) ...)): each inner list is one forbidden
        // conjunction of variable conditions, spelled as the reification triples
        // resolve_condition reads. Only *posted* nogoods appear -- the engine's
        // learned-nogood store is installed directly on the propagators and is
        // empty when the .scp is written, so it contributes nothing here.
        if (terms.size() != 3)
            throw ScpReadError{"nogoods is (label nogoods (((var op value) ...) ...))"};
        vector<Nogood> nogoods;
        for (const auto & nogood_term : children_of(terms[2], "the nogood list")) {
            Nogood nogood;
            for (const auto & condition : children_of(nogood_term, "a nogood"))
                nogood.push_back(resolve_condition(variables, condition));
            nogoods.push_back(move(nogood));
        }
        post_constraint(problem, Nogoods{move(nogoods)}, label);
    }

    auto read_knapsack(Problem & problem, const map<string, IntegerVariableID> & variables, const vector<SExpr> & terms, const string & label) -> void
    {
        // (label knapsack ((coeffs-of-row...) ...) (vars...) (totals...)): a system
        // of linear equalities, one per coefficient row -- row r asserts
        // sum_i coeffs[r][i] * vars[i] == totals[r]. (The classic weight/profit
        // knapsack is the two-row case.)
        if (terms.size() != 5)
            throw ScpReadError{"knapsack is (label knapsack ((coeffs...) ...) (vars...) (totals...))"};
        vector<vector<Integer>> coeffs;
        for (const auto & row : children_of(terms[2], "the knapsack coefficient rows"))
            coeffs.push_back(resolve_integer_list(row, "a knapsack coefficient row"));
        auto vars = resolve_variable_list(variables, terms[3], "the knapsack variable list");
        auto totals = resolve_variable_list(variables, terms[4], "the knapsack totals list");
        post_constraint(problem, Knapsack{move(coeffs), move(vars), move(totals)}, label);
    }

    // An index argument is a (variable offset) pair: the chosen entry is at
    // val(variable) - offset (Element subtracts the offset).
    auto resolve_index_pair(const map<string, IntegerVariableID> & variables, const SExpr & e) -> std::pair<IntegerVariableID, Integer>
    {
        const auto & pair = children_of(e, "an element index");
        if (pair.size() != 2)
            throw ScpReadError{"an element index must be (index offset)"};
        return {resolve_variable(variables, pair[0]), as_integer(pair[1])};
    }

    // An objective from a (prob_type ...) section, before its operand has been
    // resolved: the section is checked before any variable is created (so that
    // a malformed document leaves `problem` untouched), but resolving needs the
    // variables map, which does not exist until afterwards.
    struct ObjectiveSpec
    {
        bool maximize;
        SExpr variable;
    };

    // (prob_type <spec>), where <spec> is the bare atom `decide` or `enumerate`,
    // or the list (minimize var) / (maximize var). Checking this matters even
    // for the bare atoms -- the .scp is a contract with cake_pb_cp, and a spec
    // quietly ignored here is one cake would reject downstream.
    auto check_prob_type(const SExpr & section) -> optional<ObjectiveSpec>
    {
        auto spec = section_items(section, "prob_type");
        if (spec.size() != 1)
            throw ScpReadError{"the prob_type section takes exactly one specification"};

        if (spec[0].is_atom()) {
            const auto & kind = spec[0].as_atom();
            if (kind != "decide" && kind != "enumerate")
                throw ScpReadError{"unknown prob_type '" + kind + "'"};
            return nullopt;
        }

        const auto & parts = children_of(spec[0], "the prob_type specification");
        if (parts.size() != 2 || ! parts[0].is_atom() || (parts[0].as_atom() != "minimize" && parts[0].as_atom() != "maximize"))
            throw ScpReadError{"a prob_type objective is (minimize var) or (maximize var)"};
        if (! parts[1].is_atom())
            throw ScpReadError{"a prob_type objective's variable must be an atom"};
        return ObjectiveSpec{parts[0].as_atom() == "maximize", parts[1]};
    }

    // The objective as a variable to minimise, mirroring what
    // Problem::minimise() / Problem::maximise() would have stored -- so a
    // caller can hand it straight back to Problem::minimise(), and so that
    // reader and writer are inverses.
    auto resolve_objective(const map<string, IntegerVariableID> & variables, const ObjectiveSpec & spec) -> IntegerVariableID
    {
        // The writer renders a constant objective as (minimize 3), so an
        // undeclared atom is legitimate -- but only when it really is an
        // integer. Anything else is a typo, and silently turning it into a
        // constant would optimise something the document never mentioned.
        if (! variables.contains(spec.variable.as_atom()) && ! optional_integer(spec.variable))
            throw ScpReadError{"the prob_type objective names an unknown variable '" + spec.variable.as_atom() + "'"};

        auto variable = resolve_variable(variables, spec.variable);
        return spec.maximize ? -variable : variable;
    }

    auto read_element_2d(Problem & problem, const map<string, IntegerVariableID> & variables, const vector<SExpr> & terms, const string & label)
        -> void
    {
        // (label element_2d ((row...) ...) (i off_i) (j off_j) result): the array is
        // a list of rows, and result = array[val(i) - off_i][val(j) - off_j]. As in
        // the 1-D case, a constant entry is read as a constant variable.
        if (terms.size() != 6)
            throw ScpReadError{"element_2d takes (label element_2d ((row...) ...) (i off) (j off) result)"};
        vector<vector<IntegerVariableID>> array;
        for (const auto & row : children_of(terms[2], "the element_2d array"))
            array.push_back(resolve_variable_list(variables, row, "an element_2d array row"));
        post_constraint(problem,
            Element2D{
                resolve_variable(variables, terms[5]), resolve_index_pair(variables, terms[3]), resolve_index_pair(variables, terms[4]), move(array)},
            label);
    }
}

auto gcs::read_scp(Problem & problem, string_view text) -> ScpModel
{
    auto top = parse_s_expr(text);
    const auto & sections = children_of(top, "the top-level (version variables constraints prob_type) form");
    if (sections.size() != 4)
        throw ScpReadError{"top level must be ((version 1) (variables ...) (constraints ...) (prob_type ...))"};

    // The version comes first so that an incompatible producer is caught before
    // anything else is read. Only 1 is accepted: a different number means a
    // different grammar, and guessing at it would be worse than refusing.
    auto version = section_items(sections[0], "version");
    if (version.size() != 1)
        throw ScpReadError{"the version section must be (version 1)"};
    if (auto number = as_integer(version[0]); number != 1_i)
        throw ScpReadError{"unsupported .scp format version " + number.to_string() + ": this reader only accepts version 1"};

    // Check the trailing section before anything is posted, so a malformed
    // document leaves `problem` untouched rather than half-built. Its objective
    // can only be resolved once the variables exist, below.
    auto objective = check_prob_type(sections[3]);

    map<string, IntegerVariableID> variables;

    // Variables: each declaration is (name lower upper).
    //
    // A variable created without a name is written as `_N`, which is exactly the
    // spelling Problem::check_name() reserves and rejects -- so an anonymous
    // variable has to be recreated anonymously, the same trick post_constraint
    // uses for `_N` constraint labels. Problem numbers anonymous variables in
    // creation order and the writer emits them in that order, so the k-th `_N`
    // declaration must be `_k`; checking that keeps a hand-written document from
    // quietly getting different variables than it names.
    unsigned long long anonymous_so_far = 0;
    for (const auto & decl : section_items(sections[1], "variables")) {
        const auto & parts = children_of(decl, "a variable declaration");
        if (parts.size() != 3)
            throw ScpReadError{"a variable declaration must be (name lower upper)"};
        auto name = parts[0].as_atom();
        auto lower = as_integer(parts[1]), upper = as_integer(parts[2]);

        optional<IntegerVariableID> var;
        if (auto number = auto_number_of(name)) {
            if (*number != ++anonymous_so_far)
                throw ScpReadError{"anonymous variable '" + name + "' is declaration number " + std::to_string(anonymous_so_far) +
                    " among the anonymous ones, so it would be created as '_" + std::to_string(anonymous_so_far) + "'"};
            var = problem.create_integer_variable(lower, upper, nullopt);
        }
        else
            var = problem.create_integer_variable(lower, upper, name);

        if (! variables.emplace(name, *var).second)
            throw ScpReadError{"duplicate variable name '" + name + "'"};
    }

    // Constraints: each is (label operator args...).
    for (const auto & constraint : section_items(sections[2], "constraints")) {
        const auto & terms = children_of(constraint, "a constraint");
        if (terms.size() < 2)
            throw ScpReadError{"a constraint must be (label operator ...)"};
        const auto & label = terms[0].as_atom();
        const auto & op = terms[1].as_atom();

        if (op == "abs") {
            if (terms.size() != 4)
                throw ScpReadError{"abs takes two operands: (label abs v1 v2)"};
            post_constraint(problem, Abs{resolve_variable(variables, terms[2]), resolve_variable(variables, terms[3])}, label);
        }
        else if (op == "all_different") {
            if (terms.size() != 3)
                throw ScpReadError{"all_different takes one list: (label all_different (vars...))"};
            post_constraint(problem, AllDifferent{resolve_variable_list(variables, terms[2], "the all_different variable list")}, label);
        }
        else if (op == "all_equal") {
            if (terms.size() != 3)
                throw ScpReadError{"all_equal takes one list: (label all_equal (vars...))"};
            post_constraint(problem, AllEqual{resolve_variable_list(variables, terms[2], "the all_equal variable list")}, label);
        }
        else if (op == "circuit") {
            if (terms.size() != 3)
                throw ScpReadError{"circuit takes one list: (label circuit (succ...))"};
            post_constraint(problem, Circuit{resolve_variable_list(variables, terms[2], "the circuit successor list")}, label);
        }
        else if (op == "array_min" || op == "array_max") {
            // (label array_min (vars...) result): result = min/max of the array.
            if (terms.size() != 4)
                throw ScpReadError{"the array aggregate takes a list and a result: (label " + op + " (vars...) result)"};
            auto vars = resolve_variable_list(variables, terms[2], "the array aggregate variable list");
            auto result = resolve_variable(variables, terms[3]);
            if (op == "array_min")
                post_constraint(problem, ArrayMin{move(vars), result}, label);
            else
                post_constraint(problem, ArrayMax{move(vars), result}, label);
        }
        else if (op == "boundsglobalcardinality" || op == "boundsglobalcardinalityclosed" || op == "gacglobalcardinality" ||
            op == "gacglobalcardinalityclosed") {
            // (label <kw> (vars...) (values...) (counts...)): for each j, the
            // number of vars equal to values[j] is counts[j]; the `closed` forms
            // additionally confine every var to the cover values. The keyword
            // selects the bounds vs GAC propagator and the closure, matching the
            // writer. cake_pb_cp parses all four under the same keywords.
            if (terms.size() != 5)
                throw ScpReadError{"global cardinality is (label " + op + " (vars...) (values...) (counts...))"};
            auto vars = resolve_variable_list(variables, terms[2], "the global cardinality variable list");
            vector<Integer> values;
            for (const auto & v : children_of(terms[3], "the global cardinality value list"))
                values.push_back(as_integer(v));
            auto counts = resolve_variable_list(variables, terms[4], "the global cardinality count list");
            bool closed = op.ends_with("closed");
            auto level = op.starts_with("gac") ? GlobalCardinalityConsistency{consistency::GAC{}} : GlobalCardinalityConsistency{consistency::BC{}};
            post_constraint(problem, GlobalCardinality{move(vars), move(values), move(counts)}.with_consistency(level).with_closed(closed), label);
        }
        else if (op == "increasing" || op == "strictly_increasing" || op == "decreasing" || op == "strictly_decreasing") {
            // The keyword carries the strict / descending flags that IncreasingChain
            // takes directly (the inverse of how the writer derives the keyword).
            if (terms.size() != 3)
                throw ScpReadError{"the increasing family takes one list: (label " + op + " (vars...))"};
            post_constraint(problem,
                IncreasingChain{resolve_variable_list(variables, terms[2], "the increasing variable list"), op.starts_with("strictly_"),
                    op.ends_with("decreasing")},
                label);
        }
        else if (op == "sort") {
            read_sort(problem, variables, terms, label);
        }
        else if (op == "arg_sort") {
            read_arg_sort(problem, variables, terms, label);
        }
        else if (op == "in") {
            if (terms.size() != 4)
                throw ScpReadError{"in takes a list and a variable: (label in (values...) var)"};
            // The value list is just a list of variables; an integer value is a
            // ConstantIntegerVariableID, which In folds back into a constant. The
            // list comes first, then the variable, matching cake_pb_cp's parser.
            post_constraint(
                problem, In{resolve_variable(variables, terms[3]), resolve_variable_list(variables, terms[2], "the in value list")}, label);
        }
        else if (op == "element") {
            // (label element (X0 ... Xn-1) (index off) result): result = Xs[index - off].
            if (terms.size() != 5)
                throw ScpReadError{"element takes (label element (array...) (index off) result)"};
            const auto & index_pair = children_of(terms[3], "the element index");
            if (index_pair.size() != 2)
                throw ScpReadError{"the element index must be (index off)"};
            // Element takes an ArrayParam, so hand it the array by value: the
            // constraint owns it (no external storage to keep alive).
            post_constraint(problem,
                Element{resolve_variable(variables, terms[4]), std::pair{resolve_variable(variables, index_pair[0]), as_integer(index_pair[1])},
                    resolve_variable_list(variables, terms[2], "the element array")},
                label);
        }
        else if (op == "count") {
            // (label count (X1 ... Xn) value how_many): how_many = #{ i : Xi = value }.
            if (terms.size() != 5)
                throw ScpReadError{"count takes (label count (vars...) value how_many)"};
            post_constraint(problem,
                Count{resolve_variable_list(variables, terms[2], "the count variable list"), resolve_variable(variables, terms[3]),
                    resolve_variable(variables, terms[4])},
                label);
        }
        else if (op == "nvalue") {
            // (label nvalue (X1 ... Xn) Y): Y = #{ distinct values among the Xi }.
            if (terms.size() != 4)
                throw ScpReadError{"nvalue takes (label nvalue (vars...) n_values)"};
            post_constraint(problem,
                NValue{resolve_variable(variables, terms[3]), resolve_variable_list(variables, terms[2], "the nvalue variable list")}, label);
        }
        else if (op == "inverse") {
            // (label inverse ((X...) offx) ((Y...) offy)): X[i]=j+offy <-> Y[j]=i+offx.
            if (terms.size() != 4)
                throw ScpReadError{"inverse takes (label inverse ((X...) offx) ((Y...) offy))"};
            const auto & a = children_of(terms[2], "the inverse X group");
            const auto & b = children_of(terms[3], "the inverse Y group");
            if (a.size() != 2 || b.size() != 2)
                throw ScpReadError{"each inverse group is ((vars...) offset)"};
            post_constraint(problem,
                Inverse{resolve_variable_list(variables, a[0], "the inverse X list"), resolve_variable_list(variables, b[0], "the inverse Y list"),
                    as_integer(a[1]), as_integer(b[1])},
                label);
        }
        else if (op == "and" || op == "or") {
            // (label and/or ((Z op v) ...) (Y op v)): the reification (the final
            // tuple) holds iff all / at least one of the operand literals hold.
            if (terms.size() != 4)
                throw ScpReadError{op + " takes (label " + op + " (literals...) reif-literal)"};
            auto lits = resolve_literal_list(variables, terms[2], "the " + op + " literal list");
            auto reif = resolve_literal(variables, terms[3]);
            if (op == "and")
                post_constraint(problem, And{move(lits), reif}, label);
            else
                post_constraint(problem, Or{move(lits), reif}, label);
        }
        else if (op == "parity") {
            // (label parity ((Z op v) ...) (Y op v)): cake encodes Y =
            // XOR(operands). The solver only has the bare odd-parity constraint
            // (ParityOdd, XOR(operands) = 1), which it writes with a
            // statically-true output tuple, so require that here.
            if (terms.size() != 4)
                throw ScpReadError{"parity takes (label parity (literals...) reif-literal)"};
            auto lits = resolve_literal_list(variables, terms[2], "the parity literal list");
            if (! is_literally_true(resolve_literal(variables, terms[3])))
                throw ScpReadError{"parity output must be statically true (only bare odd parity is supported)"};
            post_constraint(problem, ParityOdd{move(lits)}, label);
        }
        else if (op == "plus") {
            // (label plus a b result): a + b = result.
            if (terms.size() != 5)
                throw ScpReadError{"plus takes (label plus a b result)"};
            post_constraint(problem,
                Plus{resolve_variable(variables, terms[2]), resolve_variable(variables, terms[3]), resolve_variable(variables, terms[4])}, label);
        }
        else if (op == "minus") {
            // (label minus a b result): a - b = result.
            if (terms.size() != 5)
                throw ScpReadError{"minus takes (label minus a b result)"};
            post_constraint(problem,
                Minus{resolve_variable(variables, terms[2]), resolve_variable(variables, terms[3]), resolve_variable(variables, terms[4])}, label);
        }
        else if (op == "divide" || op == "modulus") {
            // (label divide x y quotient) / (label modulus x y remainder):
            // truncated division, with the divide-by-zero case relational. Flat
            // shape matching cake_pb_cp.
            if (terms.size() != 5)
                throw ScpReadError{"divide/modulus takes (label " + op + " x y result)"};
            auto x = resolve_variable(variables, terms[2]), y = resolve_variable(variables, terms[3]), result = resolve_variable(variables, terms[4]);
            if (op == "divide")
                post_constraint(problem, Divide{x, y, result}, label);
            else
                post_constraint(problem, Modulus{x, y, result}, label);
        }
        else if (op == "power") {
            // (label power (base exponent result)): base ^ exponent = result,
            // with MiniZinc semantics (0^0 = 1, negative exponent truncates).
            if (terms.size() != 3)
                throw ScpReadError{"power takes (label power (base exponent result))"};
            auto vars = resolve_variable_list(variables, terms[2], "the power variable list");
            if (vars.size() != 3)
                throw ScpReadError{"power takes exactly three variables"};
            post_constraint(problem, Power{vars[0], vars[1], vars[2]}, label);
        }
        else if (op == "multiply") {
            // (label multiply v1 v2 result): v1 * v2 = result. Flat shape matching
            // cake_pb_cp. Written by both Multiply and a directly-posted
            // the signed multiply innards; reposting as Multiply resolves to the
            // same encoding for the plain three-distinct-variables shape that it
            // accepts.
            if (terms.size() != 5)
                throw ScpReadError{"multiply takes (label multiply v1 v2 result)"};
            post_constraint(problem,
                Multiply{resolve_variable(variables, terms[2]), resolve_variable(variables, terms[3]), resolve_variable(variables, terms[4])}, label);
        }
        else if (op == "disjunctive" || op == "disjunctive_strict") {
            // (label disjunctive (starts...) (lengths...)): the tasks
            // [start, start + length) pairwise do not overlap. The strict and
            // non-strict forms differ only over zero-length tasks (strict keeps
            // them, non-strict drops them), so they coincide for positive
            // lengths; the keyword carries the distinction. cake_pb_cp parses
            // `disjunctive`, which the writer emits for the non-strict form.
            if (terms.size() != 4)
                throw ScpReadError{"disjunctive is (label " + op + " (starts...) (lengths...))"};
            post_constraint(problem,
                Disjunctive{resolve_variable_list(variables, terms[2], "the disjunctive start list"),
                    resolve_variable_list(variables, terms[3], "the disjunctive length list")}
                    .with_strict(op.ends_with("_strict")),
                label);
        }
        else if (op == "disjunctive_optional" || op == "disjunctive_strict_optional") {
            // (label disjunctive_optional (starts...) (lengths...)
            // (presences...)): disjunctive over tasks that may be absent,
            // presences[i] in {0,1} saying whether task i happens at all. The
            // presences list goes last, where the FlatZinc builtin puts it.
            // Deliberately a keyword of its own rather than an optional argument
            // to `disjunctive`: each separation clause carries the pair's
            // presence disjuncts, so re-deriving it as a plain disjunctive would
            // give a different and strictly stronger constraint.
            if (terms.size() != 5)
                throw ScpReadError{"disjunctive_optional is (label " + op + " (starts...) (lengths...) (presences...))"};
            post_constraint(problem,
                Disjunctive{resolve_variable_list(variables, terms[2], "the disjunctive_optional start list"),
                    resolve_variable_list(variables, terms[3], "the disjunctive_optional length list"),
                    resolve_variable_list(variables, terms[4], "the disjunctive_optional presence list")}
                    .with_strict(op == "disjunctive_strict_optional"),
                label);
        }
        else if (op == "disjunctive2d" || op == "disjunctive2d_strict") {
            // (label disjunctive2d (xs...) (ys...) (widths...) (heights...)): the
            // rectangles [x, x + w) x [y, y + h) pairwise do not overlap. As for
            // disjunctive, the keyword carries strict vs non-strict (identical for
            // positive sizes); cake_pb_cp parses `disjunctive2d`.
            if (terms.size() != 6)
                throw ScpReadError{"disjunctive2d is (label " + op + " (xs...) (ys...) (widths...) (heights...))"};
            post_constraint(problem,
                Disjunctive2D{resolve_variable_list(variables, terms[2], "the disjunctive2d x list"),
                    resolve_variable_list(variables, terms[3], "the disjunctive2d y list"),
                    resolve_variable_list(variables, terms[4], "the disjunctive2d width list"),
                    resolve_variable_list(variables, terms[5], "the disjunctive2d height list")}
                    .with_strict(op.ends_with("_strict")),
                label);
        }
        else if (op == "cumulative_optional") {
            // (label cumulative_optional (starts...) (lengths...) (heights...)
            // (presences...) cap): cumulative over tasks that may be absent,
            // presences[i] in {0,1} saying whether task i is scheduled at all.
            // The presences list sits between the heights and the capacity,
            // where the FlatZinc builtin puts it. Deliberately a keyword of its
            // own rather than an optional argument to `cumulative`: the active
            // flags carry a third conjunct, so re-deriving it as a plain
            // cumulative would give a different, weaker encoding.
            if (terms.size() != 7)
                throw ScpReadError{"cumulative_optional is (label cumulative_optional (starts...) (lengths...) (heights...) (presences...) cap)"};
            post_constraint(problem,
                Cumulative{resolve_variable_list(variables, terms[2], "the cumulative_optional start list"),
                    resolve_variable_list(variables, terms[3], "the cumulative_optional length list"),
                    resolve_variable_list(variables, terms[4], "the cumulative_optional height list"),
                    resolve_variable_list(variables, terms[5], "the cumulative_optional presence list"), resolve_variable(variables, terms[6])},
                label);
        }
        else if (op == "cumulative") {
            // (label cumulative (starts...) (lengths...) (heights...) cap): the
            // tasks [start, start + length) each occupy `height` of a shared
            // resource, and at every time point the total height of active tasks
            // is at most `cap`. Lengths, heights and the capacity may each be a
            // variable or a constant; cake_pb_cp parses exactly this shape.
            if (terms.size() != 6)
                throw ScpReadError{"cumulative is (label cumulative (starts...) (lengths...) (heights...) cap)"};
            post_constraint(problem,
                Cumulative{resolve_variable_list(variables, terms[2], "the cumulative start list"),
                    resolve_variable_list(variables, terms[3], "the cumulative length list"),
                    resolve_variable_list(variables, terms[4], "the cumulative height list"), resolve_variable(variables, terms[5])},
                label);
        }
        else if (op == "regular") {
            read_regular(problem, variables, terms, label);
        }
        else if (op == "table") {
            read_table(problem, variables, terms, label);
        }
        else if (op == "negative_table") {
            read_negative_table(problem, variables, terms, label);
        }
        else if (op == "smart_table") {
            read_smart_table(problem, variables, terms, label);
        }
        else if (op == "all_different_except") {
            read_all_different_except(problem, variables, terms, label);
        }
        else if (op == "symmetric_all_different") {
            read_symmetric_all_different(problem, variables, terms, label);
        }
        else if (op == "at_most_one" || op == "at_most_one_smart_table") {
            read_at_most_one(problem, variables, op, terms, label);
        }
        else if (op == "among") {
            read_among(problem, variables, terms, label);
        }
        else if (op == "value_precede") {
            read_value_precede(problem, variables, terms, label);
        }
        else if (op == "seq_precede_chain") {
            read_seq_precede_chain(problem, variables, terms, label);
        }
        else if (op == "knapsack") {
            read_knapsack(problem, variables, terms, label);
        }
        else if (op == "binpacking") {
            read_bin_packing(problem, variables, terms, label);
        }
        else if (op == "difference") {
            read_difference(problem, variables, terms, label);
        }
        else if (op == "mdd") {
            read_mdd(problem, variables, terms, label);
        }
        else if (op == "min_distance") {
            read_min_distance(problem, variables, terms, label);
        }
        else if (op == "nogoods") {
            read_nogoods(problem, variables, terms, label);
        }
        else if (op == "element_2d") {
            read_element_2d(problem, variables, terms, label);
        }
        else if (op == "lex_smart_table") {
            // (label lex_smart_table (xs...) (ys...)): xs >_lex ys, enforced by a
            // SmartTable decomposition rather than the LexGreaterThan propagator.
            // Its own keyword, matching cake, because the encoding is a different
            // (much larger) one, not just a different propagator.
            if (terms.size() != 4)
                throw ScpReadError{"lex_smart_table is (label lex_smart_table (xs...) (ys...))"};
            post_constraint(problem,
                LexSmartTable{resolve_variable_list(variables, terms[2], "the lex_smart_table first variable list"),
                    resolve_variable_list(variables, terms[3], "the lex_smart_table second variable list")},
                label);
        }
        else if (op.starts_with("lex_")) {
            read_lex(problem, variables, op, terms, label);
        }
        else if (op.starts_with("less_") || op.starts_with("greater_")) {
            read_comparison(problem, variables, op, terms, label);
        }
        else if (op.starts_with("lin_")) {
            read_linear(problem, variables, op, terms, label);
        }
        else if (op.starts_with("equals") || op.starts_with("not_equals")) {
            read_equals(problem, variables, op, terms, label);
        }
        else
            throw ScpUnsupportedConstraintError{op};
    }

    auto minimise_variable = objective.transform([&](const ObjectiveSpec & spec) { return resolve_objective(variables, spec); });
    return ScpModel{move(variables), minimise_variable};
}
