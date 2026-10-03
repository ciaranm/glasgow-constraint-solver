#ifndef GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_CONSTRAINTS_REGULAR_REGEX_HH
#define GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_CONSTRAINTS_REGULAR_REGEX_HH

#include <gcs/integer.hh>

#include <set>
#include <string>
#include <unordered_map>
#include <vector>

namespace gcs::innards
{
    /**
     * \brief An epsilon-free finite automaton, possibly non-deterministic, as
     * produced by regex_to_nfa and determinise.
     *
     * State 0 is the (single) initial state. transitions[q] maps each input
     * symbol to the set of states reachable from q on that symbol (a missing key
     * means no transition). final_states lists the accepting states. A
     * deterministic automaton is the special case where every transition target
     * set is a singleton, which is the only kind the Regular constraint
     * encodes: it determinises anything else first.
     */
    struct RegexNfa
    {
        long num_states;
        std::vector<std::unordered_map<Integer, std::set<long>>> transitions;
        std::vector<long> final_states;
    };

    /**
     * \brief Compile a regular expression string into an epsilon-free NFA over
     * the given alphabet.
     *
     * The syntax matches MiniZinc/Gecode's string regex exactly (see
     * dev_docs and the libminizinc flex/bison grammar): integer literals,
     * concatenation by juxtaposition, union "|", groups "()", wildcard ".",
     * classes "[3-6 7]", negated classes "[^3 5]", and the quantifiers "*",
     * "+", "?", "{n}", "{n,}", "{n,m}". Symbols are integers; multi-digit runs
     * are a single symbol.
     *
     * \a alphabet is the set of values that "." and "[^...]" expand to: the
     * caller passes the contiguous min..max range of the constrained variables'
     * domains, mirroring MiniZinc's semantics. Literals and explicit class
     * ranges are taken verbatim and are not clamped to the alphabet.
     *
     * Throws InvalidProblemDefinitionException if the string cannot be parsed.
     */
    [[nodiscard]] auto regex_to_nfa(const std::string & regex, const std::vector<Integer> & alphabet) -> RegexNfa;

    /**
     * \brief Determinise an automaton by the subset construction.
     *
     * Returns an automaton accepting the same language in which every
     * transition target set is a singleton, so that every word has at most one
     * run. Only subsets reachable from the start state are built, and states
     * are numbered in breadth-first order over sorted symbols, so the result
     * does not depend on hash-map iteration order. The input's transitions may
     * be shorter than num_states, a missing entry meaning no transitions.
     *
     * Regular's OPB encoding needs this: its state flags say which run the
     * automaton took, and on a word with two accepting runs nothing determines
     * which, so unit propagation cannot check a solution (issue #1203). The
     * result can be exponentially larger than the input, as for any DFA.
     */
    [[nodiscard]] auto determinise(const RegexNfa & nfa) -> RegexNfa;

    /**
     * \brief Compile a regular expression string into a deterministic
     * automaton: regex_to_nfa, then determinise.
     */
    [[nodiscard]] auto regex_to_dfa(const std::string & regex, const std::vector<Integer> & alphabet) -> RegexNfa;

    /**
     * \brief Reference regex matcher, used for testing.
     *
     * Parses the same syntax as regex_to_nfa and decides membership by directly
     * interpreting the expression, independently of the NFA construction. Returns
     * true iff \a sequence is in the language of \a regex over \a alphabet.
     */
    [[nodiscard]] auto regex_reference_accepts(
        const std::string & regex, const std::vector<Integer> & alphabet, const std::vector<Integer> & sequence) -> bool;
}

#endif
