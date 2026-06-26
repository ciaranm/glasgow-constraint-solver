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
     * \brief An epsilon-free non-deterministic finite automaton, as produced by
     * regex_to_nfa.
     *
     * State 0 is the (single) initial state. transitions[q] maps each input
     * symbol to the set of states reachable from q on that symbol (a missing key
     * means no transition). final_states lists the accepting states. The Regular
     * constraint consumes this directly: a deterministic automaton is just the
     * special case where every transition target set is a singleton.
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
