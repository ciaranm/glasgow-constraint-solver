#include <gcs/constraints/regular/regex.hh>
#include <gcs/exception.hh>

#include <catch2/catch_test_macros.hpp>

#include <cstddef>
#include <set>
#include <string>
#include <vector>

using namespace gcs;
using namespace gcs::innards;

using std::set;
using std::size_t;
using std::string;
using std::vector;

namespace
{
    // Direct NFA simulation: the thing under test, kept independent of the
    // reference matcher in regex_to_nfa's source.
    auto nfa_accepts(const RegexNfa & nfa, const vector<Integer> & sequence) -> bool
    {
        set<long> active{0};
        for (const auto & value : sequence) {
            set<long> next;
            for (auto q : active) {
                if (static_cast<size_t>(q) >= nfa.transitions.size())
                    continue;
                auto it = nfa.transitions[static_cast<size_t>(q)].find(value);
                if (it != nfa.transitions[static_cast<size_t>(q)].end())
                    next.insert(it->second.begin(), it->second.end());
            }
            active = std::move(next);
            if (active.empty())
                return false;
        }
        for (auto f : nfa.final_states)
            if (active.contains(f))
                return true;
        return false;
    }

    auto is_deterministic(const RegexNfa & automaton) -> bool
    {
        for (const auto & state_transitions : automaton.transitions)
            for (const auto & [_, targets] : state_transitions)
                if (targets.size() != 1)
                    return false;
        return true;
    }

    // Enumerate every sequence of length 0..max_len over the given symbols and
    // assert the compiled NFA, and the DFA determinised from it, agree with the
    // reference matcher on each.
    auto cross_check(const string & regex, const vector<Integer> & alphabet, const vector<Integer> & enum_symbols, size_t max_len) -> void
    {
        auto nfa = regex_to_nfa(regex, alphabet);
        auto dfa = regex_to_dfa(regex, alphabet);
        CHECK(is_deterministic(dfa));
        vector<Integer> sequence;
        auto recurse = [&](auto && self) -> void {
            INFO("regex \"" << regex << "\" sequence length " << sequence.size());
            CHECK(nfa_accepts(nfa, sequence) == regex_reference_accepts(regex, alphabet, sequence));
            CHECK(nfa_accepts(dfa, sequence) == regex_reference_accepts(regex, alphabet, sequence));
            if (sequence.size() == max_len)
                return;
            for (const auto & symbol : enum_symbols) {
                sequence.push_back(symbol);
                self(self);
                sequence.pop_back();
            }
        };
        recurse(recurse);
    }
}

TEST_CASE("Regex literal and concatenation")
{
    auto nfa = regex_to_nfa("1 2 3", {});
    CHECK(nfa_accepts(nfa, {1_i, 2_i, 3_i}));
    CHECK(! nfa_accepts(nfa, {1_i, 2_i}));
    CHECK(! nfa_accepts(nfa, {1_i, 2_i, 3_i, 1_i}));
    // "123" is a single multi-digit symbol, not the concatenation 1 2 3.
    auto single = regex_to_nfa("123", {});
    CHECK(nfa_accepts(single, {123_i}));
    CHECK(! nfa_accepts(single, {1_i, 2_i, 3_i}));
}

TEST_CASE("Regex quantifier binds to the whole integer atom")
{
    // "12*" is (12)*, zero or more of the symbol twelve, per MiniZinc semantics.
    auto nfa = regex_to_nfa("12*", {});
    CHECK(nfa_accepts(nfa, {}));
    CHECK(nfa_accepts(nfa, {12_i}));
    CHECK(nfa_accepts(nfa, {12_i, 12_i}));
    CHECK(! nfa_accepts(nfa, {1_i}));
    CHECK(! nfa_accepts(nfa, {1_i, 2_i}));
    cross_check("12*", {}, {1_i, 2_i, 12_i}, 3);
}

TEST_CASE("Regex concatenation binds tighter than union")
{
    // "7 6|8" parses as (7 6) | 8.
    auto nfa = regex_to_nfa("7 6|8", {});
    CHECK(nfa_accepts(nfa, {7_i, 6_i}));
    CHECK(nfa_accepts(nfa, {8_i}));
    CHECK(! nfa_accepts(nfa, {7_i}));
    CHECK(! nfa_accepts(nfa, {7_i, 8_i}));
    cross_check("7 6|8", {}, {6_i, 7_i, 8_i}, 3);
}

TEST_CASE("Regex groups")
{
    auto nfa = regex_to_nfa("7(6|8)", {});
    CHECK(nfa_accepts(nfa, {7_i, 6_i}));
    CHECK(nfa_accepts(nfa, {7_i, 8_i}));
    CHECK(! nfa_accepts(nfa, {7_i}));
    CHECK(! nfa_accepts(nfa, {6_i}));
    cross_check("7(6|8)", {}, {6_i, 7_i, 8_i}, 3);
}

TEST_CASE("Regex star plus and optional")
{
    cross_check("0* 1 1* 0*", {}, {0_i, 1_i}, 5); // language 0*11*0*
    auto plus = regex_to_nfa("4+", {});
    CHECK(! nfa_accepts(plus, {}));
    CHECK(nfa_accepts(plus, {4_i}));
    CHECK(nfa_accepts(plus, {4_i, 4_i}));
    auto opt = regex_to_nfa("5?", {});
    CHECK(nfa_accepts(opt, {}));
    CHECK(nfa_accepts(opt, {5_i}));
    CHECK(! nfa_accepts(opt, {5_i, 5_i}));
}

TEST_CASE("Regex wildcard uses the supplied alphabet")
{
    // Caller passes the contiguous min..max range; here that models domain
    // {0,2,4}, whose min..max is {0,1,2,3,4}.
    vector<Integer> alphabet{0_i, 1_i, 2_i, 3_i, 4_i};
    auto nfa = regex_to_nfa(".", alphabet);
    CHECK(nfa_accepts(nfa, {3_i}));
    CHECK(nfa_accepts(nfa, {0_i}));
    CHECK(! nfa_accepts(nfa, {5_i}));
    CHECK(! nfa_accepts(nfa, {}));
    CHECK(! nfa_accepts(nfa, {1_i, 1_i}));
    cross_check(". .", alphabet, {0_i, 1_i, 4_i, 5_i}, 3);
}

TEST_CASE("Regex classes and negated classes")
{
    auto cls = regex_to_nfa("[3-6 7]", {});
    for (auto v : {3_i, 4_i, 5_i, 6_i, 7_i})
        CHECK(nfa_accepts(cls, {v}));
    CHECK(! nfa_accepts(cls, {2_i}));
    CHECK(! nfa_accepts(cls, {8_i}));

    // Reversed range is accepted and normalised.
    auto reversed = regex_to_nfa("[5-3]", {});
    for (auto v : {3_i, 4_i, 5_i})
        CHECK(nfa_accepts(reversed, {v}));
    CHECK(! nfa_accepts(reversed, {6_i}));

    vector<Integer> alphabet{0_i, 1_i, 2_i, 3_i, 4_i};
    auto neg = regex_to_nfa("[^2]", alphabet);
    for (auto v : {0_i, 1_i, 3_i, 4_i})
        CHECK(nfa_accepts(neg, {v}));
    CHECK(! nfa_accepts(neg, {2_i}));
    cross_check("[^2]", alphabet, {0_i, 2_i, 4_i, 5_i}, 2);
}

TEST_CASE("Regex counted quantifiers")
{
    auto exact = regex_to_nfa("1{3}", {});
    CHECK(nfa_accepts(exact, {1_i, 1_i, 1_i}));
    CHECK(! nfa_accepts(exact, {1_i, 1_i}));
    CHECK(! nfa_accepts(exact, {1_i, 1_i, 1_i, 1_i}));

    auto at_least = regex_to_nfa("9{2,}", {});
    CHECK(! nfa_accepts(at_least, {9_i}));
    CHECK(nfa_accepts(at_least, {9_i, 9_i}));
    CHECK(nfa_accepts(at_least, {9_i, 9_i, 9_i}));

    auto between = regex_to_nfa("7{1,3}", {});
    CHECK(! nfa_accepts(between, {}));
    CHECK(nfa_accepts(between, {7_i}));
    CHECK(nfa_accepts(between, {7_i, 7_i, 7_i}));
    CHECK(! nfa_accepts(between, {7_i, 7_i, 7_i, 7_i}));

    cross_check("2{0,2} 3", {}, {2_i, 3_i}, 4);
}

TEST_CASE("Regex ambiguous expressions determinise")
{
    // Each of these accepts some word along two runs of its NFA, which is
    // what Regular's encoding cannot tolerate (issue #1203).
    auto ambiguous = regex_to_nfa("0|0", {});
    CHECK(! is_deterministic(ambiguous));
    auto determinised = regex_to_dfa("0|0", {});
    CHECK(is_deterministic(determinised));
    CHECK(determinised.num_states == 2);

    cross_check("0|0", {}, {0_i, 1_i}, 3);
    cross_check("0* 0*", {}, {0_i, 1_i}, 4);
    cross_check("(0|0) 1", {}, {0_i, 1_i}, 3);
    cross_check("0 1*|0 1", {}, {0_i, 1_i}, 4);
    cross_check("(0|1)* 1 (0|1)*", {}, {0_i, 1_i}, 5);
    cross_check("(0+)+ 1?", {}, {0_i, 1_i}, 4);
}

TEST_CASE("Determinise a hand-written automaton")
{
    // Two transitions on 0 out of the start; state 3 has no entry in
    // transitions at all, and state 4 is unreachable.
    RegexNfa nfa{5, {{{0_i, {1, 2}}}, {{1_i, {3}}}, {{0_i, {3}}}}, {3, 4}};
    auto dfa = determinise(nfa);
    CHECK(is_deterministic(dfa));
    // {0}, {1, 2}, {3}: the subsets reachable from the start.
    CHECK(dfa.num_states == 3);
    CHECK(dfa.final_states == vector<long>{2});
    for (const auto & word : vector<vector<Integer>>{{}, {0_i}, {0_i, 0_i}, {0_i, 1_i}, {1_i, 0_i}, {0_i, 1_i, 0_i}})
        CHECK(nfa_accepts(dfa, word) == nfa_accepts(nfa, word));
}

TEST_CASE("Regex parse errors")
{
    CHECK_THROWS_AS(regex_to_nfa("1 & 2", {}), InvalidProblemDefinitionException);  // illegal token
    CHECK_THROWS_AS(regex_to_nfa("", {}), InvalidProblemDefinitionException);       // empty
    CHECK_THROWS_AS(regex_to_nfa("   ", {}), InvalidProblemDefinitionException);    // whitespace only
    CHECK_THROWS_AS(regex_to_nfa("*1", {}), InvalidProblemDefinitionException);     // leading quantifier
    CHECK_THROWS_AS(regex_to_nfa("(1", {}), InvalidProblemDefinitionException);     // unbalanced group
    CHECK_THROWS_AS(regex_to_nfa("1)", {}), InvalidProblemDefinitionException);     // trailing token
    CHECK_THROWS_AS(regex_to_nfa("1{3,1}", {}), InvalidProblemDefinitionException); // upper < lower
    CHECK_THROWS_AS(regex_to_nfa("[]", {}), InvalidProblemDefinitionException);     // empty class
}
