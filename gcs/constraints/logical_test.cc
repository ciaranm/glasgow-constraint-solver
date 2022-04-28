/* vim: set sw=4 sts=4 et foldmethod=syntax : */

#include <gcs/constraints/equals.hh>
#include <gcs/constraints/logical.hh>
#include <gcs/problem.hh>
#include <gcs/solve.hh>

#include <cstdlib>
#include <functional>
#include <iostream>
#include <optional>
#include <random>
#include <set>
#include <tuple>
#include <utility>
#include <vector>

using std::cerr;
using std::endl;
using std::index_sequence;
using std::make_index_sequence;
using std::mt19937;
using std::nullopt;
using std::optional;
using std::pair;
using std::random_device;
using std::set;
using std::string;
using std::to_string;
using std::tuple;
using std::uniform_int_distribution;
using std::vector;

using namespace gcs;

namespace
{
    auto power_set(int n, vector<uint8_t> & s, const auto & yield) -> void
    {
        if (0 == n)
            yield(s);
        else {
            s.push_back(true);
            power_set(n - 1, s, yield);
            s.pop_back();
            s.push_back(false);
            power_set(n - 1, s, yield);
            s.pop_back();
        }
    }
}

template <typename Logical_>
auto run_logical_test(int n_vars, optional<bool> r, const vector<pair<int, bool>> & terms,
    bool logic_start, const auto & logic) -> bool
{
    cerr << typeid(Logical_).name() << " " << n_vars << " " << (r == nullopt ? string{"null"} : to_string(*r)) << " (";
    for (auto & [c, p] : terms)
        cerr << " " << c << "," << p;
    cerr << ")" << endl;

    set<pair<vector<uint8_t>, bool>> expected, actual;

    vector<uint8_t> acc;
    power_set(n_vars, acc, [&](const vector<uint8_t> & candidate) {
        bool met = logic_start;
        for (auto & [c, p] : terms)
            met = logic(met, (c == -1 ? true : candidate.at(c)) == p);

        if (r == nullopt)
            expected.emplace(candidate, met);
        else if (r != nullopt && *r == true && met)
            expected.emplace(candidate, true);
        else if (r != nullopt && *r == false && ! met)
            expected.emplace(candidate, false);
    });

    Problem p{ProofOptions{"logical_test.opb", "logical_test.veripb"}};
    auto vs = p.create_integer_variable_vector(n_vars, 0_i, 1_i, "vs");
    auto rv = p.create_integer_variable(0_i, 1_i, "rv");

    Literals lits;
    for (auto & [c, p] : terms)
        lits.push_back(-1 == c ? (p ? Literal{TrueLiteral{}} : Literal{FalseLiteral{}}) : (p ? vs.at(c) == 1_i : vs.at(c) == 0_i));
    p.post(Logical_{lits, r == nullopt ? Literal{rv == 1_i} : *r == true ? Literal{TrueLiteral{}}
                                                                         : Literal{FalseLiteral{}}});

    if (r != nullopt)
        p.post(Equals{rv, *r ? 1_c : 0_c});

    solve(p, [&](const CurrentState & s) -> bool {
        vector<uint8_t> got;
        for (auto & v : vs)
            got.push_back(s(v) == 1_i ? 1 : 0);
        actual.emplace(got, s(rv) == 1_i ? 1 : 0);
        return true;
    });

    if (actual != expected) {
        cerr << "actual:";
        for (auto & a : actual) {
            cerr << " (";
            auto & [v, r] = a;
            for (auto & vv : v)
                cerr << (vv ? "t" : "f");
            cerr << "), " << (r ? "t" : "f");
            if (! expected.contains(a))
                cerr << "!";
            cerr << ";";
        }
        cerr << " expected:";
        for (auto & a : expected) {
            cerr << " (";
            auto & [v, r] = a;
            for (auto & vv : v)
                cerr << (vv ? "t" : "f");
            cerr << "), " << (r ? "t" : "f");
            if (! actual.contains(a))
                cerr << "!";
            cerr << ";";
        }
        cerr << endl;
    }

    if (actual != expected)
        return false;

    if (0 != system("veripb logical_test.opb logical_test.veripb"))
        return false;

    return true;
}

auto main(int, char *[]) -> int
{
    vector<tuple<int, optional<bool>, vector<pair<int, bool>>>> data = {
        {3, nullopt, {{0, true}, {1, true}, {2, true}}},
        {3, nullopt, {{0, false}, {1, false}, {2, false}}},
        {3, nullopt, {{0, false}, {1, false}, {2, true}}},
        {2, nullopt, {{0, true}, {1, true}}},
        {2, nullopt, {{0, true}, {0, false}, {1, true}}},
        {5, nullopt, {{1, true}, {1, true}, {1, true}}},
        {5, nullopt, {{1, false}, {1, false}, {1, false}}},
        {3, false, {{0, true}, {1, true}, {2, true}}},
        {3, false, {{0, false}, {1, false}, {2, true}}},
        {2, false, {{0, true}, {1, true}}},
        {2, false, {{0, true}, {0, false}, {1, true}}},
        {5, false, {{1, true}, {1, true}, {1, true}}},
        {5, false, {{1, false}, {1, false}, {1, false}}},
        {3, true, {{0, true}, {1, true}, {2, true}}},
        {3, true, {{0, false}, {1, false}, {2, true}}},
        {2, true, {{0, true}, {1, true}}},
        {2, true, {{0, true}, {0, false}, {1, true}}},
        {5, true, {{1, true}, {1, true}, {1, true}}},
        {5, true, {{1, false}, {1, false}, {1, false}}},
        {2, false, {{0, false}, {-1, false}, {1, true}}},
        {5, false, {{1, false}, {-1, false}, {3, true}, {4, false}}},
        {5, false, {{4, false}, {-1, false}, {0, true}, {-1, true}, {1, true}}},
        {5, false, {{-1, false}}},
        {5, false, {{-1, true}}},
        {5, false, {{4, true}, {0, true}, {3, false}}},
        {3, nullopt, {{-1, true}, {2, true}, {1, true}}},
        {5, nullopt, {{2, false}, {4, true}, {-1, true}, {-1, true}, {0, true}}},
        {2, nullopt, {}},
        {2, true, {}},
        {2, false, {}}};

    random_device rand_dev;
    mt19937 rand(rand_dev());
    for (int x = 0; x < 10; ++x) {
        uniform_int_distribution n_clauses(0, 5);
        uniform_int_distribution n_vars(-1, 4);
        uniform_int_distribution full_reif(0, 2);
        uniform_int_distribution positive(0, 1);

        vector<pair<int, bool>> terms;
        for (unsigned l = 0, l_end = n_clauses(rand); l != l_end; ++l)
            terms.emplace_back(n_vars(rand), positive(rand) == 1);
        optional<bool> r;
        switch (full_reif(rand)) {
        case 0: r = nullopt; break;
        case 1: r = true; break;
        case 2: r = false; break;
        }
        data.emplace_back(tuple{5, r, terms});
    }

    for (auto & [n_vars, reif, terms] : data) {
        if (! run_logical_test<And>(n_vars, reif, terms, true, [&](bool b1, bool b2) { return b1 && b2; }))
            return EXIT_FAILURE;
        if (! run_logical_test<Or>(n_vars, reif, terms, false, [&](bool b1, bool b2) { return b1 || b2; }))
            return EXIT_FAILURE;
    }

    return EXIT_SUCCESS;
}
