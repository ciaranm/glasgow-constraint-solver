// EXPERIMENT ONLY (cpaior2027 paper): random 2D/3D element instances, to compare
// nested against flat cases lines (GCS_ELEMENT_CASES=flat).
#include <cxxopts.hpp>
#include <gcs/constraints/element/element.hh>
#include <gcs/problem.hh>
#include <gcs/solve.hh>
#include <iostream>
#include <random>
#include <string>

using namespace gcs;
using std::cerr;
using std::cout;
using std::endl;
using std::string;
using std::vector;

template <typename E_>
struct Element3DStress : NDimensionalElement<E_, 3>
{
    using Base = NDimensionalElement<E_, 3>;
    Element3DStress(IntegerVariableID v, typename Base::IndexVariables i, typename Base::IndexStarts st, typename Base::Array a,
        ElementConsistency c) : Base(v, std::move(i), std::move(st), std::move(a), c)
    {
    }
};

auto main(int argc, char * argv[]) -> int
{
    cxxopts::Options options("element_stress");
    options.add_options()                                                                      //
        ("prove", "Create a proof")                                                            //
        ("seed", "Seed", cxxopts::value<int>()->default_value("0"))                            //
        ("dims", "2 or 3", cxxopts::value<int>()->default_value("2"))                          //
        ("n", "Index domain size", cxxopts::value<int>()->default_value("4"))                  //
        ("k", "Entries in 0..k", cxxopts::value<int>()->default_value("10"))                   //
        ("constant", "Constant array")                                                         //
        ("max-solutions", "Stop after this many", cxxopts::value<long>()->default_value("50")) //
        ("stats", "Print stats")                                                               //
        ("proof-files-basename", "Basename", cxxopts::value<string>()->default_value("element_stress"));
    auto o = options.parse(argc, argv);
    auto n = o["n"].as<int>(), k = o["k"].as<int>(), dims = o["dims"].as<int>();
    bool constant = o.contains("constant");
    std::mt19937 rng(o["seed"].as<int>());
    std::uniform_int_distribution<int> val{0, k}, wid{0, k / 2};

    Problem p{};
    auto entry_var = [&]() {
        auto lo = val(rng);
        return p.create_integer_variable(Integer{lo}, Integer{lo + wid(rng)});
    };
    auto entry_const = [&]() { return Integer{val(rng)}; };
    auto y = p.create_integer_variable(0_i, Integer{k + k / 2});
    vector<IntegerVariableID> idx;
    for (int d = 0; d < dims; ++d)
        idx.push_back(p.create_integer_variable(0_i, Integer{n - 1}));

    if (dims == 2) {
        if (constant) {
            vector<vector<Integer>> a(n, vector<Integer>(n, 0_i));
            for (auto & r : a)
                for (auto & e : r)
                    e = entry_const();
            p.post(Element2DConstantArray{y, idx[0], idx[1], std::move(a)});
        }
        else {
            vector<vector<IntegerVariableID>> a(n, vector<IntegerVariableID>(n, y));
            for (auto & r : a)
                for (auto & e : r)
                    e = entry_var();
            p.post(Element2D{y, idx[0], idx[1], std::move(a)});
        }
    }
    else {
        if (constant) {
            vector<vector<vector<Integer>>> a(n, vector<vector<Integer>>(n, vector<Integer>(n, 0_i)));
            for (auto & r : a)
                for (auto & c : r)
                    for (auto & e : c)
                        e = entry_const();
            p.post(Element3DStress<Integer>{y, idx, {0_i, 0_i, 0_i}, std::move(a), consistency::GAC{}});
        }
        else {
            vector<vector<vector<IntegerVariableID>>> a(n, vector<vector<IntegerVariableID>>(n, vector<IntegerVariableID>(n, y)));
            for (auto & r : a)
                for (auto & c : r)
                    for (auto & e : c)
                        e = entry_var();
            p.post(Element3DStress<IntegerVariableID>{y, idx, {0_i, 0_i, 0_i}, std::move(a), consistency::GAC{}});
        }
    }

    long sols = 0, max_sols = o["max-solutions"].as<long>();
    auto stats = solve(
        p, [&](const CurrentState &) { return ++sols < max_sols; },
        o.contains("prove") ? std::make_optional(ProofOptions{o["proof-files-basename"].as<string>()}) : std::nullopt);
    if (o.contains("stats"))
        cout << stats << endl;
    return EXIT_SUCCESS;
}
