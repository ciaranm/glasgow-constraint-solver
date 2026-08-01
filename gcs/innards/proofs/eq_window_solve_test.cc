#include <gcs/constraints/comparison.hh>
#include <gcs/constraints/equals.hh>
#include <gcs/constraints/linear.hh>
#include <gcs/current_state.hh>
#include <gcs/problem.hh>
#include <gcs/search_heuristics.hh>
#include <gcs/solve.hh>

#include <fstream>
#include <iostream>
#include <optional>
#include <string>
#include <vector>

using namespace gcs;

using std::cerr;
using std::getline;
using std::ifstream;
using std::nullopt;
using std::optional;
using std::string;
using std::vector;

// The eq-atom window (dev_docs/brancher-design.md) driven by a real search rather than by
// the proof API directly: a small enumeration branched with the four contiguous eq value
// orders, so the window's advance and per-iteration tidy are emitted from solve.cc's own
// loop, over eq atoms that propagation is naming and reasoning about at the same time.
// eq_window_test drives the mechanism in isolation and asserts the residency invariant;
// this one checks it survives contact with the solver -- interleaved propagation, holes
// left in domains by earlier decisions, solutions taking permanent references to the eq
// atoms the window would otherwise evict, and the node-close lemma still being RUP once the
// window has deleted the sibling clauses it subsumes.
//
// Every run enumerates with all four orders and compares the counts, so a window that lost
// or invented a solution fails whichever entry runs; one of the four writes the proof
// VeriPB then checks, chosen by --order, so all four proof shapes are covered across the
// registered ctest entries. The descending pair matter especially: they are the UpperBound
// mirror, which the hand-authored driver never covered.
//
// The mode, the chain gate and the window are set in code: at the shipped defaults (window
// off, gate 16) this would exercise nothing at all.
namespace
{
    auto value_order_named(const string & name) -> optional<BranchValueGenerator>
    {
        if (name == "smallest_first")
            return value_order::smallest_first();
        if (name == "largest_first")
            return value_order::largest_first();
        if (name == "smallest_in")
            return value_order::smallest_in();
        if (name == "largest_in")
            return value_order::largest_in();
        return nullopt;
    }

    auto run(const string & order_name, bool bounds_only, const optional<string> & proof_basename) -> long long
    {
        Problem p;
        auto x = p.create_integer_variable(0_i, 6_i, "x");
        auto y = p.create_integer_variable(0_i, 6_i, "y");
        auto z = p.create_integer_variable(0_i, 6_i, "z");
        // Two models, because the window's behaviour splits on one thing: whether the branch
        // layer is the first to name a value's eq atom.
        //
        //  - **bounds_only** -- a linear equality with awkward coefficients, plus an
        //    ordering. Both reason in `ge` thresholds and never name an eq atom, and the
        //    linear propagator is far too weak to see which values fail, so the search
        //    genuinely refutes values and every guess mints its own eq atom, windowed. This
        //    is the model whose advances and tidies get VeriPB-checked.
        //  - **otherwise** -- the same plus NotEquals, whose per-value pruning names eq atoms
        //    itself, permanently, before the search ever branches on them. The window then
        //    engages barely or not at all, and must cost nothing rather than emit advances it
        //    can never tidy behind. This is the eq-heavy real-instance shape (talent windows
        //    nothing at all), and it is here to be sure that path stays correct.
        p.post(LinearEquality{WeightedSum{} + 2_i * x + 3_i * y + 5_i * z, 31_i});
        p.post(LessThan{x, y});
        p.post(LessThan{y, z});
        if (! bounds_only)
            p.post(NotEquals{x, z});

        // Fixed variable order, so the solution count is compared against orders that
        // differ only in how they pick values.
        auto branch = branch_with(variable_order::in_order(vector<IntegerVariableID>{x, y, z}), *value_order_named(order_name));

        long long solutions = 0;
        optional<ProofOptions> options;
        if (proof_basename) {
            options.emplace(*proof_basename);
            options->set_order_encoding_deletion(OrderEncodingDeletion::Literals)
                .set_order_encoding_deletion_min_chain(0)
                .set_order_encoding_deletion_eq_window();
        }

        solve_with(p,
            SolveCallbacks{.solution = [&](const CurrentState &) -> bool {
                               ++solutions;
                               return true;
                           },
                .branch = branch},
            options);

        return solutions;
    }
}

auto main(int argc, char * argv[]) -> int
{
    // A hand-rolled parse rather than cxxopts, matching the other gcs innards tests, which
    // are run by run_test_and_verify.bash and take no other options. --prove and
    // --proof-files-basename are what that script passes.
    bool prove = false;
    string basename = "eq_window_solve_test";
    string proof_order = "smallest_first";
    string proof_model = "bounds";
    for (int arg = 1; arg < argc; ++arg) {
        string a{argv[arg]};
        if (a == "--prove")
            prove = true;
        else if (a == "--proof-files-basename" && arg + 1 < argc)
            basename = argv[++arg];
        else if (a == "--order" && arg + 1 < argc)
            proof_order = argv[++arg];
        else if (a == "--model" && arg + 1 < argc)
            proof_model = argv[++arg];
        else {
            cerr << "unrecognised argument '" << a << "'\n";
            return 1;
        }
    }

    if (! value_order_named(proof_order)) {
        cerr << "unrecognised value order '" << proof_order << "'\n";
        return 1;
    }
    if (proof_model != "bounds" && proof_model != "holes") {
        cerr << "unrecognised model '" << proof_model << "'\n";
        return 1;
    }

    int rc = 0;
    for (bool bounds_only : {true, false}) {
        optional<long long> expected;
        for (const auto & order : {"smallest_first", "largest_first", "smallest_in", "largest_in"}) {
            // Exactly one (order, model) pair writes the proof this run:
            // run_test_and_verify.bash checks one pair of files, and eight proofs of the same
            // enumerations would leave seven of them unchecked on disk.
            bool writes_proof = prove && order == proof_order && bounds_only == (proof_model == "bounds");
            auto solutions = run(order, bounds_only, writes_proof ? optional<string>{basename} : nullopt);
            if (! expected)
                expected = solutions;
            else if (*expected != solutions) {
                cerr << "eq window changed the solution count: " << order << " found " << solutions << ", expected " << *expected << "\n";
                rc = 1;
            }
        }

        // The exact count does not matter, but a model that found nothing would be checking
        // nothing.
        if (! expected || *expected == 0) {
            cerr << "eq window solve test found no solutions at all (bounds_only=" << bounds_only << ")\n";
            rc = 1;
        }
    }

    // A window that quietly stopped windowing anything would still enumerate correctly and
    // still verify -- it would simply be the baseline. So check the proof this run actually
    // wrote contains the window's advances. Only the full d-way orders emit them: the `_in`
    // pair's single tidiable step is the complement-sibling shape the window deliberately
    // skips (see dev_docs/brancher-design.md), and the `holes` model deliberately windows
    // nothing, so for those there is nothing to count and the coverage they carry is that
    // their proofs verify at all.
    if (prove && proof_model == "bounds" && (proof_order == "smallest_first" || proof_order == "largest_first")) {
        ifstream proof{basename + ".pbp"};
        long long advances = 0;
        for (string line; getline(proof, line);)
            if (line.find("% eq window advance") != string::npos)
                ++advances;
        if (advances == 0) {
            cerr << "no eq window advance in " << basename << ".pbp: the window did not fire, so this run checked nothing"
                 << " (fix the window, do not drop this check)\n";
            rc = 1;
        }
    }

    return rc;
}
