#include <gcs/constraints/all_different.hh>
#include <gcs/constraints/comparison.hh>
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

// Driver for payload 2 of the Brancher refactor (dev_docs/brancher-design.md, "Payload 2"):
// each improving solution retires the one it supersedes, so a branch-and-bound descent leaves
// O(1) resident objective-improvement constraints rather than O(#incumbents).
//
// What VeriPB can tell you here is narrow, and it is worth being precise about which half is
// which. It checks that the deletions are *legitimate* -- run under `-c` the `delc` has to
// autoprove, so a retirement of something the survivors do not imply fails at the deletion
// itself. It cannot tell you the retirement happened at all: a build that simply stopped
// emitting them produces a perfectly good proof, just a bigger one, and it cannot tell you the
// order was right either, because it polices the order encoding only at a point of use.
//
// So the counting below is not decoration. It asserts, from the proof text, that every
// incumbent after the first was retired (the O(1) claim, as `#soli - #delc == 1`), and that
// each retirement emitted its two deletions in the load-bearing order -- the core improvement
// constraint by checked deletion first, its Top unit second. The `first` scenario is the other
// half of the same claim: with a single incumbent there is nothing to supersede, and the
// machinery must emit nothing at all.
//
// The mode is set in code, not through GCS_DELETE_ORDER_ENCODING, so the test does not depend
// on the environment; the chain gate goes to 0 for the same reason it does in the other
// drivers, since at the shipped gate of 16 these short chains stay resident anyway.
namespace
{
    // A model that improves in small steps rather than jumping to the optimum: four
    // all-different values summing to the objective, branched largest-value-first so the first
    // solution found is the worst one and branch-and-bound has to walk down. Nothing here is
    // load-bearing except that it produces plenty of incumbents, which the test checks.
    auto run(bool stop_at_first, const optional<string> & proof_basename) -> std::pair<long long, long long>
    {
        Problem p;
        vector<IntegerVariableID> x;
        for (int i = 0; i < 4; ++i)
            x.push_back(p.create_integer_variable(0_i, 8_i, "x" + std::to_string(i)));
        auto obj = p.create_integer_variable(0_i, 32_i, "obj");

        p.post(AllDifferent{x});
        // Two orderings, to keep propagation from collapsing the whole descent into one step.
        p.post(LessThan{x[0], x[1]});
        p.post(LessThan{x[2], x[3]});
        p.post(LinearEquality{WeightedSum{} + 1_i * x[0] + 1_i * x[1] + 1_i * x[2] + 1_i * x[3] + -1_i * obj, 0_i});
        p.minimise(obj);

        optional<ProofOptions> options;
        if (proof_basename) {
            options.emplace(*proof_basename);
            options->set_order_encoding_deletion(OrderEncodingDeletion::Literals).set_order_encoding_deletion_min_chain(0);
        }

        long long incumbents = 0, best = -1;
        solve_with(p,
            SolveCallbacks{.solution = [&](const CurrentState & s) -> bool {
                               ++incumbents;
                               best = s(obj).raw_value;
                               return ! stop_at_first;
                           },
                .branch = branch_with(variable_order::in_order(x), value_order::largest_first())},
            options);

        return {incumbents, best};
    }

    struct ProofCounts
    {
        long long solutions = 0;   // `soli` lines: one core improvement constraint each.
        long long retirements = 0; // `% retire the superseded incumbent` markers.
        long long checked = 0;     // `delc` lines: core improvement constraints taken back out.
        long long unchecked = 0;   // the `del id` retiring a Top unit, counted only inside a marker.
        long long misordered = 0;  // retirements whose two deletions did not arrive in the right order.
    };

    // Walk the proof, pairing each retirement marker with the two deletion lines that must
    // immediately follow it. Reading the text rather than instrumenting the logger is
    // deliberate: what is being asserted is what the proof ended up containing.
    auto count_proof(const string & basename) -> ProofCounts
    {
        ProofCounts counts;
        ifstream proof{basename + ".pbp"};
        for (string line; getline(proof, line);) {
            if (line.starts_with("soli"))
                ++counts.solutions;
            else if (line.find("% retire the superseded incumbent") != string::npos) {
                ++counts.retirements;
                string checked_line, unchecked_line;
                if (! getline(proof, checked_line) || ! getline(proof, unchecked_line)) {
                    ++counts.misordered;
                    break;
                }
                if (checked_line.starts_with("delc "))
                    ++counts.checked;
                if (unchecked_line.starts_with("del id "))
                    ++counts.unchecked;
                if (! checked_line.starts_with("delc ") || ! unchecked_line.starts_with("del id "))
                    ++counts.misordered;
            }
        }
        return counts;
    }
}

auto main(int argc, char * argv[]) -> int
{
    // Hand-rolled parse, matching the other gcs innards drivers; --prove and
    // --proof-files-basename are what run_test_and_verify.bash passes.
    bool prove = false;
    string basename = "incumbent_retire_test";
    string scenario = "many";
    for (int arg = 1; arg < argc; ++arg) {
        string a{argv[arg]};
        if (a == "--prove")
            prove = true;
        else if (a == "--proof-files-basename" && arg + 1 < argc)
            basename = argv[++arg];
        else if (a == "--scenario" && arg + 1 < argc)
            scenario = argv[++arg];
        else {
            cerr << "unrecognised argument '" << a << "'\n";
            return 1;
        }
    }
    if (scenario != "many" && scenario != "first") {
        cerr << "unrecognised scenario '" << scenario << "'\n";
        return 1;
    }

    int rc = 0;
    auto check = [&](bool ok, const string & what) {
        if (! ok) {
            cerr << "incumbent retirement broken: " << what << " (fix the retirement, do not update the number)\n";
            rc = 1;
        }
    };

    bool stop_at_first = scenario == "first";
    auto [incumbents, best] = run(stop_at_first, prove ? optional<string>{basename} : nullopt);

    // 0+1+2+3 is the only way four distinct values from 0..8 can sum to 6, and the two
    // orderings admit it, so a complete descent must reach exactly 6. Independent of anything
    // the proof machinery does, and the point of checking it: deletions that were not implied
    // are the failure mode that would silently change the answer.
    if (! stop_at_first)
        check(best == 6, "the descent did not reach the known optimum of 6, but found " + std::to_string(best));

    if (! prove)
        return rc;

    auto counts = count_proof(basename);
    check(counts.solutions == incumbents,
        "the proof holds " + std::to_string(counts.solutions) + " soli lines for " + std::to_string(incumbents) + " incumbents");

    if (stop_at_first) {
        // One incumbent supersedes nothing, so payload 2 must be entirely inert. Find-first
        // optimisation and `-n 1` take exactly this path.
        check(incumbents == 1, "the find-first scenario did not stop at one incumbent");
        check(counts.retirements == 0, "a single incumbent retired something, with nothing to supersede");
    }
    else {
        // A model that improved once or twice would satisfy everything below by accident, so
        // insist there was a descent worth measuring in the first place.
        check(incumbents >= 5, "only " + std::to_string(incumbents) + " incumbents: too few for the O(1) claim to mean anything");
        check(counts.retirements == incumbents - 1,
            std::to_string(counts.retirements) + " retirements for " + std::to_string(incumbents) + " incumbents, expected one per improvement");
        // The headline: resident core improvement constraints at proof end, which is one
        // whatever the descent's length, rather than one per incumbent.
        check(counts.solutions - counts.checked == 1,
            std::to_string(counts.solutions - counts.checked) + " improvement constraints left resident, expected 1 regardless of descent length");
        check(counts.solutions - counts.unchecked == 1,
            std::to_string(counts.solutions - counts.unchecked) + " Top units left resident, expected 1 regardless of descent length");
    }

    // Checked deletion first, then the Top unit: VeriPB accepts either order (it rejects at a
    // point of use, not at a deletion), so nothing but this check stands behind the ordering.
    check(counts.misordered == 0, std::to_string(counts.misordered) + " retirements emitted their deletions in the wrong order");

    return rc;
}
