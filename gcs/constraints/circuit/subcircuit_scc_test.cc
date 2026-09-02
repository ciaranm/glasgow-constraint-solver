#include <gcs/constraints/circuit.hh>
#include <gcs/constraints/in.hh>
#include <gcs/constraints/innards/constraints_test_utils.hh>
#include <gcs/problem.hh>
#include <gcs/solve.hh>

#include <cstdlib>
#include <iostream>
#include <optional>
#include <string>
#include <utility>
#include <vector>

using namespace gcs;
using namespace gcs::test_innards;

using std::cout;
using std::endl;
using std::make_optional;
using std::nullopt;
using std::pair;
using std::vector;

// A scenario where the reachability rule earns its keep, which took a couple of attempts to
// build and is worth explaining, because the obvious constructions do not.
//
// The twelve nodes split into two halves that point only within themselves, and the anchor
// is node 6, in the upper half. So the lower half is unreachable from the anchor however the
// search goes: those six nodes could form a tour of their own, but then there would be two
// tours, so all six have to opt out. The reachability rule says so before any decision is
// taken.
//
// The trap is that check-and-prevent gets there too, for free, whenever the search happens
// to close the anchor's tour first: a closed cycle forces everyone outside it to opt out,
// and that is every bit as strong. So separating the two algorithms takes care. Two earlier
// versions of this test came out at *exactly* the same recursion count -- once with the
// halves the other way round, once with them the same size -- because the brancher never
// entered the unreachable half before the tour closed. Giving that half the smallest domains
// in the problem is what makes the search walk into it, where only reachability knows the
// walk is pointless.
//
// The tours through node 6 within the upper six number 5 + 20 + 60 + 120 + 120 = 325.

auto post_constraints(Problem & p, vector<IntegerVariableID> & nodes) -> void
{
    // The lower half points only within itself, each node at either itself or the next one
    // round, and the upper half points only within itself. The anchor is in the upper half,
    // so the lower half is unreachable from it however search goes.
    //
    // The lower half's domains are deliberately the *smallest* in the problem, so the
    // brancher goes there first. That is what makes the two algorithms differ: give the
    // upper half the smaller domains instead and the tour closes before the search ever
    // looks at the lower half, whereupon check forces it off for free and reachability adds
    // nothing at all.
    for (int i = 0; i < 6; ++i)
        p.post(In{nodes[static_cast<std::size_t>(i)], {Integer{i}, Integer{(i + 1) % 6}}});
    for (int i = 6; i < 12; ++i) {
        vector<Integer> values;
        for (int v = 6; v < 12; ++v)
            if (! (i == 6 && v == 6))
                values.emplace_back(Integer{v});
        p.post(In{nodes[static_cast<std::size_t>(i)], values});
    }
}

// The state at the first search node, which is the root after propagation. That is where
// the two algorithms differ crisply: reachability has already forced the whole unreachable
// half to opt out before any decision is taken, and check-and-prevent has not, because
// nothing is fixed yet for it to reason from.
auto run(SubCircuitAlgorithm algorithm, const ViewWrapConfig & view_cfg, const std::string & label, long & lower_half_fixed_at_root) -> long
{
    constexpr int n_positions = 12;
    auto wraps = wraps_for_positions(view_cfg, n_positions);

    Problem p;
    // The anchor's own index has to be out of its declared domain, not merely constrained
    // out by the In below, since with_required_node() checks the domain as declared. Node 6
    // therefore starts at 7, and the In narrows it back to the upper half.
    //
    // A view keeps that declared domain -- it is the same variable seen through an offset,
    // not a fresh one -- so the anchor is still declared on the tour under every wrap, which
    // is what lets this scenario go through the view sweep at all.
    vector<IntegerVariableID> nodes;
    for (int i = 0; i < n_positions; ++i)
        nodes.push_back(
            create_integer_variable_or_constant_with_view(p, pair{i == 6 ? 7 : 0, n_positions - 1}, wraps.at(static_cast<std::size_t>(i))));

    post_constraints(p, nodes);
    p.post(SubCircuit{nodes}.with_required_node(6).with_algorithm(algorithm));

    bool proofs = can_run_veripb();
    auto proof_name = proofs ? make_optional("subcircuit_scc_test_" + label + "_" + view_wrap_config_label(view_cfg)) : nullopt;
    long found = 0;
    auto seen_root = false;
    lower_half_fixed_at_root = 0;
    auto stats = solve_with(p, //
        SolveCallbacks{        //
            .solution = [&](const CurrentState &) -> bool {
                ++found;
                return true;
            },
            .trace = [&](const CurrentState & s) -> bool {
                if (! seen_root) {
                    seen_root = true;
                    for (int i = 0; i < 6; ++i)
                        if (s.has_single_value(nodes[static_cast<std::size_t>(i)]) && s(nodes[static_cast<std::size_t>(i)]) == Integer{i})
                            ++lower_half_fixed_at_root;
                }
                return true;
            }},
        proof_name ? make_optional<ProofOptions>(*proof_name) : nullopt);

    cout << label << ": " << found << " solutions, " << stats.recursions << " recursions, " << lower_half_fixed_at_root
         << " of the unreachable half opted out at the root" << endl;

    if (proof_name && ! verify_proof_and_dispose(*proof_name))
        return -1;

    return found;
}

auto main(int argc, char * argv[]) -> int
{
    establish_and_announce_seed(argc, argv);

    constexpr int n_positions = 12;
    auto view_cfg = parse_view_wrap_config_from_argv(argc, argv);
    if (view_cfg.single_position && (*view_cfg.single_position < 0 || *view_cfg.single_position >= n_positions)) {
        cout << "subcircuit_scc view sweep: position " << *view_cfg.single_position << " out of range for n_positions = " << n_positions
             << "; skipping" << endl;
        return EXIT_SUCCESS;
    }

    constexpr long expected_solutions = 325;

    // Both algorithms, so the reachability rule is pinned to preserving the solution set as
    // well as to verifying, and then the root-state check pins that it is doing anything at
    // all -- a rule that inferred nothing would enumerate identically and verify just as
    // happily. The recursion counts are printed rather than asserted on: the gap here is two
    // nodes out of 558, because check-and-prevent with an evidence node gets to nearly the
    // same place by another route, and a margin that thin is not something to hold a test to.
    long prevent_at_root = 0, scc_at_root = 0;
    auto with_prevent = run(subcircuit::Prevent{}, view_cfg, "prevent", prevent_at_root);
    auto with_scc = run(subcircuit::SCC{}, view_cfg, "scc", scc_at_root);

    if (with_prevent != expected_solutions || with_scc != expected_solutions) {
        cout << "expected " << expected_solutions << " solutions from each" << endl;
        return EXIT_FAILURE;
    }

    if (scc_at_root != 6) {
        cout << "expected reachability to opt the whole unreachable half out at the root, got " << scc_at_root << " of 6" << endl;
        return EXIT_FAILURE;
    }

    if (prevent_at_root != 0) {
        cout << "expected check-and-prevent to opt none of it out at the root, got " << prevent_at_root << endl;
        return EXIT_FAILURE;
    }

    return EXIT_SUCCESS;
}
