/* Does the cumulative relaxation of `diffn` extend from 2 dimensions to k?
 *
 * A probe, in the sense #730 used before any sorting-network propagator
 * existed: hand-build the derivation for a small instance and put it in front
 * of VeriPB, so that "we believe it extends" becomes "we checked". Issue #975
 * asks for exactly this and issue #972 asks for its 2-D half, which is the same
 * code with one axis fewer.
 *
 * THE ARGUMENT UNDER TEST. Project a `diffn` onto its last axis. At a point
 * `t_d` on each of the other axes, look at the boxes active there --- covering
 * `t_d` on every one of those axes at once. For two such boxes, every disjunct
 * of the separation clause except the last axis's two is refuted (both cover
 * every earlier axis's point, so neither can be before the other there), so the
 * clause is left saying they are separated on the LAST axis. A set of boxes
 * pairwise separated on one axis is a set of disjoint intervals on a line, and
 * disjoint intervals inside a window of height `H` have total size at most `H`.
 * That last step is `ComparatorNetwork`, unchanged.
 *
 * In 2-D "every other axis" is one axis and two disjuncts are refuted; in 3-D
 * it is two axes and four. The question #975 records as unchecked is whether
 * the recursion carries the separations correctly through that conjunction, and
 * what it costs. The construction below is the same function for any k, which
 * is itself part of the answer.
 *
 * WHAT THIS PROBE DOES NOT TEST, deliberately and worth stating: activity as a
 * *flag*. Here each box's domain on the earlier axes forces it to cover the
 * point, so the set is fixed and known at proof-writing time, and the
 * refutations above are unconditional. A propagator would instead want a row
 * `sum_i size_i * active_{i,t} <= H` over minted activity flags, which is a
 * strictly harder object --- see the probe's report in #975. What is checked
 * here is the geometry: that refuting the other axes' disjuncts really does
 * leave the last axis's pair, and that what the comparator network then proves
 * is a contradiction.
 */

#include <gcs/constraints/innards/constraints_test_utils.hh>
#include <gcs/innards/proofs/comparator_network.hh>
#include <gcs/innards/proofs/names_and_ids_tracker.hh>
#include <gcs/innards/proofs/pol_builder.hh>
#include <gcs/innards/proofs/proof_logger.hh>
#include <gcs/innards/proofs/proof_model.hh>

#include <bit>
#include <cstdlib>
#include <iostream>
#include <map>
#include <numeric>
#include <string>
#include <utility>
#include <vector>
#include <version>

#if defined(__cpp_lib_print) && defined(__cpp_lib_format)
#include <print>
#else
#include <fmt/core.h>
#include <fmt/ostream.h>
#endif

using std::cerr;
using std::map;
using std::move;
using std::pair;
using std::string;
using std::to_string;
using std::vector;

#if defined(__cpp_lib_print) && defined(__cpp_lib_format)
using std::println;
#else
using fmt::println;
#endif

using namespace gcs;
using namespace gcs::innards;
using namespace gcs::test_innards;

namespace
{
    auto fail(const string & message) -> void
    {
        println(cerr, "k-D relaxation probe failure: {}", message);
        std::exit(EXIT_FAILURE);
    }

    /// One box: its size on each axis, in axis order, the last of which is the
    /// one the relaxation sums over.
    using Box = vector<int>;

    /* The pairwise `diffn` encoding for k axes, which is `Disjunctive2D`'s own
     * one axis at a time: a reified `before` flag per ordered pair per axis,
     * and one separation clause per unordered pair over all 2k of them. There
     * is no time index anywhere in it, which is the whole point --- the rows
     * the relaxation wants do not exist in the model and have to be derived.
     */
    struct BoxesModel
    {
        /// Position variables, [box][axis].
        vector<vector<SimpleIntegerVariableID>> pos;
        /// before[axis][(i, j)]: box i entirely before box j on that axis.
        vector<map<pair<size_t, size_t>, ProofFlag>> before;
        vector<map<pair<size_t, size_t>, ProofLine>> before_rows;
        vector<map<pair<size_t, size_t>, Integer>> guard_coefficients;
        /// One clause per unordered pair, over every axis's two flags.
        map<pair<size_t, size_t>, ProofLine> separation_clauses;
        int width = 0;
    };

    /* `slice_at` is the point each earlier axis is sliced at; the last axis has
     * no point and gets a window of `[0, window)` instead. A box's domain on an
     * earlier axis is `[t - size + 1, t]`, which is exactly the placements that
     * cover `t` --- so every box is active in the slice under every assignment,
     * and the set the relaxation speaks about is the whole instance.
     */
    auto build_boxes_model(ProofModel & model, NamesAndIDsTracker & tracker, const vector<Box> & boxes, const vector<int> & slice_at, int window)
        -> BoxesModel
    {
        auto n = boxes.size();
        auto axes = boxes.front().size();
        BoxesModel built;
        built.before.resize(axes);
        built.before_rows.resize(axes);
        built.guard_coefficients.resize(axes);

        unsigned long long var_nr = 0;
        for (size_t i = 0; i < n; ++i) {
            vector<SimpleIntegerVariableID> row;
            for (size_t d = 0; d < axes; ++d) {
                SimpleIntegerVariableID v{var_nr++};
                auto name = "p" + to_string(i) + "_" + to_string(d);
                if (d + 1 < axes)
                    model.set_up_integer_variable(v, Integer{slice_at[d] - boxes[i][d] + 1}, Integer{slice_at[d]}, name, std::nullopt);
                else
                    model.set_up_integer_variable(v, 0_i, Integer{window - boxes[i][d]}, name, std::nullopt);
                row.push_back(v);
            }
            built.pos.push_back(move(row));
        }
        built.width = static_cast<int>(std::bit_width(static_cast<unsigned long long>(window)));

        for (size_t d = 0; d < axes; ++d)
            for (size_t i = 0; i < n; ++i)
                for (size_t j = 0; j < n; ++j) {
                    if (i == j)
                        continue;
                    auto flag = model.create_proof_flag("b" + to_string(d) + "_" + to_string(i) + "_" + to_string(j));
                    built.before[d].emplace(pair{i, j}, flag);
                    // before <-> pos_i + size_i <= pos_j, as Disjunctive2D
                    // writes it for a constant size.
                    auto ineq = WPBSum{} + 1_i * built.pos[i][d] + -1_i * built.pos[j][d] <= Integer{-boxes[i][d]};
                    built.guard_coefficients[d].emplace(
                        pair{i, j}, -tracker.reification_shape(ineq, HalfReifyOnConjunctionOf{{flag}}).reif_coefficient);
                    built.before_rows[d].emplace(pair{i, j}, model.add_two_way_reified_constraint(ineq, flag).first);
                }

        for (size_t i = 0; i < n; ++i)
            for (size_t j = i + 1; j < n; ++j) {
                WPBSum clause;
                for (size_t d = 0; d < axes; ++d) {
                    clause += 1_i * built.before[d].at(pair{i, j});
                    clause += 1_i * built.before[d].at(pair{j, i});
                }
                built.separation_clauses.emplace(
                    pair{i, j}, model.add_labelled_constraint("sep" + to_string(i) + "_" + to_string(j), move(clause) >= 1_i));
            }

        return built;
    }

    /* The recursion itself, and the only step that is new above one dimension.
     *
     * For one ordered pair and one earlier axis, refute that axis's `before`
     * flag: its [r] row says `flag -> pos_i + size_i <= pos_j`, and the two
     * boxes' own domain rows say `pos_i >= t - size_i + 1` and `pos_j <= t`,
     * which together leave `M * ~flag >= 1`. Saturating makes that the unit
     * `~flag`. This is `disjunctive_2d.cc`'s `emit_before_pol` with the bounds
     * coming from the model rather than from a search state.
     */
    auto refute_before(ProofLogger & logger, NamesAndIDsTracker & tracker, const BoxesModel & built, size_t d, size_t i, size_t j) -> ProofLine
    {
        auto rows_i = tracker.bound_rows(built.pos[i][d]);
        auto rows_j = tracker.bound_rows(built.pos[j][d]);
        if (! rows_i || ! rows_j)
            fail("a position variable has no bound rows to refute a before flag with");
        PolBuilder pol;
        pol.add(built.before_rows[d].at(pair{i, j}));
        pol.add(rows_i->first);  // pos_i >= its lower bound
        pol.add(rows_j->second); // pos_j <= its upper bound
        pol.saturate();
        return pol.emit(logger, ProofLevel::Top);
    }

    /* The separation clause the last axis is left with. Adding each refuted
     * flag's unit row to the full clause cancels that disjunct, so what comes
     * back is the two-way clause a 1-D pairwise encoding would have written in
     * the first place --- which is exactly what ComparatorNetwork::add_separation
     * wants.
     */
    auto derive_last_axis_clause(ProofLogger & logger, NamesAndIDsTracker & tracker, const BoxesModel & built, size_t i, size_t j) -> ProofLine
    {
        auto axes = built.before.size();
        PolBuilder pol;
        pol.add(built.separation_clauses.at(pair{i, j}));
        for (size_t d = 0; d + 1 < axes; ++d) {
            pol.add(refute_before(logger, tracker, built, d, i, j));
            pol.add(refute_before(logger, tracker, built, d, j, i));
        }
        return pol.emit(logger, ProofLevel::Top);
    }

    /* One instance, one run. `expect_accepted` is false for the control, where
     * the window is wide enough to hold the boxes and the concluding RUP has
     * nothing to close on.
     */
    auto check_relaxation(const vector<Box> & boxes, const vector<int> & slice_at, int window, const string & tag, bool expect_accepted) -> void
    {
        auto axes = boxes.front().size();
        auto proof_name = "kd_relaxation_probe_" + to_string(axes) + "d_" + tag;
        ProofOptions proof_options{proof_name};
        NamesAndIDsTracker tracker(proof_options);
        ProofModel model(proof_options, tracker);
        auto built = build_boxes_model(model, tracker, boxes, slice_at, window);
        model.finalise();

        ProofLogger logger(proof_options, tracker);
        tracker.switch_from_model_to_proof(&logger);
        logger.start_proof(model);
        tracker.emit_delayed_proof_steps();

        auto last = axes - 1;
        ComparatorNetwork network(logger, built.width, 0_i, Integer{window}, ProofLevel::Top);

        vector<ProofWire> wires;
        for (size_t i = 0; i < boxes.size(); ++i) {
            vector<ProofLiteralOrFlag> bits;
            for (Integer b = 0_i; b < tracker.num_bits(built.pos[i][last]); ++b)
                bits.push_back(ProofBitVariable{built.pos[i][last], b, true});
            wires.push_back(network.wire_over(bits));
        }

        for (size_t i = 0; i < boxes.size(); ++i) {
            network.add_task(wires[i], Integer{boxes[i][last]});
            // Unguarded: the boxes' last-axis domains are the window, so
            // fitting inside it is the model's own statement.
            network.set_bounds(wires[i]);
        }

        for (size_t i = 0; i < boxes.size(); ++i)
            for (size_t j = i + 1; j < boxes.size(); ++j) {
                auto clause = derive_last_axis_clause(logger, tracker, built, i, j);
                auto direction = [&](size_t a, size_t b) {
                    return ModelSeparation{
                        built.before[last].at(pair{a, b}), built.before_rows[last].at(pair{a, b}), built.guard_coefficients[last].at(pair{a, b})};
                };
                network.add_separation(wires[i], direction(i, j), wires[j], direction(j, i), clause);
            }

        auto sorted = network.sort(wires);
        (void)network.sum_up(sorted);
        logger.conclude_unsatisfiable(false);
        tracker.finalise();

        auto accepted = run_veripb(proof_name + ".opb", proof_name + ".pbp");
        if (accepted != expect_accepted)
            fail(to_string(axes) + "-D " + tag + ": veripb " + (accepted ? "accepted" : "rejected") + " where it should have done the opposite");
        dispose_of_proof_files(proof_name);
    }

    /// Boxes whose last-axis sizes overrun the window by one, which is the
    /// margin that makes every separation clause load-bearing.
    auto overfull(size_t n, size_t axes) -> pair<vector<Box>, int>
    {
        vector<Box> boxes;
        auto total = 0;
        for (size_t i = 0; i < n; ++i) {
            Box b;
            for (size_t d = 0; d + 1 < axes; ++d)
                b.push_back(2 + static_cast<int>((i + d) % 3));
            auto last_size = 2 + static_cast<int>((i * 5 + 3) % 7);
            b.push_back(last_size);
            total += last_size;
            boxes.push_back(move(b));
        }
        return {boxes, total};
    }
}

auto main(int, char *[]) -> int
{
    if (! can_run_veripb()) {
        println(cerr, "veripb not available, skipping the k-D relaxation probe");
        return EXIT_SUCCESS;
    }

    // Slicing points, one per axis other than the last. Deliberately not all
    // the same and deliberately not zero: a box's domain on an earlier axis is
    // built around its own size, so a shared point still gives every box a
    // different domain, and a non-zero one keeps the refutation from closing by
    // accident on a bound that happens to be zero.
    for (size_t axes = 2; axes <= 4; ++axes) {
        vector<int> slice_at;
        for (size_t d = 0; d + 1 < axes; ++d)
            slice_at.push_back(3 + static_cast<int>(d));

        for (size_t n = 2; n <= 4; ++n) {
            auto [boxes, total] = overfull(n, axes);
            // One unit too little room on the last axis: unsatisfiable, and the
            // relaxation is the only argument that says so.
            check_relaxation(boxes, slice_at, total - 1, "n" + to_string(n) + "_tight", true);
            // The control: one unit of slack, so the boxes fit and the endgame
            // has nothing to refute. Without it a bug that made the derivation
            // vacuously contradictory would pass the test above.
            check_relaxation(boxes, slice_at, total + 1, "n" + to_string(n) + "_slack", false);
        }
    }

    println(cerr, "k-D relaxation probe: the recursion carries for 2, 3 and 4 axes");
    return EXIT_SUCCESS;
}
