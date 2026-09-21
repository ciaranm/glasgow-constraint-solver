/* Route B for the 2-D cumulative relaxation (#972): a per-firing guarded
 * certificate, rather than a capacity row cached at Top.
 *
 * WHAT ROUTE B IS. At a search node a propagator names a set of rectangles
 * whose mandatory x-parts all cover a time t. Their activity at t is forced by
 * their *current bounds*, so it needs no activity flag: the two x-disjuncts of
 * each pair's separation clause are refuted by a `pol` over the flag's [r] row
 * and the two order literals the reason carries, leaving the pair y-separated.
 * `ComparatorNetwork` then sorts their y positions and telescopes, and the row
 * it lands on says the y window is at least as wide as the total height in it
 * --- which the firing says it is not.
 *
 * WHY IT IS WORTH PROBING BEFORE BUILDING. 1D Disjunctive already drives the
 * network exactly this way per firing (`disjunctive.cc`, emit_sorting_certificate):
 * Temporary level, `assume` a guard built from the reason, model separations,
 * `sum_up`. The one thing 2-D has that 1-D does not is that the separation
 * CLAUSE is not a model row. In 1-D `before_ij + before_ji >= 1` is in the OPB;
 * in 2-D the two-way clause has to be derived from the four-way one, and what
 * comes out carries the reason's order literals. So the question this probe
 * settles is whether the network can consume a separation clause that is
 * guarded rather than outright.
 *
 * HOW IT IS CHECKED. The model is satisfiable, so nothing here can pass
 * vacuously: the only thing to conclude is the clause saying the node's own
 * bounds cannot all hold, and the control --- the same node with one unit of
 * slack in the y window --- must fail to conclude it.
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
#include <string>
#include <utility>
#include <variant>
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
        println(cerr, "route B probe failure: {}", message);
        std::exit(EXIT_FAILURE);
    }

    struct Rect
    {
        int w, h;
    };

    /// The pairwise diffn encoding for two axes, with WIDE x domains: the node
    /// below narrows them, and the model stays satisfiable so that nothing can
    /// pass vacuously.
    struct Model2D
    {
        vector<SimpleIntegerVariableID> xs, ys;
        map<pair<size_t, size_t>, ProofFlag> bx, by;
        map<pair<size_t, size_t>, ProofLine> bx_rows, by_rows;
        map<pair<size_t, size_t>, Integer> by_guards;
        map<pair<size_t, size_t>, ProofLine> clauses;
        int width = 0;
    };

    auto build(ProofModel & model, NamesAndIDsTracker & tracker, const vector<Rect> & rects, int x_hi, int y_hi) -> Model2D
    {
        auto n = rects.size();
        Model2D built;
        unsigned long long var_nr = 0;
        for (size_t i = 0; i < n; ++i) {
            SimpleIntegerVariableID x{var_nr++};
            model.set_up_integer_variable(x, 0_i, Integer{x_hi - rects[i].w}, "x" + to_string(i), std::nullopt);
            built.xs.push_back(x);
            SimpleIntegerVariableID y{var_nr++};
            model.set_up_integer_variable(y, 0_i, Integer{y_hi - rects[i].h}, "y" + to_string(i), std::nullopt);
            built.ys.push_back(y);
        }
        built.width = static_cast<int>(std::bit_width(static_cast<unsigned long long>(y_hi)));

        auto axis = [&](const vector<SimpleIntegerVariableID> & pos, auto size_of, const string & stem, map<pair<size_t, size_t>, ProofFlag> & flags,
                        map<pair<size_t, size_t>, ProofLine> & rows, map<pair<size_t, size_t>, Integer> * guards) {
            for (size_t i = 0; i < pos.size(); ++i)
                for (size_t j = 0; j < pos.size(); ++j) {
                    if (i == j)
                        continue;
                    auto flag = model.create_proof_flag(stem + to_string(i) + "_" + to_string(j));
                    flags.emplace(pair{i, j}, flag);
                    auto ineq = WPBSum{} + 1_i * pos[i] + -1_i * pos[j] <= Integer{-size_of(i)};
                    if (guards)
                        guards->emplace(pair{i, j}, -tracker.reification_shape(ineq, HalfReifyOnConjunctionOf{{flag}}).reif_coefficient);
                    rows.emplace(pair{i, j}, model.add_two_way_reified_constraint(ineq, flag).first);
                }
        };
        axis(built.xs, [&](size_t i) { return rects[i].w; }, "bx", built.bx, built.bx_rows, nullptr);
        axis(built.ys, [&](size_t i) { return rects[i].h; }, "by", built.by, built.by_rows, &built.by_guards);

        for (size_t i = 0; i < n; ++i)
            for (size_t j = i + 1; j < n; ++j) {
                WPBSum clause;
                clause += 1_i * built.bx.at(pair{i, j});
                clause += 1_i * built.bx.at(pair{j, i});
                clause += 1_i * built.by.at(pair{i, j});
                clause += 1_i * built.by.at(pair{j, i});
                built.clauses.emplace(pair{i, j}, model.add_labelled_constraint("sep" + to_string(i) + "_" + to_string(j), move(clause) >= 1_i));
            }
        return built;
    }

    /* The node: every rectangle's x is narrowed to the placements whose
     * mandatory part covers t, which for a rectangle of width w is
     * [t - w + 1, t]. Those bounds are the reason, as a propagator's
     * generic_reason would give them.
     */
    auto node_reason(const Model2D & built, const vector<Rect> & rects, int t) -> vector<IntegerVariableCondition>
    {
        vector<IntegerVariableCondition> reason;
        for (size_t i = 0; i < built.xs.size(); ++i) {
            reason.push_back(IntegerVariableID{built.xs[i]} >= Integer{t - rects[i].w + 1});
            reason.push_back(IntegerVariableID{built.xs[i]} < Integer{t + 1});
        }
        return reason;
    }

    /* Refute one x-disjunct: the flag's [r] row says `x_i + w_i <= x_j`, and
     * the node's bounds say `x_i >= t - w_i + 1` and `x_j <= t`, which leave
     * `M * ~flag >= 1` before saturation. What comes back is a clause over
     * ~flag and the two order literals --- guarded by the reason, in other
     * words, which is the whole difference from the 1-D case.
     */
    auto refute_x(ProofLogger & logger, NamesAndIDsTracker & tracker, const Model2D & built, const vector<Rect> & rects, int t, size_t i, size_t j)
        -> ProofLine
    {
        PolBuilder pol;
        pol.add(built.bx_rows.at(pair{i, j}));
        auto add_defining = [&](const IntegerVariableCondition & cond) {
            auto item = tracker.need_pol_item_defining_literal(cond);
            if (auto * line = std::get_if<ProofLine>(&item))
                pol.add(*line);
        };
        add_defining(IntegerVariableID{built.xs[i]} >= Integer{t - rects[i].w + 1});
        add_defining(IntegerVariableID{built.xs[j]} < Integer{t + 1});
        pol.saturate();
        return pol.emit(logger, ProofLevel::Temporary);
    }

    auto check_route_b(
        const vector<Rect> & rects, int t, int x_hi, int y_hi, const string & tag, bool expect_accepted, bool guarded_separations = true) -> void
    {
        auto proof_name = "route_b_probe_" + tag;
        ProofOptions proof_options{proof_name};
        NamesAndIDsTracker tracker(proof_options);
        ProofModel model(proof_options, tracker);
        auto built = build(model, tracker, rects, x_hi, y_hi);
        model.finalise();

        ProofLogger logger(proof_options, tracker);
        tracker.switch_from_model_to_proof(&logger);
        logger.start_proof(model);
        tracker.emit_delayed_proof_steps();

        auto reason = node_reason(built, rects, t);

        ComparatorNetwork net(logger, built.width, 0_i, Integer{y_hi}, ProofLevel::Temporary);

        // The separations here are facts about the node, not about the model,
        // so the network has to be told what they rest on --- the same shape
        // 1D's overload certificate uses for its window bounds. The y bounds
        // below are model facts and would need no guard; carrying it on them
        // too is weaker and costs nothing.
        WPBSum guard;
        for (const auto & lit : reason)
            add_term_to(guard, net.big(), ! lit);
        if (guarded_separations)
            net.assume_with_guarded_separations(guard);
        else
            net.assume(guard);

        vector<ProofWire> wires;
        for (size_t i = 0; i < rects.size(); ++i) {
            vector<ProofLiteralOrFlag> bits;
            for (Integer b = 0_i; b < tracker.num_bits(built.ys[i]); ++b)
                bits.push_back(ProofBitVariable{built.ys[i], b, true});
            wires.push_back(net.wire_over(bits));
        }
        for (size_t i = 0; i < rects.size(); ++i) {
            net.add_task(wires[i], Integer{rects[i].h});
            // The y window is the rectangles' own domain extent, a model fact,
            // so these bounds need no guard. Only the separations are stateful.
            net.set_bounds(wires[i]);
        }

        for (size_t i = 0; i < rects.size(); ++i)
            for (size_t j = i + 1; j < rects.size(); ++j) {
                PolBuilder clause;
                clause.add(built.clauses.at(pair{i, j}));
                clause.add(refute_x(logger, tracker, built, rects, t, i, j));
                clause.add(refute_x(logger, tracker, built, rects, t, j, i));
                // The refutations bring in only *this pair's* order literals,
                // so each pair's clause is guarded by a different subset of the
                // reason. The network's guard is one uniform sum, and a goal
                // carrying a literal no half carries cannot cancel it --- so
                // weaken every clause up to the whole reason with literal
                // axioms, which add the term without moving the degree.
                for (size_t k = 0; k < rects.size(); ++k) {
                    if (k == i || k == j)
                        continue;
                    clause.add(! tracker.xliteral_for_ensuring(built.xs[k] >= Integer{t - rects[k].w + 1}), 1_i, tracker);
                    clause.add(tracker.xliteral_for_ensuring(built.xs[k] >= Integer{t + 1}), 1_i, tracker);
                }
                auto derived = clause.emit(logger, ProofLevel::Temporary);

                auto direction = [&](size_t a, size_t b) {
                    return ModelSeparation{built.by.at(pair{a, b}), built.by_rows.at(pair{a, b}), built.by_guards.at(pair{a, b})};
                };
                net.add_separation(wires[i], direction(i, j), wires[j], direction(j, i), derived);
            }

        (void)net.sum_up(net.sort(wires));

        // The conclusion a firing would draw: the node's bounds cannot all
        // hold. Under the negated clause every reason literal is true, the
        // guards on the row above vanish, and what is left is the false
        // statement that the window holds the work.
        WPBSum conclusion;
        for (const auto & lit : reason)
            conclusion += 1_i * ! lit;
        logger.emit_rup_proof_line(move(conclusion) >= 1_i, ProofLevel::Current);

        logger.conclude_none();
        tracker.finalise();

        auto accepted = run_veripb(proof_name + ".opb", proof_name + ".pbp");
        if (accepted != expect_accepted)
            fail(tag + ": veripb " + (accepted ? "accepted" : "rejected") + " where it should have done the opposite");
        dispose_of_proof_files(proof_name);
    }
}

auto main(int, char *[]) -> int
{
    if (! can_run_veripb()) {
        println(cerr, "veripb not available, skipping the route B probe");
        return EXIT_SUCCESS;
    }

    // Three rectangles whose heights overrun the y window by one when all
    // three are forced to cover t on the x axis.
    vector<Rect> rects{{3, 3}, {4, 2}, {3, 4}};
    auto total = 0;
    for (const auto & r : rects)
        total += r.h;

    check_route_b(rects, 4, 12, total - 1, "tight", true);
    // The control that says the tight run means something: one unit of slack
    // and the rectangles fit, so the node's bounds are consistent and the
    // conclusion cannot be drawn.
    check_route_b(rects, 4, 12, total + 1, "slack", false);
    // And the control that says the new mode is load-bearing: the same
    // instance driven through plain `assume`, which guards the bounds but not
    // the clauses, is rejected --- the gap lemma's case split is left holding
    // the guard it has no goal term to cancel against.
    check_route_b(rects, 4, 12, total - 1, "unguarded_clauses", false, false);

    println(cerr, "route B probe: the per-firing guarded certificate carries");
    return EXIT_SUCCESS;
}
