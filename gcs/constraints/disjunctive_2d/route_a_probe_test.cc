/* Route A for the 2-D cumulative relaxation (#984): the FLAGGED capacity row
 * `sum_i h_i * active_{i,t} <= H`, derived outright rather than per firing.
 *
 * WHY. Route B (#972, route_b_probe_test.cc) lands on a statement about the
 * *mandatory* set, which is all time-tabling needs. Every energetic rule sums a
 * capacity row over a window instead, over tasks only *possibly* active at each
 * time in it, and for that it needs a row with an activity flag per task.
 *
 * HOW. Mint `active_{i,t}` by redundance over the order literals, then give the
 * comparator network an OPTIONAL task per rectangle: a position muxed on the
 * activity literal (`active ? y_i : H`) and a duration `h_i * active`. An
 * inactive rectangle becomes a zero-duration dummy parked at the top of the
 * window, every pair is then separated under every assignment, and the
 * endgame telescopes to the flagged row with no guard left over. The network
 * carries a parking row (`wire + H * duration >= H`) in place of positivity,
 * which is what lets a zero duration through the gap lemma.
 *
 * HOW IT IS CHECKED. The model is satisfiable and contains a placement that
 * stacks every rectangle over t filling the window exactly, so a row one unit
 * stronger than the claim is false and must be rejected; and the row has to
 * refute the node route B refuted, as its first use.
 */

#include <gcs/constraints/innards/constraints_test_utils.hh>
#include <gcs/innards/proofs/comparator_network.hh>
#include <gcs/innards/proofs/names_and_ids_tracker.hh>
#include <gcs/innards/proofs/pol_builder.hh>
#include <gcs/innards/proofs/proof_logger.hh>
#include <gcs/innards/proofs/proof_model.hh>

#include <bit>
#include <cstdlib>
#include <filesystem>
#include <iostream>
#include <map>
#include <optional>
#include <random>
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
        println(cerr, "route A probe failure: {}", message);
        std::exit(EXIT_FAILURE);
    }

    struct Rect
    {
        int w, h;
        /// A y domain narrower than the window, or -1 for the whole of it.
        int y_min = -1, y_max = -1;
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

    auto build(ProofModel & model, NamesAndIDsTracker & tracker, const vector<Rect> & rects, int x_hi, int y_lo, int y_hi) -> Model2D
    {
        auto n = rects.size();
        Model2D built;
        unsigned long long var_nr = 0;
        for (size_t i = 0; i < n; ++i) {
            SimpleIntegerVariableID x{var_nr++};
            model.set_up_integer_variable(x, 0_i, Integer{x_hi - rects[i].w}, "x" + to_string(i), std::nullopt);
            built.xs.push_back(x);
            SimpleIntegerVariableID y{var_nr++};
            model.set_up_integer_variable(y, Integer{rects[i].y_min >= 0 ? rects[i].y_min : y_lo},
                Integer{rects[i].y_max >= 0 ? rects[i].y_max : y_hi - rects[i].h}, "y" + to_string(i), std::nullopt);
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

    /* Refute one x-disjunct at t: the flag's [r] row says `x_i + w_i <= x_j`,
     * against `x_i >= t - w_i + 1` and `x_j <= t`. What comes back is a clause
     * over ~flag and the two order literals.
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

    struct Outcome
    {
        bool accepted;
        long long proof_bytes;
    };

    /* Derive the flagged row at t, then state `claim` about it: either the row
     * itself at `H - claim_offset`, or (`use_it`) the conclusion that no node
     * can put every rectangle over t.
     */
    auto check_route_a(const vector<Rect> & rects, int t, int x_hi, int y_hi, const string & tag, int claim_offset, bool use_it,
        ComparatorNetworkMutation mutation = comparator_network_mutation::None{}, bool skip_network = false, int y_lo = 0) -> Outcome
    {
        auto proof_name = "route_a_probe_" + tag;
        ProofOptions proof_options{proof_name};
        NamesAndIDsTracker tracker(proof_options);
        ProofModel model(proof_options, tracker);
        auto built = build(model, tracker, rects, x_hi, y_lo, y_hi);
        model.finalise();

        ProofLogger logger(proof_options, tracker);
        tracker.switch_from_model_to_proof(&logger);
        logger.start_proof(model);
        tracker.emit_delayed_proof_steps();

        auto n = rects.size();
        auto lower = [&](size_t i) { return IntegerVariableID{built.xs[i]} >= Integer{t - rects[i].w + 1}; };
        auto upper = [&](size_t i) { return IntegerVariableID{built.xs[i]} < Integer{t + 1}; };

        // active_{i,t} <-> the rectangle's x-extent covers t.
        vector<ProofFlag> active;
        for (size_t i = 0; i < n; ++i) {
            WPBSum covers;
            add_term_to(covers, 1_i, lower(i));
            add_term_to(covers, 1_i, upper(i));
            active.push_back(std::get<0>(logger.create_proof_flag_reifying(move(covers) >= 2_i, "act" + to_string(i), ProofLevel::Top)));
        }

        ComparatorNetwork net(logger, built.width, Integer{y_lo}, Integer{y_hi}, ProofLevel::Top, mutation);
        std::optional<ProofLine> derived;
        if (! skip_network) {

            vector<ProofWire> positions;
            for (size_t i = 0; i < n; ++i) {
                vector<ProofLiteralOrFlag> bits;
                for (Integer b = 0_i; b < tracker.num_bits(built.ys[i]); ++b)
                    bits.push_back(ProofBitVariable{built.ys[i], b, true});
                positions.push_back(net.add_optional_task(ProofLiteralOrFlag{active[i]}, net.wire_over(bits), Integer{rects[i].h}, "p"));
            }

            for (size_t i = 0; i < n; ++i)
                for (size_t j = i + 1; j < n; ++j) {
                    // Both active => y-separated: the pair's 4-way clause with its
                    // two x-disjuncts refuted at t, then the order literals traded
                    // for the activity flags.
                    PolBuilder clause;
                    clause.add(built.clauses.at(pair{i, j}));
                    clause.add(refute_x(logger, tracker, built, rects, t, i, j));
                    clause.add(refute_x(logger, tracker, built, rects, t, j, i));
                    (void)clause.emit(logger, ProofLevel::Temporary);
                    WPBSum both_active;
                    both_active += 1_i * ! active[i];
                    both_active += 1_i * ! active[j];
                    both_active += 1_i * built.by.at(pair{i, j});
                    both_active += 1_i * built.by.at(pair{j, i});
                    auto line = logger.emit_rup_proof_line(move(both_active) >= 1_i, ProofLevel::Top);

                    auto direction = [&](size_t a, size_t b) {
                        return ModelSeparation{built.by.at(pair{a, b}), built.by_rows.at(pair{a, b}), built.by_guards.at(pair{a, b})};
                    };
                    net.add_optional_separation(positions[i], direction(i, j), positions[j], direction(j, i), line);
                }

            derived = net.sum_up(net.sort(positions));
        }

        if (use_it) {
            WPBSum conclusion;
            for (size_t i = 0; i < n; ++i) {
                conclusion += 1_i * ! lower(i);
                conclusion += 1_i * ! upper(i);
            }
            logger.emit_rup_proof_line(move(conclusion) >= 1_i, ProofLevel::Current);
        }
        else {
            WPBSum row;
            for (size_t i = 0; i < n; ++i)
                row += Integer{rects[i].h} * active[i];
            // Checked as implied by the endgame's own line, not by RUP: the row
            // is a knapsack-shaped constraint whose negation propagates nothing
            // in general, so RUP rejects it even when it is literally the line
            // above. With no network there is no line, and RUP is all there is.
            if (derived)
                logger.emit(ImpliesProofRule{*derived}, move(row) <= Integer{y_hi - y_lo - claim_offset}, ProofLevel::Current);
            else
                logger.emit_rup_proof_line(move(row) <= Integer{y_hi - y_lo - claim_offset}, ProofLevel::Current);
        }

        logger.conclude_none();
        tracker.finalise();

        std::error_code ec;
        auto bytes = static_cast<long long>(std::filesystem::file_size(proof_name + ".pbp", ec));
        auto accepted = run_veripb("--force-checked-deletion", proof_name + ".opb", proof_name + ".pbp");
        return Outcome{accepted, bytes};
    }

    auto expect(const Outcome & outcome, bool accepted, const string & tag) -> void
    {
        if (outcome.accepted != accepted)
            fail(tag + ": veripb " + (outcome.accepted ? "accepted" : "rejected") + " where it should have done the opposite");
        dispose_of_proof_files("route_a_probe_" + tag);
    }
}

auto main(int argc, char * argv[]) -> int
{
    if (! can_run_veripb()) {
        println(cerr, "veripb not available, skipping the route A probe");
        return EXIT_SUCCESS;
    }

    // Heights 3 + 2 + 4 + 3 = 12 against H = 9: not all four fit over t = 4,
    // but the first three do exactly (the fourth moved clear in x), so the
    // flagged row is tight, one unit stronger is false, and without the
    // network nothing reaches it.
    vector<Rect> four{{3, 3}, {4, 2}, {3, 4}, {2, 3}};
    auto row = check_route_a(four, 4, 12, 9, "row", 0, false);
    println(cerr, "route A probe: flagged row over four rectangles, {} proof bytes", row.proof_bytes);
    expect(row, true, "row");
    expect(check_route_a(four, 4, 12, 9, "row_too_strong", 1, false), false, "row_too_strong");
    expect(check_route_a(four, 4, 12, 9, "row_no_network", 0, false, comparator_network_mutation::None{}, true), false, "row_no_network");
    // The same over a window [3, 12): parking's coefficient is the window's
    // width, and the endgame's bottom bound is load-bearing.
    expect(check_route_a(four, 4, 12, 12, "row_offset", 0, false, comparator_network_mutation::None{}, false, 3), true, "row_offset");
    expect(check_route_a(four, 4, 12, 12, "row_offset_too_strong", 1, false, comparator_network_mutation::None{}, false, 3), false,
        "row_offset_too_strong");
    // Parking is what carries a zero duration through the gap lemma.
    expect(check_route_a(four, 4, 12, 9, "drop_parking", 0, false, comparator_network_mutation::DropParking{}), false, "drop_parking");

    // A height equal to the wires' span: window [0, 7) is three bits, and a
    // rectangle of height 7 pinned at y = 0. Its upper-bound half degenerates
    // and its both-active clause loses ~active; both must still close.
    vector<Rect> full_span{{2, 7, 0, 0}, {3, 2}, {2, 3}};
    expect(check_route_a(full_span, 4, 12, 7, "full_span", 0, false), true, "full_span");
    expect(check_route_a(full_span, 4, 12, 7, "full_span_too_strong", 1, false), false, "full_span_too_strong");

    // y domains strictly inside the window, so the start bounds are RUPs
    // through the bit encoding's bound rows rather than those rows themselves.
    vector<Rect> inside{{3, 3, 2, 3}, {4, 2, 1, 5}, {3, 4, 0, 4}, {2, 3, 3, 6}};
    expect(check_route_a(inside, 4, 12, 9, "inside", 0, false), true, "inside");

    // First use: three rectangles of total height 9 in H = 8 cannot all
    // cover t, which is the node route B refutes.
    vector<Rect> three{{3, 3}, {4, 2}, {3, 4}};
    expect(check_route_a(three, 4, 12, 8, "refutes", 0, true), true, "refutes");
    expect(check_route_a(three, 4, 12, 9, "refutes_slack", 0, true), false, "refutes_slack");
    expect(check_route_a(three, 4, 12, 8, "refutes_no_network", 0, true, comparator_network_mutation::None{}, true), false, "refutes_no_network");

    // Random shapes: the row must verify for every one. Where it says
    // something (total height over H) the same claim without the network is
    // tried too, but only counted: propagation reaches it on its own for two
    // rectangles, and there is no reason it cannot for some larger shapes.
    auto count = argc > 1 ? std::atoi(argv[1]) : 12;
    auto max_n = argc > 2 ? std::atoi(argv[2]) : 5;
    std::mt19937 rng(984);
    auto nontrivial = 0, needed_network = 0;
    for (int k = 0; k < count; ++k) {
        auto n = std::uniform_int_distribution<int>{2, max_n}(rng);
        vector<Rect> rects;
        auto total = 0, tallest = 0;
        for (int i = 0; i < n; ++i) {
            rects.push_back(Rect{std::uniform_int_distribution<int>{1, 4}(rng), std::uniform_int_distribution<int>{1, 6}(rng)});
            total += rects.back().h;
            tallest = std::max(tallest, rects.back().h);
        }
        auto height = std::uniform_int_distribution<int>{tallest, std::max(tallest, total - 1)}(rng);
        // Every third window starts above zero, where parking's coefficient
        // is the window's width rather than its end.
        auto y_lo = (k % 3 == 2) ? std::uniform_int_distribution<int>{1, 5}(rng) : 0;
        auto y_hi = y_lo + height;
        auto t = std::uniform_int_distribution<int>{0, 7}(rng);
        auto tag = "random" + to_string(k);
        auto outcome = check_route_a(rects, t, 12, y_hi, tag, 0, false, comparator_network_mutation::None{}, false, y_lo);
        println(cerr, "route A probe: {} n={} window=[{},{}) total={} t={}: {} bytes", tag, n, y_lo, y_hi, total, t, outcome.proof_bytes);
        expect(outcome, true, tag);
        if (total > height) {
            ++nontrivial;
            auto control = check_route_a(rects, t, 12, y_hi, tag + "_no_network", 0, false, comparator_network_mutation::None{}, true, y_lo);
            if (! control.accepted)
                ++needed_network;
            dispose_of_proof_files("route_a_probe_" + tag + "_no_network");
        }
    }
    println(cerr, "route A probe: {} of {} nontrivial random rows needed the network", needed_network, nontrivial);

    println(cerr, "route A probe: the flagged row derives");
    return EXIT_SUCCESS;
}
