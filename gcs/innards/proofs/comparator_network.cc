#include <gcs/innards/proofs/comparator_network.hh>
#include <gcs/innards/proofs/names_and_ids_tracker.hh>
#include <gcs/innards/proofs/pol_builder.hh>
#include <gcs/innards/proofs/proof_error.hh>

#include <algorithm>
#include <map>
#include <optional>
#include <string>
#include <utility>

using namespace gcs;
using namespace gcs::innards;

using std::holds_alternative;
using std::map;
using std::max;
using std::move;
using std::optional;
using std::pair;
using std::string;
using std::to_string;
using std::vector;

ComparatorNetwork::ComparatorNetwork(
    ProofLogger & logger, int width, Integer window_lo, Integer window_hi, ProofLevel level, ComparatorNetworkMutation mutation) :
    _logger(logger), _width(width), _window_lo(window_lo), _window_hi(window_hi), _level(level), _mutation(mutation),
    _span((Integer{1LL << width}) - 1_i),
    // Twice a wire's span, so that a transfer lemma --- which adds two record
    // rows and divides by a separation row's guard coefficient --- comes out at
    // exactly one; and at least the window's end, so that a model row's own
    // guard coefficient can be raised to it. Larger would still be sound and
    // would make that division land short.
    _big(max(2_i * ((Integer{1LL << width}) - 1_i), window_hi)),
    // Every case split divides by this, which is generous enough for the
    // largest guard coefficient any lemma below accumulates (the gap lemma's
    // `big + 3 * span`). Generous is safe because the negated goal cancels
    // every record term exactly, so dividing can only touch the surviving guard
    // literal.
    _div(4_i * _big + 4_i * _span)
{
}

auto ComparatorNetwork::width() const -> int
{
    return _width;
}

auto ComparatorNetwork::span() const -> Integer
{
    return _span;
}

auto ComparatorNetwork::big() const -> Integer
{
    return _big;
}

auto ComparatorNetwork::next_name(const string & stem) -> string
{
    return stem + to_string(_counter++);
}

auto ComparatorNetwork::fresh_wire(const string & stem) -> ProofWire
{
    ProofWire wire{.id = _next_wire_id++, .bits = {}};
    auto name = next_name(stem);
    for (auto t = 0; t < _width; ++t)
        wire.bits.push_back(ProofLiteralOrFlag{_logger.create_proof_flag(name + "b" + to_string(t))});
    return wire;
}

auto ComparatorNetwork::wire_over(const vector<ProofLiteralOrFlag> & bits) -> ProofWire
{
    if (static_cast<int>(bits.size()) > _width)
        throw ProofError{"comparator network wire wider than the network"};

    // Padding a narrower variable is two wasted mux clauses per padded bit ---
    // the two that place a constant-zero input into the output are tautologies
    // --- and the other two are what force the output's high bits to zero, so
    // the padding is not free but is very nearly so, and it is what lets a
    // window hold tasks whose starts were encoded to different widths.
    auto padded = bits;
    while (static_cast<int>(padded.size()) < _width)
        padded.push_back(ProofLiteralOrFlag{ProofLiteral{FalseLiteral{}}});
    return ProofWire{.id = _next_wire_id++, .bits = move(padded)};
}

auto ComparatorNetwork::terms(const ProofWire & wire, Integer sign) const -> WPBSum
{
    WPBSum sum;
    add_terms(sum, wire, sign);
    return sum;
}

auto ComparatorNetwork::add_terms(WPBSum & sum, const ProofWire & wire, Integer sign) const -> void
{
    for (auto t = 0; t < _width; ++t)
        add_term_to(sum, sign * Integer{1LL << t}, wire.bits[t]);
}

auto ComparatorNetwork::pin(const ProofWire & wire, Integer value) -> void
{
    for (auto t = 0; t < _width; ++t) {
        auto on = 0 != ((value.raw_value >> t) & 1);
        WPBSum sum;
        add_term_to(sum, 1_i, on ? wire.bits[t] : ! wire.bits[t]);
        _logger.emit_red_proof_line(
            move(sum) >= 1_i, {{wire.bits[t], on ? ProofLiteralOrFlag{TrueLiteral{}} : ProofLiteralOrFlag{FalseLiteral{}}}}, _level);
    }
}

auto ComparatorNetwork::add_task(const ProofWire & start, Integer duration) -> void
{
    if (duration < 1_i)
        throw ProofError{"a zero-duration task does not participate in a comparator network"};

    auto wire = fresh_wire("d");
    pin(wire, duration);
    _duration.emplace(start.id, wire);

    // `duration >= 1`, load-bearing in the gap lemma, and the one place where
    // unequal durations need something an equal-duration construction gets for
    // free. "A starts at or after B, so A is not the one that finishes first"
    // is only valid if B's duration is positive: with the duration subtracted
    // out of the separation row the degree drops to zero, and a zero-duration
    // task really can be "before" a task it starts level with. With equal
    // durations this never comes up, the duration sitting in the degree as a
    // constant.
    _positivity.emplace(wire.id, _logger.emit_rup_proof_line(terms(wire, 1_i) >= 1_i, _level));
    // And its upper bound, which is what makes a model row duration-relative.
    // The pins are units, so this closes at once.
    _duration_upper.emplace(wire.id, _logger.emit_rup_proof_line(terms(wire, -1_i) >= -duration, _level));
}

auto ComparatorNetwork::assume(const WPBSum & guard) -> void
{
    _guard = guard;
}

auto ComparatorNetwork::set_bounds(const ProofWire & start) -> void
{
    auto guarded = [&](WPBSum sum) {
        for (const auto & term : _guard.terms)
            sum += term;
        return sum;
    };

    WPBSum fits;
    add_terms(fits, start, -1_i);
    add_terms(fits, _duration.at(start.id), -1_i);
    _upper.insert_or_assign(start.id, _logger.emit_rup_proof_line(guarded(move(fits)) >= -_window_hi, _level));

    _lower.insert_or_assign(start.id, _logger.emit_rup_proof_line(guarded(terms(start, 1_i)) >= _window_lo, _level));
}

auto ComparatorNetwork::add_separation(
    const ProofWire & x, const ModelSeparation & x_first, const ProofWire & y, const ModelSeparation & y_first, ProofLine clause) -> void
{
    auto adopt = [&](const ProofWire & first, const ModelSeparation & direction) -> ProofLine {
        if (direction.guard_coefficient > _big)
            throw ProofError{"comparator network guard coefficient is too small for the model's rows"};

        // Subtract the pinned duration, putting the model's `y - x >= p_x` in
        // the duration-relative form the network maintains across a mux.
        PolBuilder relative;
        relative.add(direction.row).add(_duration_upper.at(_duration.at(first.id).id));
        auto result = relative.emit(_logger, _level);

        // Then raise the row's own big-M to the network's, using the literal
        // axiom `~flag >= 0`, so that separation rows all carry the same guard
        // coefficient whether they came from the model or from a comparator.
        // Per direction, since the two halves of a pair rarely agree.
        if (direction.guard_coefficient == _big)
            return result;
        PolBuilder raised;
        raised
            .add(! _logger.names_and_ids_tracker().xliteral_for(direction.flag), _big - direction.guard_coefficient, _logger.names_and_ids_tracker())
            .add(result);
        return raised.emit(_logger, _level);
    };

    record_separation(x, adopt(x, x_first), y, adopt(y, y_first), clause);
}

auto ComparatorNetwork::record_separation(
    const ProofWire & x, ProofLine when_first, const ProofWire & y, ProofLine when_other_first, ProofLine clause) -> void
{
    auto key = pair{std::min(x.id, y.id), std::max(x.id, y.id)};
    _separations.insert_or_assign(key, Separation{.first = {{x.id, when_first}, {y.id, when_other_first}}, .clause = clause});
}

auto ComparatorNetwork::separation_between(const ProofWire & x, const ProofWire & y) const -> const Separation &
{
    return _separations.at(pair{std::min(x.id, y.id), std::max(x.id, y.id)});
}

auto ComparatorNetwork::compare(const ProofWire & a, const ProofWire & b, const string & stem) -> Comparator
{
    auto selector = _logger.create_proof_flag(next_name(stem) + "sel");
    auto d_a = _duration.at(a.id), d_b = _duration.at(b.id);
    auto lo = fresh_wire(stem + "lo"), hi = fresh_wire(stem + "hi");
    auto d_lo = fresh_wire(stem + "dlo"), d_hi = fresh_wire(stem + "dhi");

    // The selector, reifying `a <= b`. Both proofgoals autoprove: the negated
    // goal pins the selector, since a wire's span cannot reach the guard
    // coefficient, and the surviving row is then the goal itself.
    WPBSum fwd;
    add_terms(fwd, b, 1_i);
    add_terms(fwd, a, -1_i);
    fwd += _big * ! selector;
    auto forward = _logger.emit_red_proof_line(move(fwd) >= 0_i, {{selector, ProofLiteralOrFlag{FalseLiteral{}}}}, _level);

    WPBSum rev;
    add_terms(rev, a, 1_i);
    add_terms(rev, b, -1_i);
    rev += _big * selector;
    auto reverse = _logger.emit_red_proof_line(move(rev) >= 1_i, {{selector, ProofLiteralOrFlag{TrueLiteral{}}}}, _level);

    // The bitwise muxes: `out_t <-> (sel AND on_true_t) OR (~sel AND
    // on_false_t)`, four clauses per bit, each a `red` whose single-variable
    // witness makes both proofgoals autoprove. Both the start and the duration
    // are muxed on the one selector, because a comparator permutes whole tasks:
    // without the durations following their starts the endgame cannot say what
    // the gap between two sorted wires is.
    //
    // Every clause is introduced before any record row is built from them. A
    // record row is a statement about an output's *value*, so a later red
    // pinning one of that output's bits does not preserve it --- put one in the
    // database early and the next bit's clause has a proofgoal it cannot
    // discharge.
    using MuxClauses = vector<vector<ProofLine>>;
    auto introduce = [&](const ProofWire & out, const ProofWire & on_true, const ProofWire & on_false) -> MuxClauses {
        MuxClauses clauses;
        for (auto t = 0; t < _width; ++t) {
            const auto &out_bit = out.bits[t], &on_t = on_true.bits[t], &on_f = on_false.bits[t];
            vector<ProofLine> per_bit;
            for (auto which = 0; which < 4; ++which) {
                WPBSum clause;
                switch (which) {
                case 0: clause += 1_i * ! selector, add_term_to(clause, 1_i, ! on_t), add_term_to(clause, 1_i, out_bit); break;
                case 1: clause += 1_i * selector, add_term_to(clause, 1_i, ! on_f), add_term_to(clause, 1_i, out_bit); break;
                case 2: clause += 1_i * ! selector, add_term_to(clause, 1_i, on_t), add_term_to(clause, 1_i, ! out_bit); break;
                default: clause += 1_i * selector, add_term_to(clause, 1_i, on_f), add_term_to(clause, 1_i, ! out_bit); break;
                }
                auto witness = (which < 2) ? ProofLiteralOrFlag{TrueLiteral{}} : ProofLiteralOrFlag{FalseLiteral{}};
                per_bit.push_back(_logger.emit_red_proof_line(move(clause) >= 1_i, {{out_bit, witness}}, _level));
            }
            clauses.push_back(move(per_bit));
        }
        return clauses;
    };

    auto lo_clauses = introduce(lo, a, b);
    auto hi_clauses = introduce(hi, b, a);
    auto d_lo_clauses = introduce(d_lo, d_a, d_b);
    auto d_hi_clauses = introduce(d_hi, d_b, d_a);

    // Per output, the four record rows: multiply the bit-`t` mux clause by
    // `2^t` and sum, which turns a family of clauses about bits into one
    // inequality about the wires they encode. The guard coefficient comes out
    // at `span` and stays there.
    auto record = [&](const MuxClauses & clauses, int which) -> ProofLine {
        PolBuilder pol;
        for (auto t = 0; t < _width; ++t)
            pol.add(clauses[t][which], Integer{1LL << t});
        return pol.emit(_logger, _level);
    };

    // Braced initialisation is sequenced left to right, so naming every member
    // here also fixes the order the record rows come out in.
    Comparator c{.selector = selector,
        .a = a,
        .b = b,
        .d_a = d_a,
        .d_b = d_b,
        .lo = lo,
        .hi = hi,
        .d_lo = d_lo,
        .d_hi = d_hi,
        .forward = forward,
        .reverse = reverse,
        .lo_ge_a = record(lo_clauses, 0),
        .lo_le_a = record(lo_clauses, 2),
        .lo_ge_b = record(lo_clauses, 1),
        .lo_le_b = record(lo_clauses, 3),
        .hi_ge_b = record(hi_clauses, 0),
        .hi_le_b = record(hi_clauses, 2),
        .hi_ge_a = record(hi_clauses, 1),
        .hi_le_a = record(hi_clauses, 3),
        .d_lo_ge_a = record(d_lo_clauses, 0),
        .d_lo_le_a = record(d_lo_clauses, 2),
        .d_lo_ge_b = record(d_lo_clauses, 1),
        .d_lo_le_b = record(d_lo_clauses, 3),
        .d_hi_ge_b = record(d_hi_clauses, 0),
        .d_hi_le_b = record(d_hi_clauses, 2),
        .d_hi_ge_a = record(d_hi_clauses, 1),
        .d_hi_le_a = record(d_hi_clauses, 3)};

    _duration.emplace(lo.id, d_lo);
    _duration.emplace(hi.id, d_hi);

    return c;
}

auto ComparatorNetwork::case_split(const WPBSumLE & goal, const vector<ProofLine> & guarded_halves) -> ProofLine
{
    // The goal holds under each polarity of a selector, so it holds. Each half
    // is the goal plus a guard: adding the negated goal cancels every record
    // term and leaves the guard alone, and the two guards then sum past one.
    map<ProofGoal, Subproof> subproofs;
    subproofs.emplace("#1", Subproof{[&](ProofLogger & sub_logger) {
        // The negated goal is the last line added when the subproof opens.
        auto negation = sub_logger.get_current_proof_line();
        vector<ProofLine> guards;
        for (const auto & half : guarded_halves) {
            PolBuilder builder;
            builder.add(half).add(negation).divide_by(_div);
            guards.push_back(builder.emit(sub_logger, ProofLevel::Temporary));
        }
        PolBuilder builder;
        for (const auto & guard : guards)
            builder.add(guard);
        builder.emit(sub_logger, ProofLevel::Temporary);
    }});

    return _logger.emit_red_proof_line(goal, {}, _level, subproofs);
}

auto ComparatorNetwork::derive_positivity(const ProofWire & out, const vector<pair<ProofLine, ProofWire>> & halves) -> void
{
    // `d_out >= 1`, carried through the mux, and needed by the *next*
    // comparator's gap lemma, which is where the degree has to come from. Each
    // guarded `d_out >= d_in` row is paired with THAT input's positivity:
    // pairing them the other way round leaves the two durations in the sum
    // instead of cancelling, which still derives something, just not the goal.
    vector<ProofLine> rows;
    for (const auto & [record, source] : halves) {
        PolBuilder builder;
        builder.add(record).add(_positivity.at(source.id));
        rows.push_back(builder.emit(_logger, _level));
    }

    auto goal = terms(out, 1_i) >= 1_i;
    _positivity.emplace(out.id,
        holds_alternative<comparator_network_mutation::RupPositivity>(_mutation) ? _logger.emit_rup_proof_line(goal, _level)
                                                                                 : case_split(goal, rows));
}

auto ComparatorNetwork::derive_preservation(const Comparator & c) -> ProofLine
{
    // `d_lo + d_hi - d_a - d_b >= 0`. New at unequal durations: the endgame
    // sums the sorted wires' durations and needs that sum to be at least the
    // instance's total work, which is only true because each comparator
    // permutes rather than loses.
    PolBuilder selected;
    selected.add(c.d_lo_ge_a).add(c.d_hi_ge_b);
    PolBuilder not_selected;
    not_selected.add(c.d_lo_ge_b).add(c.d_hi_ge_a);

    WPBSum goal;
    add_terms(goal, c.d_lo, 1_i);
    add_terms(goal, c.d_hi, 1_i);
    add_terms(goal, c.d_a, -1_i);
    add_terms(goal, c.d_b, -1_i);

    if (holds_alternative<comparator_network_mutation::RupPreservation>(_mutation))
        return _logger.emit_rup_proof_line(move(goal) >= 0_i, _level);
    return case_split(move(goal) >= 0_i, {selected.emit(_logger, _level), not_selected.emit(_logger, _level)});
}

auto ComparatorNetwork::derive_gap(const Comparator & c) -> ProofLine
{
    // `hi - lo - d_lo >= 0`: the gap between the two outputs is the earlier
    // task's duration, which is now a muxed record rather than a constant.
    const auto & separation = separation_between(c.a, c.b);
    auto a_first = separation.first.at(c.a.id), b_first = separation.first.at(c.b.id);

    // One half per polarity of the selector. Under the guard one of the two
    // inputs starts strictly later, so the separation cannot be resolved that
    // way round: `later_first` is the row this refutes, `earlier_first` the one
    // left standing, and the gap then reads off the outputs' record rows.
    auto half = [&](ProofLine later_first, ProofLine earlier_first, ProofLine guard_row, const ProofWire & later_duration, ProofLine hi_ge,
                    ProofLine lo_le, ProofLine d_lo_le) -> ProofLine {
        // Starting later is only a reason not to finish first if the later
        // task's duration is positive --- which has to be said, the duration no
        // longer being a constant in the degree.
        auto running = later_first;
        if (! holds_alternative<comparator_network_mutation::DropPositivity>(_mutation)) {
            PolBuilder builder;
            builder.add(later_first).add(_positivity.at(later_duration.id));
            running = builder.emit(_logger, _level);
        }
        {
            PolBuilder builder;
            builder.add(running).add(guard_row).divide_by(_big);
            running = builder.emit(_logger, _level);
        }
        {
            PolBuilder builder;
            builder.add(running).add(separation.clause);
            running = builder.emit(_logger, _level);
        }
        {
            PolBuilder builder;
            builder.add(running).multiply_by(_big).add(earlier_first);
            running = builder.emit(_logger, _level);
        }
        PolBuilder builder;
        builder.add(running).add(hi_ge).add(lo_le).add(d_lo_le);
        return builder.emit(_logger, _level);
    };

    auto swapped = holds_alternative<comparator_network_mutation::SwapDurations>(_mutation);
    auto when_a_is_later = half(a_first, b_first, c.reverse, c.d_a, c.hi_ge_a, c.lo_le_b, swapped ? c.d_lo_le_a : c.d_lo_le_b);
    auto when_b_is_later = half(b_first, a_first, c.forward, c.d_b, c.hi_ge_b, c.lo_le_a, swapped ? c.d_lo_le_b : c.d_lo_le_a);

    WPBSum goal;
    add_terms(goal, c.hi, 1_i);
    add_terms(goal, c.lo, -1_i);
    add_terms(goal, c.d_lo, -1_i);

    if (holds_alternative<comparator_network_mutation::RupGap>(_mutation))
        return _logger.emit_rup_proof_line(move(goal) >= 0_i, _level);
    return case_split(move(goal) >= 0_i, {when_a_is_later, when_b_is_later});
}

auto ComparatorNetwork::derive_dominance(const Comparator & c) -> ProofLine
{
    // `hi >= a`: the running maximum never decreases.
    PolBuilder selected;
    selected.add(c.hi_ge_b).add(c.forward);

    WPBSum goal;
    add_terms(goal, c.hi, 1_i);
    add_terms(goal, c.a, -1_i);
    return case_split(move(goal) >= 0_i, {selected.emit(_logger, _level), c.hi_ge_a});
}

auto ComparatorNetwork::derive_bound(const Comparator & c, const ProofWire & out, const ProofWire & d_out, ProofLine le_a, ProofLine le_b,
    ProofLine d_le_a, ProofLine d_le_b) -> ProofLine
{
    // `horizon - out - d_out >= 0`, carried through the mux from the inputs'.
    //
    // Derived for BOTH outputs. Aliasing the low output's bound to the high
    // one's --- on the grounds that lo <= hi --- would be a statement about the
    // wrong wire: `horizon - hi - d_hi >= 0` is not `horizon - lo - d_lo >= 0`,
    // and a later comparator consuming it as an input bound adds a row
    // mentioning a wire that is no longer in play, so nothing cancels.
    PolBuilder from_a;
    from_a.add(_upper.at(c.a.id)).add(le_a).add(d_le_a);
    PolBuilder from_b;
    from_b.add(_upper.at(c.b.id)).add(le_b).add(d_le_b);

    WPBSum goal;
    add_terms(goal, out, -1_i);
    add_terms(goal, d_out, -1_i);
    for (const auto & term : _guard.terms)
        goal += term;
    return case_split(move(goal) >= -_window_hi, {from_a.emit(_logger, _level), from_b.emit(_logger, _level)});
}

auto ComparatorNetwork::derive_lower_bound(const Comparator & c, const ProofWire & out, ProofLine ge_a, ProofLine ge_b) -> ProofLine
{
    // `out - window_lo >= 0`, carried through the mux from the inputs'. Free at
    // a window starting from zero, where a bit vector cannot be negative in the
    // first place --- but the endgame telescopes down to the earliest task's
    // start, and over a real window what makes that a refutation is that the
    // earliest start is not earlier than the window it was selected for.
    PolBuilder from_a;
    from_a.add(_lower.at(c.a.id)).add(ge_a);
    PolBuilder from_b;
    from_b.add(_lower.at(c.b.id)).add(ge_b);

    auto goal = terms(out, 1_i);
    for (const auto & term : _guard.terms)
        goal += term;
    return case_split(move(goal) >= _window_lo, {from_a.emit(_logger, _level), from_b.emit(_logger, _level)});
}

auto ComparatorNetwork::reify_separation(const ProofWire & x, const ProofWire & y, const string & stem) -> SeparationFlags
{
    auto name = next_name(stem);
    SeparationFlags flags{.x_first = _logger.create_proof_flag(name + "f"),
        .y_first = _logger.create_proof_flag(name + "b"),
        .x_first_row = {},
        .x_first_reverse = {},
        .y_first_row = {},
        .y_first_reverse = {}};

    auto reify = [&](const ProofWire & first, const ProofWire & second, ProofFlag flag) -> pair<ProofLine, ProofLine> {
        const auto & duration = _duration.at(first.id);

        WPBSum forward;
        add_terms(forward, second, 1_i);
        add_terms(forward, first, -1_i);
        add_terms(forward, duration, -1_i);
        forward += _big * ! flag;
        auto forward_line = _logger.emit_red_proof_line(move(forward) >= 0_i, {{flag, ProofLiteralOrFlag{FalseLiteral{}}}}, _level);

        WPBSum reverse;
        add_terms(reverse, first, 1_i);
        add_terms(reverse, second, -1_i);
        add_terms(reverse, duration, 1_i);
        reverse += _big * flag;
        auto reverse_line = _logger.emit_red_proof_line(move(reverse) >= 1_i, {{flag, ProofLiteralOrFlag{TrueLiteral{}}}}, _level);

        return {forward_line, reverse_line};
    };

    std::tie(flags.x_first_row, flags.x_first_reverse) = reify(x, y, flags.x_first);
    std::tie(flags.y_first_row, flags.y_first_reverse) = reify(y, x, flags.y_first);
    return flags;
}

auto ComparatorNetwork::separate_from_gap(const ProofWire & x, const ProofWire & y, ProofLine gap) -> void
{
    // Register a separation between two wires the network has just *proved* are
    // apart, rather than one the model gave it. The reverse half of "x runs
    // first" contradicts the gap outright, so what comes out is the *unit*
    // `x runs first` --- strictly stronger than the two-literal clause a model
    // pair gives.
    //
    // Weaken it straight back, by adding the literal axiom for the other
    // direction. A transfer lemma cancels a separation's clause against one
    // guard from each of its two halves, which lands on a contradiction only
    // when the clause has both literals: handed the unit it lands one literal
    // short, sound but not closing, and the subproof then needs a
    // database-wide RUP to finish. That is a real cost --- transfers are the
    // cubic term here --- for a row that is only stronger than needed.
    auto flags = reify_separation(x, y, "gap");
    PolBuilder builder;
    builder.add(flags.x_first_reverse)
        .add(gap)
        .divide_by(_big)
        .add(_logger.names_and_ids_tracker().xliteral_for(flags.y_first), _logger.names_and_ids_tracker());
    record_separation(x, flags.x_first_row, y, flags.y_first_row, builder.emit(_logger, _level));
}

auto ComparatorNetwork::transfer(const ProofWire & out, const ProofWire & other, const Comparator & c, ProofLine le_a, ProofLine ge_a, ProofLine le_b,
    ProofLine ge_b, ProofLine d_le_a, ProofLine d_le_b) -> void
{
    // A separation between one of the comparator's outputs and a wire not in
    // the comparator, from the separations its two *inputs* had with that wire,
    // by cases on the selector. The duration record rows are what unequal
    // durations add: without them `d_out` cannot be turned into `d_a` inside a
    // case.
    struct Branch
    {
        ProofLine le, ge, d_le;
        const Separation * separation;
        const ProofWire * input;
    };

    const auto & from_a = separation_between(c.a, other);
    const auto & from_b = separation_between(c.b, other);
    const Branch branches[]{{le_a, ge_a, d_le_a, &from_a, &c.a}, {le_b, ge_b, d_le_b, &from_b, &c.b}};

    auto flags = reify_separation(out, other, "t");

    WPBSum goal;
    goal += 1_i * flags.x_first;
    goal += 1_i * flags.y_first;

    map<ProofGoal, Subproof> subproofs;
    subproofs.emplace("#1", Subproof{[&](ProofLogger & sub_logger) {
        // Under the negated goal neither flag holds, so both reverse halves
        // fire: the output is not before the other wire, and the other wire is
        // not before the output.
        auto no_x = sub_logger.emit_rup_proof_line(WPBSum{} + 1_i * ! flags.x_first >= 1_i, ProofLevel::Temporary);
        auto no_y = sub_logger.emit_rup_proof_line(WPBSum{} + 1_i * ! flags.y_first >= 1_i, ProofLevel::Temporary);

        PolBuilder out_late_builder;
        out_late_builder.add(flags.x_first_reverse).add(no_x, _big);
        auto out_late = out_late_builder.emit(sub_logger, ProofLevel::Temporary);

        PolBuilder other_late_builder;
        other_late_builder.add(flags.y_first_reverse).add(no_y, _big);
        auto other_late = other_late_builder.emit(sub_logger, ProofLevel::Temporary);

        vector<ProofLine> kills;
        for (const auto & branch : branches) {
            // Rewrite both halves onto this input, then cancel each against the
            // input's own separation row, leaving the selector's polarity and
            // the separation's guard. The clause then removes the guard.
            PolBuilder as_input;
            as_input.add(out_late).add(branch.le).add(branch.d_le);
            auto forwards = as_input.emit(sub_logger, ProofLevel::Temporary);

            PolBuilder as_input_reverse;
            as_input_reverse.add(other_late).add(branch.ge);
            auto backwards = as_input_reverse.emit(sub_logger, ProofLevel::Temporary);

            PolBuilder cancel_forwards;
            cancel_forwards.add(forwards).add(branch.separation->first.at(branch.input->id)).divide_by(_big);
            forwards = cancel_forwards.emit(sub_logger, ProofLevel::Temporary);

            PolBuilder cancel_backwards;
            cancel_backwards.add(backwards).add(branch.separation->first.at(other.id)).divide_by(_big);
            backwards = cancel_backwards.emit(sub_logger, ProofLevel::Temporary);

            PolBuilder kill;
            kill.add(forwards).add(backwards).add(branch.separation->clause).divide_by(2_i);
            kills.push_back(kill.emit(sub_logger, ProofLevel::Temporary));
        }

        PolBuilder both;
        both.add(kills[0]).add(kills[1]);
        both.emit(sub_logger, ProofLevel::Temporary);
    }});

    auto clause = _logger.emit_red_proof_line(move(goal) >= 1_i, {}, _level, subproofs);
    record_separation(out, flags.x_first_row, other, flags.y_first_row, clause);
}

auto ComparatorNetwork::sort(const vector<ProofWire> & tasks) -> SortedTasks
{
    // Selection sort: each pass runs a maximum along the live wires, leaving
    // the smaller output of each comparator behind for the next pass. A
    // comparison network of a smarter shape would emit fewer comparators, but
    // this one has the property the endgame needs --- every pass ends holding a
    // gap row from its own maximum to each of its leftovers --- and the cost is
    // dominated by the transfers either way.
    if (tasks.size() < 2)
        throw ProofError{"a comparator network needs at least two tasks to sort"};

    SortedTasks result{.chain = {}, .preserved = {}, .top_upper_bound = {}, .bottom_lower_bound = {}};

    auto live = tasks;
    optional<ProofWire> previous_maximum, first_maximum;
    map<int, ProofLine> previous_gaps;

    while (live.size() > 1) {
        auto running = live[0];
        vector<ProofWire> leftovers;
        map<int, ProofLine> gaps;
        optional<ProofLine> carried;
        if (previous_maximum)
            carried = previous_gaps.at(running.id);

        for (size_t j = 1; j < live.size(); ++j) {
            auto c = compare(running, live[j], "c");
            derive_positivity(c.d_lo, {{c.d_lo_ge_a, c.d_a}, {c.d_lo_ge_b, c.d_b}});
            derive_positivity(c.d_hi, {{c.d_hi_ge_b, c.d_b}, {c.d_hi_ge_a, c.d_a}});
            result.preserved.push_back(derive_preservation(c));
            auto gap = derive_gap(c);

            // Every wire the outputs will still be compared against needs a
            // separation with them: the ones not yet reached in this pass, and
            // the ones this pass has already put aside.
            auto still_to_come = vector<ProofWire>{live.begin() + j + 1, live.end()};
            still_to_come.insert(still_to_come.end(), leftovers.begin(), leftovers.end());
            for (const auto & other : still_to_come) {
                transfer(c.lo, other, c, c.lo_le_a, c.lo_ge_a, c.lo_le_b, c.lo_ge_b, c.d_lo_le_a, c.d_lo_le_b);
                transfer(c.hi, other, c, c.hi_le_a, c.hi_ge_a, c.hi_le_b, c.hi_ge_b, c.d_hi_le_a, c.d_hi_le_b);
            }
            separate_from_gap(c.lo, c.hi, gap);

            // The gap rows this pass is accumulating are all against the
            // running maximum, so when the maximum moves they all move with it.
            if (j > 1) {
                auto dominance = derive_dominance(c);
                for (auto & [wire, row] : gaps) {
                    PolBuilder builder;
                    builder.add(row).add(dominance);
                    row = builder.emit(_logger, _level);
                }
            }
            gaps.emplace(c.lo.id, gap);

            // And the previous pass's maximum has to keep up with this pass's,
            // which is the link between one pass and the next.
            if (previous_maximum) {
                PolBuilder selected;
                selected.add(previous_gaps.at(live[j].id)).add(c.hi_le_b).add(c.d_hi_le_b);
                PolBuilder not_selected;
                not_selected.add(*carried).add(c.hi_le_a).add(c.d_hi_le_a);

                WPBSum goal;
                add_terms(goal, *previous_maximum, 1_i);
                add_terms(goal, c.hi, -1_i);
                add_terms(goal, c.d_hi, -1_i);
                carried = case_split(move(goal) >= 0_i, {selected.emit(_logger, _level), not_selected.emit(_logger, _level)});
            }

            // `hi` takes `b` under the selector and `lo` takes `a`, so each
            // output pairs its selector-guarded record row with THAT input's
            // bound.
            _upper.insert_or_assign(c.hi.id, derive_bound(c, c.hi, c.d_hi, c.hi_le_a, c.hi_le_b, c.d_hi_le_a, c.d_hi_le_b));
            _upper.insert_or_assign(c.lo.id, derive_bound(c, c.lo, c.d_lo, c.lo_le_a, c.lo_le_b, c.d_lo_le_a, c.d_lo_le_b));
            _lower.insert_or_assign(c.hi.id, derive_lower_bound(c, c.hi, c.hi_ge_a, c.hi_ge_b));
            _lower.insert_or_assign(c.lo.id, derive_lower_bound(c, c.lo, c.lo_ge_a, c.lo_ge_b));

            leftovers.push_back(c.lo);
            running = c.hi;
        }

        if (previous_maximum)
            result.chain.push_back(*carried);
        else
            first_maximum = running;

        previous_maximum = running;
        previous_gaps = gaps;
        live = leftovers;
    }

    result.chain.push_back(previous_gaps.at(live[0].id));
    result.top_upper_bound = _upper.at(first_maximum->id);
    result.bottom_lower_bound = _lower.at(live[0].id);
    return result;
}

auto ComparatorNetwork::sum_up(const SortedTasks & sorted) -> ProofLine
{
    // Telescope: each chain row is one adjacent gap, so summing them leaves the
    // largest start minus the smallest, minus every duration but the largest's.
    // The largest's upper bound and the smallest's lower bound then replace the
    // two ends by the window they were selected for, and the preservation rows
    // turn the sorted durations back into the instance's own. What is left says
    // the window is as wide as the work inside it.
    PolBuilder builder;
    for (const auto & row : sorted.chain)
        builder.add(row);
    builder.add(sorted.top_upper_bound);
    builder.add(sorted.bottom_lower_bound);
    if (! holds_alternative<comparator_network_mutation::DropPreservation>(_mutation))
        for (const auto & row : sorted.preserved)
            builder.add(row);
    return builder.emit(_logger, _level);
}
