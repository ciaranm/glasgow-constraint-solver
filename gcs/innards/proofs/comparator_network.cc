#include <gcs/innards/proofs/comparator_network.hh>
#include <gcs/innards/proofs/names_and_ids_tracker.hh>
#include <gcs/innards/proofs/pol_builder.hh>

#include <string>

using namespace gcs;
using namespace gcs::innards;

using std::move;
using std::string;
using std::to_string;
using std::vector;

ComparatorNetwork::ComparatorNetwork(ProofLogger & logger, int width, ProofLevel level) :
    _logger(logger), _width(width), _level(level), _span((Integer{1LL << width}) - 1_i),
    // Twice a wire's span, so that a transfer lemma --- which adds two record
    // rows and divides by a separation row's guard coefficient --- comes out at
    // exactly one. Larger would still be sound and would make that division
    // land short.
    _big(2_i * ((Integer{1LL << width}) - 1_i))
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
    ProofWire wire;
    auto name = next_name(stem);
    for (auto t = 0; t < _width; ++t)
        wire.bits.push_back(_logger.create_proof_flag(name + "b" + to_string(t)));
    return wire;
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
        sum += (sign * Integer{1LL << t}) * wire.bits[t];
}

auto ComparatorNetwork::pin(const ProofWire & wire, Integer value) -> void
{
    for (auto t = 0; t < _width; ++t) {
        auto on = 0 != ((value.raw_value >> t) & 1);
        WPBSum sum;
        if (on)
            sum += 1_i * wire.bits[t];
        else
            sum += 1_i * ! wire.bits[t];
        _logger.emit_red_proof_line(
            move(sum) >= 1_i, {{wire.bits[t], on ? ProofLiteralOrFlag{TrueLiteral{}} : ProofLiteralOrFlag{FalseLiteral{}}}}, _level);
    }
}

auto ComparatorNetwork::compare(const ProofWire & a, const ProofWire & b, const string & stem) -> Comparator
{
    auto selector = _logger.create_proof_flag(next_name(stem) + "sel");
    auto lo = fresh_wire(stem + "lo"), hi = fresh_wire(stem + "hi");

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
    // witness makes both proofgoals autoprove.
    struct Mux
    {
        const ProofWire &out, &on_true, &on_false;
    };
    const Mux muxes[]{{lo, a, b}, {hi, b, a}};

    // Per output, the four record rows: multiply the bit-`t` mux clause by
    // `2^t` and sum, which turns a family of clauses about bits into one
    // inequality about the wires they encode. The guard coefficient comes out
    // at `span` and stays there.
    auto record = [&](const Mux & m, int which) -> ProofLine {
        PolBuilder pol;
        for (auto t = 0; t < _width; ++t) {
            const auto &out = m.out.bits[t], &on_t = m.on_true.bits[t], &on_f = m.on_false.bits[t];
            WPBSum clause;
            switch (which) {
            case 0: clause += 1_i * ! selector, clause += 1_i * ! on_t, clause += 1_i * out; break;
            case 1: clause += 1_i * selector, clause += 1_i * ! on_f, clause += 1_i * out; break;
            case 2: clause += 1_i * ! selector, clause += 1_i * on_t, clause += 1_i * ! out; break;
            default: clause += 1_i * selector, clause += 1_i * on_f, clause += 1_i * ! out; break;
            }
            auto witness = (which < 2) ? ProofLiteralOrFlag{TrueLiteral{}} : ProofLiteralOrFlag{FalseLiteral{}};
            pol.add(_logger.emit_red_proof_line(move(clause) >= 1_i, {{out, witness}}, _level), Integer{1LL << t});
        }
        return pol.emit(_logger, _level);
    };

    auto lo_ge_a = record(muxes[0], 0);
    auto lo_ge_b = record(muxes[0], 1);
    auto lo_le_a = record(muxes[0], 2);
    auto lo_le_b = record(muxes[0], 3);
    auto hi_ge_b = record(muxes[1], 0);
    auto hi_ge_a = record(muxes[1], 1);
    auto hi_le_b = record(muxes[1], 2);
    auto hi_le_a = record(muxes[1], 3);

    // Built in one go with every member named, rather than default-constructed
    // and filled in: a designated initialiser that leaves members out is a
    // -Wmissing-field-initializers error on the one CI lane that builds with
    // -Werror. The rows are emitted above rather than inline here so that the
    // order they come out in stays the order they are derived in, which
    // declaration order would otherwise decide.
    return Comparator{.selector = selector,
        .lo = lo,
        .hi = hi,
        .forward = forward,
        .reverse = reverse,
        .lo_ge_a = lo_ge_a,
        .lo_le_a = lo_le_a,
        .lo_ge_b = lo_ge_b,
        .lo_le_b = lo_le_b,
        .hi_ge_b = hi_ge_b,
        .hi_le_b = hi_le_b,
        .hi_ge_a = hi_ge_a,
        .hi_le_a = hi_le_a};
}
