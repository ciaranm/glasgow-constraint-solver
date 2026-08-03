#include <gcs/exception.hh>
#include <gcs/innards/proofs/emit_inequality_to.hh>
#include <gcs/innards/proofs/names_and_ids_tracker.hh>
#include <gcs/innards/proofs/pol_builder.hh>
#include <gcs/innards/proofs/proof_logger.hh>

#include <util/overloaded.hh>

using std::nullopt;
using std::optional;
using std::string;
using std::vector;
using std::visit;
using std::ranges::contains;

using namespace gcs;
using namespace gcs::innards;

PolBuilder::PolBuilder() = default;

PolBuilder::~PolBuilder() = default;

PolBuilder::PolBuilder(PolBuilder &&) noexcept = default;

auto PolBuilder::operator=(PolBuilder &&) noexcept -> PolBuilder & = default;

auto PolBuilder::enable_deview_mode(const NamesAndIDsTracker & tracker) -> PolBuilder &
{
    _deview_tracker = &tracker;
    return *this;
}

auto PolBuilder::separator_if_not_first() -> void
{
    if (! _empty)
        _text += " +";
}

auto PolBuilder::add(ProofLine line) -> PolBuilder &
{
    ProofLine resolved = _deview_tracker ? _deview_tracker->deviewed_line_for(line) : line;
    _text += ' ';
    _refs.emplace_back(_text.size(), move(resolved));
    separator_if_not_first();
    _empty = false;
    return *this;
}

auto PolBuilder::add(ProofLine line, Integer coeff) -> PolBuilder &
{
    if (coeff == 0_i)
        throw UnexpectedException{"PolBuilder::add called with zero coefficient"};
    ProofLine resolved = _deview_tracker ? _deview_tracker->deviewed_line_for(line) : line;
    _text += ' ';
    _refs.emplace_back(_text.size(), move(resolved));
    if (coeff != 1_i) {
        _text += ' ';
        append_number_to(_text, coeff);
        _text += " *";
    }
    separator_if_not_first();
    _empty = false;
    return *this;
}

auto PolBuilder::add(const XLiteral & lit, const NamesAndIDsTracker & tracker) -> PolBuilder &
{
    _text += ' ';
    _text += tracker.pb_file_string_for(lit);
    separator_if_not_first();
    _empty = false;
    return *this;
}

auto PolBuilder::add(const XLiteral & lit, Integer coeff, const NamesAndIDsTracker & tracker) -> PolBuilder &
{
    if (coeff == 0_i)
        throw UnexpectedException{"PolBuilder::add called with zero coefficient"};
    _text += ' ';
    _text += tracker.pb_file_string_for(lit);
    if (coeff != 1_i) {
        _text += ' ';
        append_number_to(_text, coeff);
        _text += " *";
    }
    separator_if_not_first();
    _empty = false;
    return *this;
}

auto PolBuilder::note_literal_pushed(const IntegerVariableCondition & lit) -> void
{
    // The other way an atom enters a pol: pushed as a literal rather than reached through
    // an operand's names. `add(XLiteral)` cannot be caught here -- an XLiteral is already a
    // proof name with no condition to read back -- but every atom a caller means to push
    // arrives through add_for_literal, which still has the condition.
    const auto * sid = std::get_if<SimpleIntegerVariableID>(&lit.var);
    if (! sid)
        return;

    optional<EqualsOrGreaterEqual> kind;
    switch (lit.op) {
        using enum VariableConditionOperator;
    case Equal:
    case NotEqual: kind = EqualsOrGreaterEqual::Equals; break;
    // ge(v) is named by `X >= v` and by `X < v` (its negation); `X <= v` / `X > v` are
    // lowered to Less(v+1) / GreaterEqual(v+1), so the threshold is the value either way.
    case GreaterEqual:
    case Less: kind = EqualsOrGreaterEqual::GreaterEqual; break;
    default: break;
    }
    if (! kind)
        return;

    NamedAtom atom{*sid, lit.value, *kind};
    if (! contains(_named_atoms, atom))
        _named_atoms.push_back(atom);
}

auto PolBuilder::add_for_literal(NamesAndIDsTracker & tracker, const IntegerVariableCondition & lit) -> PolBuilder &
{
    note_literal_pushed(lit);
    visit(overloaded{
              [&](const ProofLine & l) { add(l); },        //
              [&](const XLiteral & x) { add(x, tracker); } //
          },
        tracker.need_pol_item_defining_literal(lit));
    return *this;
}

auto PolBuilder::add_for_literal(NamesAndIDsTracker & tracker, const IntegerVariableCondition & lit, Integer coeff) -> PolBuilder &
{
    note_literal_pushed(lit);
    visit(overloaded{
              [&](const ProofLine & l) { add(l, coeff); },        //
              [&](const XLiteral & x) { add(x, coeff, tracker); } //
          },
        tracker.need_pol_item_defining_literal(lit));
    return *this;
}

auto PolBuilder::saturate() -> PolBuilder &
{
    _text += " s";
    return *this;
}

auto PolBuilder::multiply_by(Integer n) -> PolBuilder &
{
    _text += ' ';
    append_number_to(_text, n);
    _text += " *";
    return *this;
}

auto PolBuilder::divide_by(Integer n) -> PolBuilder &
{
    _text += ' ';
    append_number_to(_text, n);
    _text += " d";
    return *this;
}

auto PolBuilder::weaken(const ProofFlag & flag, const NamesAndIDsTracker & tracker) -> PolBuilder &
{
    _text += ' ';
    _text += tracker.pb_file_string_for(flag);
    _text += " w";
    return *this;
}

auto PolBuilder::empty() const -> bool
{
    return _empty;
}

auto PolBuilder::render(optional<long long> current_max) const -> string
{
    string out = "pol";
    std::size_t done = 0;
    for (const auto & [offset, line] : _refs) {
        out.append(_text, done, offset - done);
        done = offset;
        if (current_max)
            out += relative_proof_line(line, *current_max);
        else if (const auto * n = std::get_if<ProofLineNumber>(&line))
            append_number_to(out, n->number);
        else {
            out += '@';
            out += std::get<ProofLineLabel>(line).label;
        }
    }
    out.append(_text, done, string::npos);
    return out + " ;";
}

auto PolBuilder::str() const -> string
{
    return render(std::nullopt);
}

auto PolBuilder::emit(ProofLogger & logger, ProofLevel level) -> ProofLine
{
    // What does the constraint this pol derives actually name? The text cannot say: it is
    // reverse-polish over *references*, and the result's literals fall out of the
    // arithmetic. gcs never evaluates that arithmetic, so before this the answer was
    // "nobody knows", and a Top pol over operands naming a windowed eq atom was an
    // invisible permanent reference to it -- which is why
    // `magic_square --size=4 --all-different gac` rejected under the window, at the
    // all-different Hall-set at-most-one row.
    //
    // It does not need evaluating. Cutting planes cannot invent an atom: addition,
    // multiplication, division and saturation all yield a constraint over a subset of the
    // operands' variables. So the union over the operands' recorded names, plus whatever
    // was pushed as a literal rather than a reference, over-approximates the result --
    // soundly, automatically, and with nothing for a caller to declare or forget.
    //
    // Over-approximating costs only a pin that was not strictly required; under-approximating
    // costs a rejected proof, so erring this way is the whole point.
    //
    // Gated on bound_advances_active() rather than eq_window_active(): ge definitions are
    // deletable under Literals whether or not the eq window was asked for, so gating the ge
    // half on the window would miss every reference in the shipped configuration.
    NamedAtoms named;
    if (logger.bound_advances_active()) {
        const auto & tracker = logger.names_and_ids_tracker();
        auto note = [&](const NamedAtom & atom) {
            if (! contains(named, atom))
                named.push_back(atom);
        };
        for (const auto & [offset, line] : _refs)
            if (const auto * from_operand = tracker.atoms_named_by(line))
                for (const auto & atom : *from_operand)
                    note(atom);
        for (const auto & atom : _named_atoms)
            note(atom);

        // A pol landing at Top is a permanent reference to everything it names, so pin
        // before the line is written -- hoisting emits lines of its own, and they have to
        // precede the citing line. Rendering must therefore happen after this, or the
        // relative operand offsets would be computed against a stale line counter.
        if (level == ProofLevel::Top) {
            // ge references go through the existing hoist path: it owns the Top-pin counting
            // that evict_order_literal's precondition reads, and hoisting is the action a
            // permanent reference requires. One call, so all its emissions stay together.
            vector<Literal> ge_references;
            for (const auto & atom : named) {
                if (atom.kind == EqualsOrGreaterEqual::Equals)
                    logger.names_and_ids_tracker().note_permanent_eq_reference(atom.id, atom.value);
                else
                    ge_references.push_back(Literal{atom.id >= atom.value});
            }
            if (! ge_references.empty())
                logger.names_and_ids_tracker().hoist_live_order_literals_toward_level(ge_references, 0, OrderEncodingResidencyCause::LineHoist);
        }
    }

    auto result = logger.emit_proof_line(render(logger.get_current_proof_line().number), level, nullopt, named);
    clear();
    return result;
}

auto PolBuilder::clear() -> void
{
    _text.clear();
    _refs.clear();
    _named_atoms.clear();
    _empty = true;
}
