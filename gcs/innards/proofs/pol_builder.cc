#include <gcs/exception.hh>
#include <gcs/innards/proofs/emit_inequality_to.hh>
#include <gcs/innards/proofs/names_and_ids_tracker.hh>
#include <gcs/innards/proofs/pol_builder.hh>
#include <gcs/innards/proofs/proof_logger.hh>

#include <util/overloaded.hh>

using std::optional;
using std::string;
using std::visit;

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

auto PolBuilder::add_for_literal(NamesAndIDsTracker & tracker, const IntegerVariableCondition & lit) -> PolBuilder &
{
    visit(overloaded{
              [&](const ProofLine & l) { add(l); },        //
              [&](const XLiteral & x) { add(x, tracker); } //
          },
        tracker.need_pol_item_defining_literal(lit));
    return *this;
}

auto PolBuilder::add_for_literal(NamesAndIDsTracker & tracker, const IntegerVariableCondition & lit, Integer coeff) -> PolBuilder &
{
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
    auto result = logger.emit_proof_line(render(logger.get_current_proof_line().number), level);
    clear();
    return result;
}

auto PolBuilder::clear() -> void
{
    _text.clear();
    _refs.clear();
    _empty = true;
}
