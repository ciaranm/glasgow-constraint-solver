#include <gcs/exception.hh>
#include <gcs/innards/proofs/names_and_ids_tracker.hh>
#include <gcs/innards/proofs/pol_builder.hh>
#include <gcs/innards/proofs/proof_logger.hh>

#include <util/overloaded.hh>

using std::move;
using std::string;
using std::stringstream;
using std::variant;
using std::visit;

using namespace gcs;
using namespace gcs::innards;

PolBuilder::PolBuilder() :
    _empty(true)
{
    _s << "pol";
}

PolBuilder::~PolBuilder() = default;

PolBuilder::PolBuilder(PolBuilder &&) noexcept = default;

auto PolBuilder::operator=(PolBuilder &&) noexcept -> PolBuilder & = default;

auto PolBuilder::separator_if_not_first() -> void
{
    if (! _empty)
        _s << " +";
}

auto PolBuilder::add(ProofLine line) -> PolBuilder &
{
    _s << " " << line;
    separator_if_not_first();
    _empty = false;
    return *this;
}

auto PolBuilder::add(ProofLine line, Integer coeff) -> PolBuilder &
{
    if (coeff == 0_i)
        throw UnexpectedException{"PolBuilder::add called with zero coefficient"};
    _s << " " << line;
    if (coeff != 1_i)
        _s << " " << coeff.raw_value << " *";
    separator_if_not_first();
    _empty = false;
    return *this;
}

auto PolBuilder::add(const XLiteral & lit, const NamesAndIDsTracker & tracker) -> PolBuilder &
{
    _s << " " << tracker.pb_file_string_for(lit);
    separator_if_not_first();
    _empty = false;
    return *this;
}

auto PolBuilder::add(const XLiteral & lit, Integer coeff, const NamesAndIDsTracker & tracker) -> PolBuilder &
{
    if (coeff == 0_i)
        throw UnexpectedException{"PolBuilder::add called with zero coefficient"};
    _s << " " << tracker.pb_file_string_for(lit);
    if (coeff != 1_i)
        _s << " " << coeff.raw_value << " *";
    separator_if_not_first();
    _empty = false;
    return *this;
}

auto PolBuilder::add_for_literal(NamesAndIDsTracker & tracker, const IntegerVariableCondition & lit) -> PolBuilder &
{
    visit(overloaded{
              [&](const ProofLine & l) { add(l); },
              [&](const XLiteral & x) { add(x, tracker); }},
        tracker.need_pol_item_defining_literal(lit));
    return *this;
}

auto PolBuilder::add_for_literal(NamesAndIDsTracker & tracker, const IntegerVariableCondition & lit, Integer coeff) -> PolBuilder &
{
    visit(overloaded{
              [&](const ProofLine & l) { add(l, coeff); },
              [&](const XLiteral & x) { add(x, coeff, tracker); }},
        tracker.need_pol_item_defining_literal(lit));
    return *this;
}

auto PolBuilder::add_and_saturate(ProofLine line) -> PolBuilder &
{
    bool was_empty = _empty;
    add(line);
    if (! was_empty)
        saturate();
    return *this;
}

auto PolBuilder::add_and_saturate(const XLiteral & lit, const NamesAndIDsTracker & tracker) -> PolBuilder &
{
    bool was_empty = _empty;
    add(lit, tracker);
    if (! was_empty)
        saturate();
    return *this;
}

auto PolBuilder::saturate() -> PolBuilder &
{
    _s << " s";
    return *this;
}

auto PolBuilder::multiply_by(Integer n) -> PolBuilder &
{
    _s << " " << n.raw_value << " *";
    return *this;
}

auto PolBuilder::divide_by(Integer n) -> PolBuilder &
{
    _s << " " << n.raw_value << " d";
    return *this;
}

auto PolBuilder::empty() const -> bool
{
    return _empty;
}

auto PolBuilder::str() const -> string
{
    return _s.str() + " ;";
}

auto PolBuilder::emit(ProofLogger & logger, ProofLevel level) -> ProofLine
{
    auto result = logger.emit_proof_line(str(), level);
    clear();
    return result;
}

auto PolBuilder::clear() -> void
{
    _s.str("");
    _s.clear();
    _s << "pol";
    _empty = true;
}
