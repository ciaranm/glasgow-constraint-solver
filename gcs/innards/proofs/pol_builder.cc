#include <gcs/exception.hh>
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
        _tokens.emplace_back(string{" +"});
}

auto PolBuilder::add(ProofLine line) -> PolBuilder &
{
    ProofLine resolved = _deview_tracker ? _deview_tracker->deviewed_line_for(line) : line;
    _tokens.emplace_back(resolved);
    separator_if_not_first();
    _empty = false;
    return *this;
}

auto PolBuilder::add(ProofLine line, Integer coeff) -> PolBuilder &
{
    if (coeff == 0_i)
        throw UnexpectedException{"PolBuilder::add called with zero coefficient"};
    ProofLine resolved = _deview_tracker ? _deview_tracker->deviewed_line_for(line) : line;
    _tokens.emplace_back(resolved);
    if (coeff != 1_i)
        _tokens.emplace_back(" " + std::to_string(coeff.raw_value) + " *");
    separator_if_not_first();
    _empty = false;
    return *this;
}

auto PolBuilder::add(const XLiteral & lit, const NamesAndIDsTracker & tracker) -> PolBuilder &
{
    _tokens.emplace_back(" " + tracker.pb_file_string_for(lit));
    separator_if_not_first();
    _empty = false;
    return *this;
}

auto PolBuilder::add(const XLiteral & lit, Integer coeff, const NamesAndIDsTracker & tracker) -> PolBuilder &
{
    if (coeff == 0_i)
        throw UnexpectedException{"PolBuilder::add called with zero coefficient"};
    _tokens.emplace_back(" " + tracker.pb_file_string_for(lit));
    if (coeff != 1_i)
        _tokens.emplace_back(" " + std::to_string(coeff.raw_value) + " *");
    separator_if_not_first();
    _empty = false;
    return *this;
}

auto PolBuilder::add_for_literal(NamesAndIDsTracker & tracker, const IntegerVariableCondition & lit) -> PolBuilder &
{
    visit(
        overloaded{[&](const ProofLine & l) { add(l); }, [&](const XLiteral & x) { add(x, tracker); }}, tracker.need_pol_item_defining_literal(lit));
    return *this;
}

auto PolBuilder::add_for_literal(NamesAndIDsTracker & tracker, const IntegerVariableCondition & lit, Integer coeff) -> PolBuilder &
{
    visit(overloaded{[&](const ProofLine & l) { add(l, coeff); }, [&](const XLiteral & x) { add(x, coeff, tracker); }},
        tracker.need_pol_item_defining_literal(lit));
    return *this;
}

auto PolBuilder::saturate() -> PolBuilder &
{
    _tokens.emplace_back(string{" s"});
    return *this;
}

auto PolBuilder::multiply_by(Integer n) -> PolBuilder &
{
    _tokens.emplace_back(" " + std::to_string(n.raw_value) + " *");
    return *this;
}

auto PolBuilder::divide_by(Integer n) -> PolBuilder &
{
    _tokens.emplace_back(" " + std::to_string(n.raw_value) + " d");
    return *this;
}

auto PolBuilder::empty() const -> bool
{
    return _empty;
}

auto PolBuilder::render(optional<long long> current_max) const -> string
{
    string out = "pol";
    for (const auto & t : _tokens)
        out += visit(overloaded{[&](const string & s) -> string { return s; },
                         [&](const ProofLine & l) -> string {
                             if (current_max)
                                 return " " + relative_proof_line(l, *current_max);
                             else if (auto n = std::get_if<ProofLineNumber>(&l))
                                 return " " + std::to_string(n->number);
                             else
                                 return " @" + std::get<ProofLineLabel>(l).label;
                         }},
            t);
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
    _tokens.clear();
    _empty = true;
}
