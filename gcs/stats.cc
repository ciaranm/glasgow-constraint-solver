#include <gcs/stats.hh>

#include <algorithm>
#include <chrono>
#include <iostream>
#include <ostream>
#include <utility>

using namespace gcs;

using std::move;
using std::ostream;
using std::shared_ptr;
using std::string;
using std::vector;

ComponentStats::~ComponentStats() = default;

auto gcs::render(const StatsNote & note) -> string
{
    string result;
    if (note.level != StatsLevel::Important && ! note.component.empty())
        result += note.component + ": ";
    result += note.text;
    if (note.constraint)
        result += " (" + as_string(*note.constraint) + ")";
    return result;
}

auto gcs::default_stats_report(StatsLevel level) -> StatsReportCallback
{
    return [level](const StatsNote & note) -> void {
        if (note.level >= level)
            std::cerr << render(note) << '\n';
    };
}

auto gcs::silent_stats_report() -> StatsReportCallback
{
    return [](const StatsNote &) -> void {};
}

auto Stats::add_component(shared_ptr<const ComponentStats> component) -> void
{
    if (! component)
        return;
    // A constraint installed many times, or a presolver whose run() is reached
    // more than once, reports one aggregate rather than one entry per install.
    if (_components.end() != std::ranges::find(_components, component))
        return;
    _components.push_back(move(component));
}

auto Stats::report(StatsNote note) -> void
{
    if (_handler)
        _handler(note);
    _notes.push_back(move(note));
}

auto Stats::set_report_handler(StatsReportCallback handler) -> void
{
    _handler = move(handler);
}

auto Stats::components() const -> const vector<shared_ptr<const ComponentStats>> &
{
    return _components;
}

auto Stats::notes() const -> const vector<StatsNote> &
{
    return _notes;
}

auto gcs::operator<<(ostream & o, const Stats & s) -> ostream &
{
    o << "propagators: " << s.n_propagators << '\n';
    if (0 != s.idempotence_downgrades)
        o << "idempotence downgrades: " << s.idempotence_downgrades << '\n';
    o << "recursions: " << s.recursions << '\n';
    o << "failures: " << s.failures << '\n';
    o << "propagations: " << s.propagations << " " << s.effectful_propagations << " " << s.contradicting_propagations << '\n';
    o << "max depth:  " << s.max_depth << '\n';
    o << "restarts: " << s.restarts << '\n';
    o << "learned nogoods: " << s.learned_nogoods << '\n';
    o << "solutions: " << s.solutions << '\n';
    o << "solve time: " << (s.solve_time.count() / 1'000'000.0) << "s" << '\n';

    for (const auto & component : s.components())
        o << component->component_name() << ": " << component->summary() << '\n';

    for (const auto & note : s.notes())
        if (note.level >= StatsLevel::General)
            o << render(note) << '\n';

    return o;
}
