#include <gcs/constraints/cumulative/derived_cumulative_stats.hh>

using namespace gcs;

using std::string;
using std::vector;

auto DerivedCumulativeStats::add_entries_to(vector<StatsEntry> & entries, const string & prefix) const -> void
{
    entries.push_back(StatsEntry{prefix + "constraints", static_cast<long long>(constraints)});
    entries.push_back(StatsEntry{prefix + "donors", static_cast<long long>(donors)});
    entries.push_back(StatsEntry{prefix + "capacity_rows", static_cast<long long>(capacity_rows)});
    entries.push_back(StatsEntry{prefix + "makespan_bounds_posted", static_cast<long long>(makespan_bounds_posted)});
}
