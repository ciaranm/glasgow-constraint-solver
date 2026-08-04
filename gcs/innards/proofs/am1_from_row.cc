#include <gcs/innards/proofs/am1_from_row.hh>
#include <gcs/innards/proofs/proof_error.hh>
#include <gcs/innards/proofs/proof_logger.hh>

#include <algorithm>
#include <numeric>
#include <string>
#include <vector>

using namespace gcs;
using namespace gcs::innards;

using std::min;
using std::to_string;
using std::vector;

auto gcs::innards::build_am1_from_row(PolBuilder & into, ProofLine capacity_row, const vector<Integer> & member_demands,
    const vector<ProofFlag> & weaken_out, Integer capacity, const NamesAndIDsTracker & tracker) -> Integer
{
    if (member_demands.empty())
        throw ProofError{"an at-most-one needs members to be about"};

    auto overshoot = std::accumulate(member_demands.begin(), member_demands.end(), 0_i) - capacity;
    if (overshoot <= 0_i)
        throw ProofError{"an at-most-one needs its members to overshoot the capacity, but they overshoot it by " + to_string(overshoot.raw_value)};

    // Saturation caps each coefficient at the degree, which weakening has left
    // at the overshoot; this is then the smallest divisor that brings every
    // capped coefficient down to one, and so the one that leaves the most
    // degree behind.
    auto largest = *std::max_element(member_demands.begin(), member_demands.end());
    auto divisor = min(largest, overshoot);

    into.add(capacity_row);
    for (const auto & flag : weaken_out)
        into.weaken(flag, tracker);
    into.saturate();
    into.divide_by(divisor);

    // Every member's coefficient is one by the choice of divisor, so the line
    // says `sum ~a_i >= ceil(overshoot / divisor)` over `|K|` of them.
    auto rounded_up = (overshoot + divisor - 1_i) / divisor;
    return Integer{static_cast<long long>(member_demands.size())} - rounded_up;
}

auto gcs::innards::recover_am1_from_row(ProofLogger & logger, ProofLine capacity_row, const vector<Integer> & member_demands,
    const vector<ProofFlag> & weaken_out, Integer capacity, ProofLevel level) -> Am1FromRow
{
    PolBuilder bound;
    auto at_most = build_am1_from_row(bound, capacity_row, member_demands, weaken_out, capacity, logger.names_and_ids_tracker());
    return Am1FromRow{bound.emit(logger, level), at_most};
}
