#include <gcs/innards/proofs/flag_bridge.hh>
#include <gcs/innards/proofs/names_and_ids_tracker.hh>
#include <gcs/innards/proofs/pol_builder.hh>
#include <gcs/innards/proofs/proof_error.hh>
#include <gcs/innards/proofs/proof_logger.hh>
#include <gcs/innards/proofs/pseudo_boolean.hh>

#include <cstddef>
#include <string>
#include <utility>
#include <vector>

using namespace gcs;
using namespace gcs::innards;

using std::move;
using std::size_t;
using std::string;
using std::to_string;
using std::vector;

namespace
{
    // A fully reified flag's two halves, under the labels ProofModel gives
    // them: `[r]` is `flag -> ineq` and `[f]` is `ineq -> flag`. The names read
    // backwards, which is ProofModel's doing and not worth diverging from here.
    //
    // Built from the flag's full PB rendering rather than from name_of, which
    // for a flag made from a plain stem returns just that stem and would name
    // the wrong row --- or none. ProofModel labels these halves the same way,
    // and says so where it does it.
    [[nodiscard]] auto label_base(const NamesAndIDsTracker & tracker, const ProofFlag & flag) -> string
    {
        if (! flag.positive)
            throw ProofError{"flag bridge: bridging a negated flag, whose reification halves are labelled under the positive one"};
        return tracker.pb_file_string_for(flag);
    }

    [[nodiscard]] auto implies_condition(const NamesAndIDsTracker & tracker, const ProofFlag & flag) -> ProofLine
    {
        return reification_half(tracker, flag, ReificationHalf::Implies);
    }

    [[nodiscard]] auto implied_by_condition(const NamesAndIDsTracker & tracker, const ProofFlag & flag) -> ProofLine
    {
        return reification_half(tracker, flag, ReificationHalf::ImpliedBy);
    }
}

auto gcs::innards::reification_half(const NamesAndIDsTracker & tracker, const ProofFlag & flag, ReificationHalf which) -> ProofLine
{
    if (auto in_proof = tracker.in_proof_reification(flag))
        return which == ReificationHalf::Implies ? in_proof->first : in_proof->second;
    return ProofLineLabel{label_base(tracker, flag) + (which == ReificationHalf::Implies ? "[r]" : "[f]")};
}

auto gcs::innards::recover_flag_bridge(ProofLogger & logger, const ProofFlag & from, const ProofFlag & to, ProofLevel level) -> ProofLine
{
    auto & tracker = logger.names_and_ids_tracker();

    // `from -> ineq` plus `ineq -> to`. The inequality goes in once with each
    // sign, so all of it cancels --- however many variables and bits it
    // mentions --- and saturation turns the remainder into the clause.
    PolBuilder bridge;
    bridge.add(implies_condition(tracker, from));
    bridge.add(implied_by_condition(tracker, to));
    bridge.saturate();
    return bridge.emit(logger, level);
}

auto gcs::innards::recover_conjunction_flag_bridge(ProofLogger & logger, const ProofFlag & from, const vector<ProofFlag> & from_conjuncts,
    const ProofFlag & to, const vector<ProofFlag> & to_conjuncts, ProofLevel level) -> ProofLine
{
    if (from_conjuncts.size() != to_conjuncts.size())
        throw ProofError{"conjunction bridge: " + to_string(from_conjuncts.size()) + " conjuncts on one side and " + to_string(to_conjuncts.size()) +
            " on the other, so they cannot correspond"};
    if (from_conjuncts.empty())
        throw ProofError{"conjunction bridge: no conjuncts to bridge"};

    auto & tracker = logger.names_and_ids_tracker();

    // Bridge the conjuncts first: those *are* reified on the same inequality as
    // each other, one pol apiece.
    vector<ProofLine> conjunct_bridges;
    conjunct_bridges.reserve(from_conjuncts.size());
    for (size_t i = 0; i < from_conjuncts.size(); ++i)
        conjunct_bridges.push_back(recover_flag_bridge(logger, from_conjuncts[i], to_conjuncts[i], level));

    // Then every conjunct appears once positively (out of `from`'s [r] half,
    // which says all of them hold) and once negatively (out of `to`'s [f] half,
    // which says one of them fails), with the bridges carrying each across.
    // They all cancel, and saturation clears the multiplicities the
    // conjunction's arity leaves behind.
    PolBuilder combine;
    combine.add(implies_condition(tracker, from));
    for (const auto & bridge : conjunct_bridges)
        combine.add(bridge);
    combine.add(implied_by_condition(tracker, to));
    combine.saturate();
    return combine.emit(logger, level);
}

auto gcs::innards::recover_bridged_row(ProofLogger & logger, ProofLine row, const vector<BridgedRowTerm> & terms,
    const vector<ProofFlag> & weaken_out, Integer capacity, ProofLevel level) -> ProofLine
{
    if (terms.empty())
        throw ProofError{"bridged row: no terms to carry across, so there would be nothing left of the row"};

    // Weaken first, so that the terms being carried are all there is left, and
    // then add each one's bridge as many times as its coefficient. Every flag
    // the row mentions then appears once with each sign and cancels, and the
    // constants that leaves behind are exactly what the degree loses, so the
    // right-hand side does not move.
    //
    // No saturation: the row wanted is the row the arithmetic lands on, and
    // capping a coefficient at the degree would quietly hand back a different
    // one --- stronger, which the pin below would accept without comment.
    //
    // A term nobody asked to weaken out is not a soundness problem, since the
    // pin drops it again; it only makes this pol wider than it needed to be.
    PolBuilder carry;
    carry.add(row);
    for (const auto & flag : weaken_out)
        carry.weaken(flag, logger.names_and_ids_tracker());
    for (const auto & term : terms)
        if (term.implies_row_flag)
            carry.add(*term.implies_row_flag, term.coefficient);
    auto carried = carry.emit(logger, level);

    WPBSum bridged;
    for (const auto & term : terms)
        bridged += term.coefficient * term.flag;
    return logger.emit(ImpliesProofRule{carried}, move(bridged) <= capacity, level);
}
