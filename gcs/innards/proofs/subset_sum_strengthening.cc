#include <gcs/innards/proofs/names_and_ids_tracker.hh>
#include <gcs/innards/proofs/pol_builder.hh>
#include <gcs/innards/proofs/proof_error.hh>
#include <gcs/innards/proofs/proof_logger.hh>
#include <gcs/innards/proofs/simplify_literal.hh>
#include <gcs/innards/proofs/subset_sum_strengthening.hh>

#include <util/overloaded.hh>

#include <algorithm>
#include <cstdint>
#include <map>
#include <numeric>
#include <string>
#include <vector>

using namespace gcs;
using namespace gcs::innards;

using std::map;
using std::string;
using std::to_string;
using std::vector;

namespace
{
    // The file-format literal for a term, so that it can be pushed onto a pol
    // stack as a literal axiom (`x >= 0`). Constants have no literal, and an
    // item that is always in or always out of the sum is a caller error rather
    // than something to silently ignore.
    auto xliteral_of(NamesAndIDsTracker & tracker, const ProofLiteralOrFlag & term) -> XLiteral
    {
        return overloaded{//
            [&](const ProofLiteral & l) -> XLiteral {
                return overloaded{                                                                                                        //
                    [&](const VariableConditionFrom<SimpleIntegerVariableID> & c) { return tracker.xliteral_for_ensuring(c); },           //
                    [&](const ProofVariableCondition & c) { return tracker.xliteral_for_ensuring(c); },                                   //
                    [&](const TrueLiteral &) -> XLiteral { throw ProofError{"subset sum strengthening over a constantly true term"}; },   //
                    [&](const FalseLiteral &) -> XLiteral { throw ProofError{"subset sum strengthening over a constantly false term"}; }} //
                    .visit(simplify_literal(tracker, l));
            },                                                                     //
            [&](const ProofFlag & f) { return tracker.xliteral_for(f); },          //
            [&](const ProofBitVariable & b) { return tracker.get_bit(b).second; }} //
            .visit(term);
    }

    // Which sums the coefficients can reach, as a bitset: bit v is set iff some
    // subset sums to v. mask |= mask << c per item, which is the whole
    // algorithm.
    auto reachable_sums(const vector<Integer> & coefficients, Integer bound) -> vector<uint64_t>
    {
        auto words = static_cast<size_t>(bound.raw_value / 64 + 1);
        vector<uint64_t> mask(words, 0);
        mask[0] = 1;

        for (const auto & c : coefficients) {
            if (c > bound)
                continue;
            auto shift = static_cast<size_t>(c.raw_value);
            auto word_shift = shift / 64, bit_shift = shift % 64;
            // Descending, so that each item is used at most once.
            for (size_t w = words; w-- > 0;) {
                uint64_t shifted = 0;
                if (w >= word_shift) {
                    shifted = mask[w - word_shift] << bit_shift;
                    if (bit_shift != 0 && w > word_shift)
                        shifted |= mask[w - word_shift - 1] >> (64 - bit_shift);
                }
                mask[w] |= shifted;
            }
        }

        // Bits past the bound are meaningless (the shifts run off the end of
        // the last word), so clear them rather than let a caller read one.
        auto top = static_cast<size_t>(bound.raw_value % 64);
        if (top != 63)
            mask[words - 1] &= (uint64_t{1} << (top + 1)) - 1;

        return mask;
    }

    auto is_reachable(const vector<uint64_t> & mask, Integer v) -> bool
    {
        return 0 != (mask[static_cast<size_t>(v.raw_value / 64)] & (uint64_t{1} << (v.raw_value % 64)));
    }

    // One reachable partial sum, at one layer: the flags saying the prefix sum
    // is at least it, at most it, and (their conjunction) exactly it, with the
    // two halves of each reification.
    struct LayerState
    {
        ProofFlag at_least, at_most, exactly;
        ProofLine at_least_forward, at_least_reverse;
        ProofLine at_most_forward, at_most_reverse;
        ProofLine exactly_forward;
    };

    auto make_state(ProofLogger & logger, const WPBSum & prefix, Integer value, size_t layer, ProofLevel level) -> LayerState
    {
        auto tag = "_" + to_string(layer) + "_" + to_string(value.raw_value);
        auto [at_least, ge_fwd, ge_rev] = logger.create_proof_flag_reifying(prefix >= value, "ssge" + tag, level);
        auto [at_most, le_fwd, le_rev] = logger.create_proof_flag_reifying(prefix <= value, "ssle" + tag, level);
        auto [exactly, eq_fwd, eq_rev] = logger.create_proof_flag_reifying(WPBSum{} + 1_i * at_least + 1_i * at_most >= 2_i, "sseq" + tag, level);
        return LayerState{at_least, at_most, exactly, ge_fwd, ge_rev, le_fwd, le_rev, eq_fwd};
    }
}

auto gcs::innards::largest_subset_sum_at_most(const vector<Integer> & coefficients, Integer bound) -> Integer
{
    if (bound < 0_i)
        throw ProofError{"subset sum strengthening needs a non-negative bound"};
    for (const auto & c : coefficients)
        if (c <= 0_i)
            throw ProofError{"subset sum strengthening needs strictly positive coefficients"};

    auto mask = reachable_sums(coefficients, bound);
    for (Integer v = bound; v >= 0_i; --v)
        if (is_reachable(mask, v))
            return v;

    throw ProofError{"subset sum strengthening: zero is always reachable"};
}

auto gcs::innards::derive_subset_sum_strengthening(ProofLogger & logger, const vector<SubsetSumItem> & items, ProofLine source, Integer bound,
    ProofLevel level, SubsetSumMutation mutation) -> SubsetSumStrengthening
{
    vector<Integer> coefficients;
    coefficients.reserve(items.size());
    for (const auto & item : items)
        coefficients.push_back(item.coefficient);

    auto strengthened = largest_subset_sum_at_most(coefficients, bound);
    auto claim_one_better = std::holds_alternative<subset_sum_mutation::ClaimOneBetter>(mutation);
    auto bogus_divisor = std::holds_alternative<subset_sum_mutation::BogusDivisor>(mutation);
    auto skip_a_layer = std::holds_alternative<subset_sum_mutation::SkipALayer>(mutation);

    // Nothing to say: the bound is already a sum the coefficients can reach.
    // Re-deriving it would be a line that says exactly what the caller already
    // had.
    if (strengthened == bound && ! claim_one_better && ! bogus_divisor)
        return SubsetSumStrengthening{source, bound, false};

    auto claimed = claim_one_better ? strengthened - 1_i : strengthened;

    auto & tracker = logger.names_and_ids_tracker();

    WPBSum total;
    for (const auto & item : items)
        add_term_to(total, item.coefficient, item.term);

    // Divisibility: every coefficient is a multiple of d, so the sum is too,
    // and rounding the bound down to a multiple of d loses nothing. Divide,
    // then multiply back --- Chvatal-Gomory rounding in two pol steps.
    auto divisor = 0_i;
    for (const auto & c : coefficients)
        divisor = Integer{std::gcd(divisor.raw_value, c.raw_value)};
    if (bogus_divisor) {
        // The smallest divisor that does *not* divide everything. Dividing by
        // it is still a sound proof step --- division rounds --- but the line
        // it lands on is not the one the caller is told about.
        divisor = 2_i;
        while (std::all_of(coefficients.begin(), coefficients.end(), [&](const Integer & c) { return c % divisor == 0_i; }))
            ++divisor;
    }

    if (bogus_divisor || (divisor > 1_i && divisor * (bound / divisor) == claimed)) {
        PolBuilder rounding;
        rounding.add(source);
        rounding.divide_by(divisor);
        rounding.multiply_by(divisor);
        logger.emit_proof_comment("subset sum strengthening by divisibility: " + to_string(bound.raw_value) + " to " + to_string(claimed.raw_value) +
            ", divisor " + to_string(divisor.raw_value));
        return SubsetSumStrengthening{rounding.emit(logger, level), claimed, true};
    }

    logger.emit_proof_comment(
        "subset sum strengthening by dynamic programming: " + to_string(bound.raw_value) + " to " + to_string(claimed.raw_value));

    // Layered dynamic programming. Layer k speaks about the prefix sum of the
    // first k items, and has one state per value that prefix can reach without
    // already exceeding the bound. A prefix that exceeds the bound is dead: the
    // source line says the whole sum is at most the bound, and every remaining
    // coefficient is non-negative, so no such prefix can be completed.
    vector<map<Integer, LayerState>> layers;
    WPBSum prefix;

    layers.emplace_back();
    layers.back().emplace(0_i, make_state(logger, prefix, 0_i, 0, level));
    // Layer zero's prefix is the empty sum, so both halves are tautologies and
    // both flags are pinned true by their own reifications: the at-least-one
    // is a one-line RUP. Every later layer's at-least-one is a RUP against the
    // previous one, which is why they are emitted rather than kept: unit
    // propagation finds them in the database.
    logger.emit_rup_proof_line(WPBSum{} + 1_i * layers.back().at(0_i).exactly >= 1_i, level);

    for (size_t k = 0; k < items.size(); ++k) {
        const auto & item = items[k];
        auto item_literal = xliteral_of(tracker, item.term);
        auto negated_item_literal = xliteral_of(tracker, ! item.term);

        const auto & before = layers.back();
        auto after_prefix = prefix;
        add_term_to(after_prefix, item.coefficient, item.term);

        // The states this layer can be in, and the transitions into them.
        map<Integer, LayerState> after;
        for (const auto & [value, state] : before) {
            if (! after.contains(value))
                after.emplace(value, make_state(logger, after_prefix, value, k + 1, level));
            auto advanced = value + item.coefficient;
            if (advanced <= bound && ! after.contains(advanced))
                after.emplace(advanced, make_state(logger, after_prefix, advanced, k + 1, level));
        }

        // Tests only: leaving one layer's transitions out means its
        // at-least-one has nothing to stand on.
        auto skip_this_layer = skip_a_layer && k == items.size() / 2;

        for (const auto & [value, state] : before) {
            const auto & stay = after.at(value);
            auto advanced = value + item.coefficient;

            // Carrying the lower bound needs nothing: the prefix sum only ever
            // grows. Carrying the upper bound needs the item to be out.
            PolBuilder carry_at_least;
            carry_at_least.add(state.at_least_forward).add(stay.at_least_reverse).add(item_literal, item.coefficient, tracker).saturate();
            carry_at_least.emit(logger, level);

            PolBuilder carry_at_most;
            carry_at_most.add(state.at_most_forward).add(stay.at_most_reverse).saturate();
            carry_at_most.emit(logger, level);

            // Item out: the state stays where it was.
            WPBSum stays;
            stays += 1_i * ! state.exactly;
            add_term_to(stays, 1_i, item.term);
            stays += 1_i * stay.exactly;
            auto stay_transition = logger.emit_rup_proof_line(move(stays) >= 1_i, level);

            if (advanced <= bound) {
                const auto & step = after.at(advanced);

                // Advancing the lower bound needs the item to be in; advancing
                // the upper bound needs nothing, since the item can add at
                // most its coefficient.
                PolBuilder advance_at_least;
                advance_at_least.add(state.at_least_forward)
                    .add(step.at_least_reverse)
                    .add(negated_item_literal, item.coefficient, tracker)
                    .saturate();
                advance_at_least.emit(logger, level);

                PolBuilder advance_at_most;
                advance_at_most.add(state.at_most_forward).add(step.at_most_reverse).add(negated_item_literal, item.coefficient, tracker).saturate();
                advance_at_most.emit(logger, level);

                WPBSum steps;
                steps += 1_i * ! state.exactly;
                add_term_to(steps, 1_i, ! item.term);
                steps += 1_i * step.exactly;
                auto step_transition = logger.emit_rup_proof_line(move(steps) >= 1_i, level);

                // Either way the layer moves to one of the two states:
                // resolving the two transitions on the item literal.
                if (! skip_this_layer) {
                    PolBuilder resolve;
                    resolve.add(stay_transition).add(step_transition).saturate();
                    resolve.emit(logger, level);
                }
            }
            else {
                // Taking the item from here would put the prefix past the
                // bound, which the source line forbids. So the item is out,
                // and the only transition is the one that stays.
                PolBuilder dead;
                dead.add(state.at_least_forward).add(source);
                for (size_t later = k + 1; later < items.size(); ++later)
                    dead.add(xliteral_of(tracker, items[later].term), items[later].coefficient, tracker);
                dead.add(negated_item_literal, item.coefficient, tracker).saturate();
                dead.emit(logger, level);

                WPBSum out;
                out += 1_i * ! state.exactly;
                add_term_to(out, 1_i, ! item.term);
                auto item_is_out = logger.emit_rup_proof_line(move(out) >= 1_i, level);

                if (! skip_this_layer) {
                    PolBuilder resolve;
                    resolve.add(stay_transition).add(item_is_out).saturate();
                    resolve.emit(logger, level);
                }
            }
        }

        // The prefix sum is in one of this layer's states: with every
        // transition in hand, that follows from the previous layer's version
        // of the same statement.
        WPBSum at_least_one;
        for (const auto & [value, state] : after)
            at_least_one += 1_i * state.exactly;
        logger.emit_rup_proof_line(move(at_least_one) >= 1_i, level);

        layers.push_back(move(after));
        prefix = move(after_prefix);
    }

    // Every state of the last layer is at most the strengthened bound --- that
    // is what makes it the strengthened bound --- so whichever one holds, the
    // sum is under it.
    auto [under, under_forward, under_reverse] = logger.create_proof_flag_reifying(total <= claimed, "ssunder", level);
    for (const auto & [value, state] : layers.back()) {
        PolBuilder dominated;
        dominated.add(state.at_most_forward).add(under_reverse).saturate();
        dominated.emit(logger, level);
        logger.emit_rup_proof_line(WPBSum{} + 1_i * ! state.exactly + 1_i * under >= 1_i, level);
    }

    auto under_holds = logger.emit_rup_proof_line(WPBSum{} + 1_i * under >= 1_i, level);

    // Discharge the flag: its forward half is the strengthened line, weakened
    // by the reification coefficient, and the unit above pays exactly that
    // coefficient back.
    auto shape = tracker.reification_shape(total <= claimed, HalfReifyOnConjunctionOf{{under}});
    PolBuilder discharge;
    discharge.add(under_forward).add(under_holds, -shape.reif_coefficient);
    return SubsetSumStrengthening{discharge.emit(logger, level), claimed, false};
}
