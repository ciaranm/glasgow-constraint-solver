#include <gcs/innards/proofs/lifted_cover_cut.hh>
#include <gcs/innards/proofs/names_and_ids_tracker.hh>
#include <gcs/innards/proofs/pol_builder.hh>
#include <gcs/innards/proofs/proof_error.hh>
#include <gcs/innards/proofs/proof_logger.hh>
#include <gcs/innards/proofs/pseudo_boolean.hh>

#include <algorithm>
#include <numeric>
#include <optional>
#include <vector>

using namespace gcs;
using namespace gcs::innards;

using std::max;
using std::move;
using std::nullopt;
using std::optional;
using std::size_t;
using std::vector;

namespace
{
    /// How many copies of the row and of the running cut a lifting step may
    /// take. Every certificate wanted by the corpus behind this file needs at
    /// most two of each; the rest is headroom, and it is bounded because a
    /// search that never gives up is a presolver that never returns.
    const Integer max_copies = 8_i;

    /**
     * A constraint as VeriPB normalises it: `sum c_i ~a_i >= degree` over the
     * members' complemented activity literals, which is the form both a
     * capacity row and every cut derived from one take. Nothing here ever adds
     * a literal to its own negation, so no cancellation can arise and the
     * coefficients stay parallel to the caller's member vectors.
     */
    struct Normalised
    {
        vector<Integer> coefficients;
        Integer degree;

        [[nodiscard]] auto saturated() const -> Normalised
        {
            auto result = *this;
            for (auto & c : result.coefficients)
                c = std::min(c, degree);
            return result;
        }

        [[nodiscard]] auto divided_by(Integer d) const -> Normalised
        {
            auto ceiling = [&](Integer x) { return (x + d - 1_i) / d; };
            auto result = *this;
            for (auto & c : result.coefficients)
                c = ceiling(c);
            result.degree = ceiling(degree);
            return result;
        }

        [[nodiscard]] auto plus(const Normalised & other, Integer copies) const -> Normalised
        {
            auto result = *this;
            for (size_t i = 0; i < coefficients.size(); ++i)
                result.coefficients[i] += other.coefficients[i] * copies;
            result.degree += other.degree * copies;
            return result;
        }

        [[nodiscard]] auto scaled_by(Integer copies) const -> Normalised
        {
            auto result = *this;
            for (auto & c : result.coefficients)
                c = c * copies;
            result.degree = degree * copies;
            return result;
        }

        [[nodiscard]] auto largest_coefficient() const -> Integer
        {
            return *std::max_element(coefficients.begin(), coefficients.end());
        }

        [[nodiscard]] auto operator==(const Normalised & other) const -> bool = default;
    };

    /// The capacity row `sum c_i a_i <= C` complemented and then weakened down
    /// to `support`: weakening drops a task's term and takes its demand off the
    /// degree, so what is left says the support alone overshoots by this much.
    [[nodiscard]] auto row_weakened_to(const vector<Integer> & demands, Integer capacity, const vector<size_t> & support) -> Normalised
    {
        Normalised result{vector<Integer>(demands.size(), 0_i), -capacity};
        for (auto i : support) {
            result.coefficients[i] = demands[i];
            result.degree += demands[i];
        }
        return result;
    }

    /// What the caller is asking to arrive at, over `support`.
    [[nodiscard]] auto target_over(const vector<Integer> & coefficients, Integer rhs, const vector<size_t> & support) -> Normalised
    {
        Normalised result{vector<Integer>(coefficients.size(), 0_i), -rhs};
        for (auto i : support) {
            result.coefficients[i] = coefficients[i];
            result.degree += coefficients[i];
        }
        return result;
    }

    /// Saturate or not, then divide by something: the tail every step shares.
    /// Calls `accept` with each (saturate, divisor) whose result is `target`.
    template <typename Accept_>
    [[nodiscard]] auto round_onto(const Normalised & combined, const Normalised & target, const Accept_ & accept) -> bool
    {
        if (combined.degree <= 0_i)
            return false;

        for (auto saturate : {false, true}) {
            auto rounded = saturate ? combined.saturated() : combined;
            // A divisor bigger than every coefficient and than the degree only
            // rounds further down, so there is nothing above that to try.
            auto top = max(rounded.largest_coefficient(), rounded.degree);
            for (auto divisor = 1_i; divisor <= top; ++divisor)
                if (rounded.divided_by(divisor) == target && accept(saturate, divisor))
                    return true;
        }
        return false;
    }

    /// Lift `member` into `current` over `support`: `row_copies` of the row
    /// weakened to the support plus the new member, `cut_copies` of the cut so
    /// far, rounded onto the target.
    [[nodiscard]] auto plan_lifting_step(const vector<Integer> & demands, const vector<Integer> & coefficients, Integer capacity, Integer rhs,
        const vector<size_t> & support, size_t member, const Normalised & current) -> optional<LiftedCoverCutStep>
    {
        auto grown = support;
        grown.push_back(member);
        auto row = row_weakened_to(demands, capacity, grown);
        auto target = target_over(coefficients, rhs, grown);

        optional<LiftedCoverCutStep> found;
        for (auto row_copies = 1_i; row_copies <= max_copies && ! found; ++row_copies)
            for (auto cut_copies = 0_i; cut_copies <= max_copies && ! found; ++cut_copies) {
                auto combined = row.scaled_by(row_copies).plus(current, cut_copies);
                [[maybe_unused]] auto landed = round_onto(combined, target, [&](bool saturate, Integer divisor) {
                    found = LiftedCoverCutStep{grown, row_copies, cut_copies, saturate, divisor};
                    return true;
                });
            }
        return found;
    }

    /// The covers worth trying, largest demands first. Exhaustive while the
    /// budget allows, since a derived constraint's support is small by
    /// construction; a greedy family beyond that, which is a refusal risk and
    /// never a soundness one.
    [[nodiscard]] auto candidate_covers(const vector<Integer> & demands, Integer capacity, const vector<size_t> & by_demand, size_t max_covers)
        -> vector<vector<size_t>>
    {
        auto overshoots = [&](const vector<size_t> & set) {
            return std::accumulate(set.begin(), set.end(), 0_i, [&](Integer a, size_t i) { return a + demands[i]; }) > capacity;
        };

        vector<vector<size_t>> covers;
        auto n = by_demand.size();
        if (n < 64 && (1uLL << n) <= max_covers) {
            for (unsigned long long mask = 1; mask < (1uLL << n); ++mask) {
                vector<size_t> cover;
                for (size_t k = 0; k < n; ++k)
                    if (mask & (1uLL << k))
                        cover.push_back(by_demand[k]);
                if (cover.size() >= 2 && overshoots(cover))
                    covers.push_back(move(cover));
            }
        }
        else {
            for (size_t start = 0; start < n && covers.size() < max_covers; ++start) {
                vector<size_t> cover;
                for (size_t k = start; k < n; ++k) {
                    cover.push_back(by_demand[k]);
                    if (cover.size() >= 2 && overshoots(cover)) {
                        covers.push_back(cover);
                        break;
                    }
                }
            }
        }
        return covers;
    }
}

auto gcs::innards::grow_lifted_cover_cut(const vector<Integer> & demands, const vector<Integer> & weights, Integer capacity,
    const vector<size_t> & cover, size_t max_support) -> optional<LiftedCoverCut>
{
    if (demands.size() != weights.size())
        throw ProofError{"a lifted cover cut needs one weight per demand"};
    if (cover.size() < 2)
        return nullopt;

    // The cover inequality, as build_am1_from_row recovers it: weaken to the
    // cover, saturate, and divide by the margin, which is the smallest divisor
    // bringing every capped coefficient down to one.
    auto base = row_weakened_to(demands, capacity, cover);
    if (base.degree <= 0_i)
        return nullopt;
    auto largest = 0_i;
    for (auto i : cover)
        largest = max(largest, demands[i]);
    auto divisor = std::min(largest, base.degree);

    LiftedCoverCut result{{}, 0_i, {LiftedCoverCutStep{cover, 1_i, 0_i, true, divisor}}};
    auto current = base.saturated().divided_by(divisor);
    auto right_hand_side = [](const Normalised & cut) { return std::accumulate(cut.coefficients.begin(), cut.coefficients.end(), 0_i) - cut.degree; };
    if (right_hand_side(current) < 1_i)
        return nullopt;

    // What the caller is ranking by: the weight the cut's members carry per
    // unit of its right-hand side. Compared by cross-multiplication, since
    // whether one ratio beats another is the whole question and rounding it
    // first would decide some of them wrongly.
    auto weight_of = [&](const Normalised & cut) {
        auto total = 0_i;
        for (size_t i = 0; i < weights.size(); ++i)
            total += weights[i] * cut.coefficients[i];
        return total;
    };

    auto support = cover;
    vector<size_t> by_demand(demands.size());
    std::iota(by_demand.begin(), by_demand.end(), size_t{0});
    std::sort(by_demand.begin(), by_demand.end(), [&](size_t a, size_t b) {
        if (demands[a] != demands[b])
            return demands[a] > demands[b];
        return a < b;
    });

    for (auto member : by_demand) {
        if (support.size() >= max_support)
            break;
        if (std::find(support.begin(), support.end(), member) != support.end())
            continue;

        auto grown = support;
        grown.push_back(member);
        auto row = row_weakened_to(demands, capacity, grown);

        optional<Normalised> best;
        optional<LiftedCoverCutStep> best_step;
        for (auto row_copies = 1_i; row_copies <= max_copies; ++row_copies)
            for (auto cut_copies = 0_i; cut_copies <= max_copies; ++cut_copies) {
                auto combined = row.scaled_by(row_copies).plus(current, cut_copies);
                if (combined.degree <= 0_i)
                    continue;
                for (auto saturate : {false, true}) {
                    auto rounded = saturate ? combined.saturated() : combined;
                    auto top = max(rounded.largest_coefficient(), rounded.degree);
                    for (auto d = 1_i; d <= top; ++d) {
                        auto got = rounded.divided_by(d);
                        // A member whose coefficient came out at zero is not in
                        // this cut, and a right-hand side below one is a
                        // constraint saying nothing may run --- neither is a
                        // Cumulative the caller can post.
                        if (std::any_of(grown.begin(), grown.end(), [&](size_t i) { return got.coefficients[i] < 1_i; }))
                            continue;
                        auto rhs = right_hand_side(got);
                        if (rhs < 1_i)
                            continue;
                        if (! best || weight_of(got) * right_hand_side(*best) > weight_of(*best) * rhs) {
                            best = got;
                            best_step = LiftedCoverCutStep{grown, row_copies, cut_copies, saturate, d};
                        }
                    }
                }
            }

        // Only worth taking if it argues about more than the cut already does.
        if (best && weight_of(*best) * right_hand_side(current) > weight_of(current) * right_hand_side(*best)) {
            current = *best;
            support = best_step->support;
            result.plan.push_back(move(*best_step));
        }
    }

    result.coefficients = current.coefficients;
    result.rhs = right_hand_side(current);
    return result;
}

auto gcs::innards::plan_lifted_cover_cut(const vector<Integer> & demands, const vector<Integer> & coefficients, Integer capacity, Integer rhs,
    size_t max_covers) -> optional<LiftedCoverCutPlan>
{
    if (demands.size() != coefficients.size())
        throw ProofError{"a lifted cover cut needs one coefficient per demand"};

    vector<size_t> everything(demands.size());
    std::iota(everything.begin(), everything.end(), size_t{0});

    // Nothing to derive: no 0/1 point can miss a degree of zero or less. This
    // is the usual state of affairs at the edges of a derived constraint's
    // window, where too few of its tasks have flags for their coefficients to
    // reach the right-hand side.
    auto target = target_over(coefficients, rhs, everything);
    if (target.degree <= 0_i)
        return LiftedCoverCutPlan{};

    if (demands.empty())
        return nullopt;

    // One `pol`: the whole row, weakened to the members, saturated or not, and
    // divided. This is build_am1_from_row's program with the divisor free, and
    // it is what almost everything needs.
    optional<LiftedCoverCutPlan> plan;
    if (round_onto(row_weakened_to(demands, capacity, everything), target, [&](bool saturate, Integer divisor) {
            plan = LiftedCoverCutPlan{LiftedCoverCutStep{everything, 1_i, 0_i, saturate, divisor}};
            return true;
        }))
        return plan;

    // Otherwise a cover, and then the rest of the members lifted into it one at
    // a time, which is where the non-unit coefficients reachable today come
    // from: `2a + b + c + d <= 2` from `5a + 2b + 2c + 2d <= 5` is one copy of
    // the row plus one of the cover cut, over three. A literal-axiom shave
    // would reach the same line in one `pol` and is not implemented; see #674
    // and the header, which says what the two families can and cannot do.
    auto by_demand = everything;
    std::sort(by_demand.begin(), by_demand.end(), [&](size_t a, size_t b) {
        if (demands[a] != demands[b])
            return demands[a] > demands[b];
        return a < b;
    });

    for (const auto & cover : candidate_covers(demands, capacity, by_demand, max_covers)) {
        LiftedCoverCutPlan steps;
        auto current = target_over(coefficients, rhs, cover);
        if (! round_onto(row_weakened_to(demands, capacity, cover), current, [&](bool saturate, Integer divisor) {
                steps.push_back(LiftedCoverCutStep{cover, 1_i, 0_i, saturate, divisor});
                return true;
            }))
            continue;

        auto support = cover;
        bool stuck = false;
        for (auto member : by_demand) {
            if (std::find(support.begin(), support.end(), member) != support.end())
                continue;
            auto step = plan_lifting_step(demands, coefficients, capacity, rhs, support, member, current);
            if (! step) {
                stuck = true;
                break;
            }
            support = step->support;
            current = target_over(coefficients, rhs, support);
            steps.push_back(move(*step));
        }

        if (! stuck && current == target)
            return steps;
    }

    return nullopt;
}

auto gcs::innards::derive_lifted_cover_cut(ProofLogger & logger, ProofLine capacity_row, const LiftedCoverCutPlan & plan,
    const vector<ProofFlag> & flags, const vector<Integer> & claimed_coefficients, const vector<ProofFlag> & weaken_out, Integer claimed_rhs,
    ProofLevel level) -> ProofLine
{
    if (flags.size() != claimed_coefficients.size())
        throw ProofError{"a lifted cover cut needs one coefficient per flag"};

    WPBSum claimed;
    for (size_t i = 0; i < flags.size(); ++i)
        claimed += claimed_coefficients[i] * flags[i];

    if (plan.empty())
        return logger.emit_rup_proof_line(move(claimed) <= claimed_rhs, level);

    // The intermediates go one level deeper than the caller's own, so that
    // forgetting them on the way out cannot take the caller's scope with them
    // --- the same isolation recover_am1() needs, and for the same reason: a
    // caller inside a JustifyExplicitly is already using its own Temporary
    // depth. Only the pin below survives this routine.
    auto saved_level = logger.proof_level();
    logger.enter_proof_level(saved_level + 1);

    const auto & tracker = logger.names_and_ids_tracker();
    optional<ProofLine> previous;
    for (const auto & step : plan) {
        PolBuilder pol;
        pol.add(capacity_row, step.row_copies);
        for (size_t i = 0; i < flags.size(); ++i)
            if (std::find(step.support.begin(), step.support.end(), i) == step.support.end())
                pol.weaken(flags[i], tracker);
        for (const auto & flag : weaken_out)
            pol.weaken(flag, tracker);
        if (step.cut_copies > 0_i) {
            if (! previous)
                throw ProofError{"a lifted cover cut's first step has no cut to take copies of"};
            pol.add(*previous, step.cut_copies);
        }
        if (step.saturate)
            pol.saturate();
        pol.divide_by(step.divisor);
        previous = pol.emit(logger, ProofLevel::Temporary);
    }

    // Restore the caller's level and pin there, while the scaffolding is still
    // alive for VeriPB to resolve the reference against, then drop the
    // scaffolding.
    logger.enter_proof_level(saved_level);
    auto result = logger.emit(ImpliesProofRule{previous}, move(claimed) <= claimed_rhs, level);
    logger.forget_proof_level(saved_level + 2);
    return result;
}
