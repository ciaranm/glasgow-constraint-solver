#include <gcs/constraints/cumulative/donor_view.hh>
#include <gcs/constraints/cumulative/propagate.hh>
#include <gcs/innards/power.hh>
#include <gcs/innards/proofs/bits_encoding.hh>
#include <gcs/innards/proofs/names_and_ids_tracker.hh>
#include <gcs/innards/proofs/pol_builder.hh>
#include <gcs/innards/proofs/proof_logger.hh>
#include <gcs/innards/proofs/pseudo_boolean.hh>
#include <gcs/innards/state.hh>

#include <algorithm>
#include <optional>
#include <utility>
#include <variant>
#include <vector>

using namespace gcs;
using namespace gcs::innards;

using std::make_optional;
using std::move;
using std::nullopt;
using std::optional;
using std::pair;
using std::size_t;
using std::vector;

auto gcs::innards::cumulative_donor_view(const Cumulative & donor, const State & state, const ProofLogger * const logger)
    -> optional<CumulativeDonorView>
{
    CumulativeDonorView view;
    auto n = donor.starts().size();

    // A view capacity has no bits of its own to cancel the row's against, so
    // there is no order literal to resolve and nothing to reduce it to. The
    // constant and simple-variable cases are what every model in reach uses.
    if (! is_constant_variable(donor.capacity()) && ! std::holds_alternative<SimpleIntegerVariableID>(donor.capacity()))
        return nullopt;

    if (is_constant_variable(donor.capacity()))
        view.capacity = constant_value_of(donor.capacity());
    else {
        view.capacity = state.upper_bound(donor.capacity());
        view.capacity_bounded_by = donor.capacity();
    }

    view.lengths.assign(n, constant_variable(0_i));
    view.heights.assign(n, 0_i);
    view.height_bounded_by.assign(n, nullopt);
    view.presences = donor.presences();

    for (size_t i = 0; i < n; ++i) {
        auto length = donor.lengths()[i], height = donor.heights()[i];

        // A variable height makes the donor's row terms the bits of a
        // linearised contribution rather than `height x active`, so a subset
        // sum of the heights is not a subset sum of the row's coefficients ---
        // until the contribution is converted back into a coefficient on the
        // activity flag, which recover_constant_argument_row does with the row
        // saying the contribution is at least the height. What that leaves is
        // the *guaranteed* demand, which is the height's lower bound.
        auto height_value = 0_i;
        if (is_constant_variable(height))
            height_value = constant_value_of(height);
        else {
            // A view's reification is over its own bit vector rather than the
            // underlying variable's, so the height's bound rows have nothing to
            // cancel against and there is no conversion to make. A zero lower
            // bound guarantees nothing, which is the same as having no term.
            // Either way, what is left is the set-aside this used to be.
            if (! std::holds_alternative<SimpleIntegerVariableID>(height) || state.lower_bound(height) <= 0_i) {
                view.set_aside.push_back(i);
                continue;
            }
            height_value = state.lower_bound(height);
            view.height_bounded_by[i] = height;
        }

        // A task that can never load the resource, or that was posted as
        // constantly absent, usually has no flags and no term in any row.
        // Asked before the length test below, and that is not an ordering
        // nicety: the donor gave such a
        // task no window, so it published no end proxy for it either, and
        // asking would come back with the same nullopt a genuinely unusable
        // duration does. The largest duration still allowed is what says
        // whether it can run at all, and is the same bound the donor windowed
        // its flags with.
        auto presence = task_presence(view.presences.empty() ? nullopt : make_optional(view.presences[i]), "Cumulative");
        if (state.upper_bound(length) <= 0_i || height_value <= 0_i || presence.never_present) {
            view.height_bounded_by[i] = nullopt;
            // Usually there is nothing here to set aside, because the donor
            // gave such a task no window and so no flags and no term. But these
            // are *today's* bounds against a donor that resolved its windows at
            // prepare() time, and a length whose upper bound has collapsed to
            // zero since is a task the donor did encode --- one whose terms
            // would then be left in every reduced row, which is a row not
            // saying what the recipe using it claims. Ask rather than assume.
            //
            // Asking at `lb(start)` is enough: bounds only tighten, so today's
            // is inside the window the donor windowed with, whatever has
            // happened to the length. A task the donor never encoded has no
            // flag there and stays out of `set_aside`, which matters --- a
            // posted zero height is not a donor being used in part, and the
            // counters that say so would stop meaning anything.
            if (logger &&
                logger->names_and_ids_tracker().find_proof_flag_values(
                    donor.constraint_id(), ConstraintProofModelData<Cumulative>::active_flag_key(i, state.lower_bound(donor.starts()[i]))))
                view.set_aside.push_back(i);
            continue;
        }

        // An *optional* task whose guaranteed demand alone exceeds the capacity
        // is one the donor's own propagator will falsify the presence of; it is
        // not a donor that cannot be satisfied. Set it aside, so that a caller
        // asking "is any usable task over the capacity" gets the question it
        // means to ask --- a donor that really is infeasible on its own ---
        // rather than an optional task that has simply not been decided yet,
        // and so that the rest of the donor keeps whatever it was going to get.
        if (presence.literal && height_value > view.capacity) {
            view.height_bounded_by[i] = nullopt;
            view.set_aside.push_back(i);
            continue;
        }

        // A variable length is not a set-aside. It leaves the row untouched ---
        // no length appears in one --- and costs the *pins* instead: `after` is
        // then reified on the two-variable `start + length`, which no RUP
        // reaches from the operands' bounds, so pinning it goes through the
        // donor's proof-only end proxy and through the line giving that proxy
        // its lower bound. That line is the donor's to publish, and asking for
        // it is the whole test: a constant start needs no proxy and publishes
        // none, and a proof written with assertions on omits the definition
        // along with everything else it asserts. With no logger there is
        // nothing to pin and nothing to ask.
        if (logger && ! is_constant_variable(length) && ! is_constant_variable(donor.starts()[i]) &&
            ! logger->names_and_ids_tracker().find_derived_line(
                donor.constraint_id(), ConstraintProofModelData<Cumulative>::end_lower_bound_role(i))) {
            view.height_bounded_by[i] = nullopt;
            view.set_aside.push_back(i);
            continue;
        }

        view.lengths[i] = length;
        view.heights[i] = height_value;
        view.usable.push_back(i);
    }

    return view;
}

auto CumulativeDonorView::with_converted_heights_set_aside() const -> CumulativeDonorView
{
    CumulativeDonorView result = *this;
    result.usable.clear();
    for (auto i : usable) {
        if (! height_bounded_by[i]) {
            result.usable.push_back(i);
            continue;
        }
        // Back to what it was before the conversion: no length and no height to
        // quote, its position among the ones every derived row is weakened
        // over, and nothing left saying it was ever convertible.
        result.lengths[i] = constant_variable(0_i);
        result.heights[i] = 0_i;
        result.height_bounded_by[i] = nullopt;
        result.set_aside.push_back(i);
    }
    std::sort(result.set_aside.begin(), result.set_aside.end());
    return result;
}

auto gcs::innards::recover_constant_argument_row(ProofLogger & logger, const CumulativeDonorView & view, const ConstraintID & donor, ProofLine row,
    Integer t, ProofLevel level) -> optional<ProofLine>
{
    auto & tracker = logger.names_and_ids_tracker();

    // Which of the set-aside tasks have a term in *this* row: one only appears
    // where the donor gave it a window, so asking for the flag is also asking
    // whether there is anything here to weaken.
    vector<ProofFlag> weaken_out;
    for (auto i : view.set_aside) {
        if (auto active = tracker.find_proof_flag_values(donor, ConstraintProofModelData<Cumulative>::active_flag_key(i, t))) {
            // A constant height puts `height x active` in the row, so the one
            // flag is the whole term. A variable one puts the bits of a
            // linearised contribution there instead, and every one of them has
            // to go; how many there are is the donor's business, so ask for bit
            // zero, one, two and so on until it has no more.
            auto bits = 0;
            for (;; ++bits) {
                auto cc = tracker.find_proof_flag_values(donor, ConstraintProofModelData<Cumulative>::contribution_flag_key(i, t, Integer{bits}));
                if (! cc)
                    break;
                weaken_out.push_back(*cc);
            }
            // A constant height puts the whole term on the one flag, so that
            // is what goes. Worth knowing before someone deletes it as
            // untested: no test can catch its absence, because a recipe pins
            // what it returns with an `ia` and dropping a non-negative term
            // from the left of a `<=` is a valid implication --- the pin
            // weakens the term away for free. It is here so that the row a
            // recipe argues over is the row it claims, which is what everything
            // downstream assumes; the variable-height case above is the one
            // that fails loudly without it, its terms not being on a flag any
            // recipe mentions.
            if (0 == bits)
                weaken_out.push_back(*active);
        }
    }

    // And which of the *converted* tasks have one: same question, same answer,
    // and the bits are what the conversion is about rather than what it weakens
    // away. A task the donor gave no window here has nothing to convert.
    vector<pair<size_t, vector<ProofFlag>>> convert;
    for (auto i : view.usable) {
        if (! view.height_bounded_by[i])
            continue;
        vector<ProofFlag> cc;
        for (auto bit = 0;; ++bit) {
            auto flag = tracker.find_proof_flag_values(donor, ConstraintProofModelData<Cumulative>::contribution_flag_key(i, t, Integer{bit}));
            if (! flag)
                break;
            cc.push_back(*flag);
        }
        if (! cc.empty())
            convert.emplace_back(i, move(cc));
    }

    // The all-constant case, which is the common one: the row already says what
    // a recipe needs, so it is handed back untouched and the proof is
    // byte-identical to one written without any of this.
    if (weaken_out.empty() && convert.empty() && ! view.capacity_bounded_by)
        return row;

    PolBuilder reduced;
    reduced.add(row);

    // Convert each variable-height task's bit terms into `lb(h) x active`,
    // which is a coefficient on a flag again and so a term a recipe can argue
    // about. One line each:
    //
    //     Sum_k 2^k cc_k  +  lb(h) ~active  >=  lb(h)
    //
    // added to the row with coefficient one, so the bits cancel exactly and
    // what is left on the task is `lb(h) x active`. It is a RUP rather than a
    // `pol`, and that is not laziness: negating it forces `~active` to zero,
    // and what remains is the `cge` row and the height's lower bound over two
    // power-of-two bit counters, which unit propagation walks down a bit at a
    // time. Every step is single-constraint, so any fixpoint finds it --- I
    // swept it over several thousand (bound, upper bound, bit width) shapes,
    // including contribution bits narrower than the height's, before believing
    // it. The `pol` it replaces would be the `cge` row plus the bound, then a
    // saturate to cap the reification constant down to the bound, then a
    // literal axiom per bit to put the coefficients back.
    for (const auto & [i, cc] : convert) {
        auto height = std::get<SimpleIntegerVariableID>(*view.height_bounded_by[i]);
        auto active = tracker.find_proof_flag_values(donor, ConstraintProofModelData<Cumulative>::active_flag_key(i, t));
        auto contribution_row = tracker.constraint_row_label(donor, ConstraintProofModelData<Cumulative>::contribution_ge_row_role(i, t));
        // The flags exist, so the donor gave this task a window here and both
        // of these went out with them. Missing means the donor is not the
        // Cumulative these keys were published by.
        if (! active || ! contribution_row)
            return nullopt;

        // The bound the height has *now*, by the same route the capacity takes
        // and for the same reason: the declared one is a weaker number the
        // moment anything has tightened it, and a declared zero would give up
        // the conversion altogether. The atom's definition supplies the bits,
        // and the unit saying the atom holds is what makes the row
        // unconditional --- permanently, the bound having been reached before
        // the search started.
        //
        // The fallback below --- the RUP where no pin was written down --- has
        // no fixture, because every in-tree model reaches this bound by the
        // declared one, which need_gevar has already pinned. What makes it
        // sound is that a tightening that got the bound here was *proof
        // logged*: the RUP then closes against the line that logged it. A root
        // tightening of a donor's height taken with NoJustificationNeeded would
        // leave nothing to close against and this would fail at check time, not
        // here --- which is a dependency on the rest of the solver rather than
        // on anything in this file, and so is written down rather than tested.
        auto at_least = height >= view.heights[i];
        auto definition = tracker.need_pol_item_defining_literal(at_least);
        auto holds = tracker.boundary_pin_line(height, view.heights[i]);
        if (! holds)
            holds = logger.emit_rup_proof_line(WPBSum{} + 1_i * at_least >= 1_i, ProofLevel::Temporary);

        // Hints, where the definition came back as a line: they are what makes
        // this cheap to check, and they are exactly the three facts the
        // argument above uses. A zero-one height resolves to a bare literal
        // instead, which a hint list cannot carry --- so that one goes
        // unhinted, which is slower to check and no less true.
        std::optional<vector<ProofLine>> hints;
        if (auto line = std::get_if<ProofLine>(&definition))
            hints = vector<ProofLine>{ProofLine{*contribution_row}, *line, *holds};

        WPBSum guaranteed;
        for (size_t k = 0; k < cc.size(); ++k)
            guaranteed += power2(Integer(static_cast<long long>(k))) * cc[k];
        guaranteed += view.heights[i] * ! *active;
        reduced.add(logger.emit(RUPProofRule{hints}, move(guaranteed) >= view.heights[i], ProofLevel::Temporary));
    }

    if (view.capacity_bounded_by) {
        // How much of the order literal is left once its definition has handed
        // over the bits: the definition says `capacity <= bound` *or* the atom
        // holds, and the atom's coefficient is the rest of what the encoding
        // could have reached. Worked out from the same primitive the encoding
        // itself is built with, over the range the tracker says the variable
        // was encoded over, rather than from anything this file assumes about
        // the shape.
        auto [lo, hi] = tracker.tracked_bounds(std::get<SimpleIntegerVariableID>(*view.capacity_bounded_by));
        auto [shift, highest_bit, negative_bit] = get_bits_encoding_coeffs(lo, hi);
        if (0_i != negative_bit)
            return nullopt; // a signed capacity, which Cumulative rejects anyway
        // Written as two additions rather than as `2 * highest_bit - 1 -
        // capacity`, which is the same number by a route that overflows: a
        // capacity encoded up to bit 62 makes the doubling the first thing that
        // does not fit, where the sum below reaches at most the largest value
        // the encoding can express and so at most what a bit vector holds.
        auto atom_coefficient = (highest_bit - 1_i - view.capacity) + highest_bit;

        // The definition, which is what brings the capacity's bits over to
        // cancel against the row's, and what leaves the atom behind.
        auto capacity_at_most = *view.capacity_bounded_by < view.capacity + 1_i;
        reduced.add_for_literal(tracker, capacity_at_most);

        // And what pays the atom off: the line saying it is false. Where the
        // bound is the capacity's declared one, need_gevar has already pinned
        // that as a persistent top-of-proof line --- the pin exists to be
        // cited, so cite it rather than emit the same unit again per row.
        // Anywhere else the fact is still permanent, the bound having been
        // reached before the search started, but nothing has written it down:
        // a unit RUP does, as working, and so at Temporary whatever level the
        // caller wants the row itself at. Untested for the same reason as the
        // height's fallback above, and resting on the same dependency: the RUP
        // closes because whatever tightened the capacity logged doing so.
        auto capacity_variable = std::get<SimpleIntegerVariableID>(*view.capacity_bounded_by);
        auto atom_is_false = tracker.boundary_pin_line(capacity_variable, view.capacity + 1_i);
        if (! atom_is_false)
            atom_is_false = logger.emit_rup_proof_line(WPBSum{} + 1_i * capacity_at_most >= 1_i, ProofLevel::Temporary);

        if (atom_coefficient > 0_i)
            reduced.add(*atom_is_false, atom_coefficient);
    }

    for (const auto & flag : weaken_out)
        reduced.weaken(flag, tracker);

    return reduced.emit(logger, level);
}
