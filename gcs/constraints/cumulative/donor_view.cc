#include <gcs/constraints/cumulative/donor_view.hh>
#include <gcs/constraints/cumulative/propagate.hh>
#include <gcs/innards/proofs/bits_encoding.hh>
#include <gcs/innards/proofs/names_and_ids_tracker.hh>
#include <gcs/innards/proofs/pol_builder.hh>
#include <gcs/innards/proofs/proof_logger.hh>
#include <gcs/innards/proofs/pseudo_boolean.hh>
#include <gcs/innards/state.hh>

#include <optional>
#include <variant>
#include <vector>

using namespace gcs;
using namespace gcs::innards;

namespace
{
    auto const_value_of(const IntegerVariableID & v) -> Integer
    {
        return std::get<ConstantIntegerVariableID>(v).const_value;
    }
}

using std::make_optional;
using std::nullopt;
using std::optional;
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
        view.capacity = const_value_of(donor.capacity());
    else {
        view.capacity = state.upper_bound(donor.capacity());
        view.capacity_bounded_by = donor.capacity();
    }

    view.lengths.assign(n, constant_variable(0_i));
    view.heights.assign(n, 0_i);
    view.presences = donor.presences();

    for (size_t i = 0; i < n; ++i) {
        auto length = donor.lengths()[i], height = donor.heights()[i];

        // A variable height is what a set-aside is for: it makes the donor's
        // row terms the bits of a linearised contribution rather than
        // `height x active`, so a subset sum of the heights is not a subset sum
        // of the row's coefficients, and nothing a recipe does to that row is
        // an argument about this task.
        if (! is_constant_variable(height)) {
            view.set_aside.push_back(i);
            continue;
        }

        // A task that can never load the resource, or that was posted as
        // constantly absent, has no flags and no term in any row: nothing to
        // set aside, because there is nothing there. Asked before the length
        // test below, and that is not an ordering nicety: the donor gave such a
        // task no window, so it published no end proxy for it either, and
        // asking would come back with the same nullopt a genuinely unusable
        // duration does. The largest duration still allowed is what says
        // whether it can run at all, and is the same bound the donor windowed
        // its flags with.
        auto presence = cumulative_task_presence(view.presences.empty() ? nullopt : make_optional(view.presences[i]));
        if (state.upper_bound(length) <= 0_i || const_value_of(height) <= 0_i || presence.never_present)
            continue;

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
            view.set_aside.push_back(i);
            continue;
        }

        view.lengths[i] = length;
        view.heights[i] = const_value_of(height);
        view.usable.push_back(i);
    }

    return view;
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

    // The all-constant case, which is the common one: the row already says what
    // a recipe needs, so it is handed back untouched and the proof is
    // byte-identical to one written without any of this.
    if (weaken_out.empty() && ! view.capacity_bounded_by)
        return row;

    PolBuilder reduced;
    reduced.add(row);

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
        auto atom_coefficient = 2_i * highest_bit - 1_i - view.capacity;

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
        // caller wants the row itself at.
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
