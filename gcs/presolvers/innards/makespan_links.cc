#include <gcs/constraints/comparison.hh>
#include <gcs/constraints/difference/difference_graph.hh>
#include <gcs/constraints/linear.hh>
#include <gcs/presolvers/innards/makespan_links.hh>
#include <gcs/problem.hh>

#include <optional>
#include <variant>

using namespace gcs;
using namespace gcs::innards;

using std::map;
using std::optional;

auto gcs::innards::find_makespan_links(const Problem & problem, const ProofLogger * const logger, IntegerVariableID makespan)
    -> map<IntegerVariableID, makespan_energy::MakespanLink>
{
    map<IntegerVariableID, makespan_energy::MakespanLink> links;

    for (const auto & [c, label] : problem.each_constraint_of_type_with_proof_data<ReifiedLinearInequality>(logger)) {
        // A conditional row says nothing unless its condition holds, and its
        // condition is not in the reason an energy argument gives.
        if (! std::holds_alternative<reif::MustHold>(c.reification_condition()))
            continue;

        // The row is stored as `sum <= value`, so `makespan - start >= bound`
        // arrives as `start - makespan <= -bound`.
        const auto & terms = c.coefficients_and_variables().terms;
        if (2 != terms.size())
            continue;

        optional<IntegerVariableID> start, limit;
        for (const auto & t : terms) {
            if (1_i == t.coefficient && ! start)
                start = t.variable;
            else if (-1_i == t.coefficient && ! limit)
                limit = t.variable;
        }
        // Aliasing says `0 >= bound`, which is a fact about the model and not
        // about any task.
        if (! start || ! limit || *limit != makespan || *start == makespan)
            continue;

        // A plain variable on the task's side: the `pol` cancels this row's
        // bits against the start's own order-literal definitions, and a view's
        // are not those.
        if (! std::holds_alternative<SimpleIntegerVariableID>(*start))
            continue;

        auto bound = -c.value();
        if (bound <= 0_i)
            continue;

        // With proofs on, a row nothing can cite is a row this cannot use: the
        // derivation would name a label the `.opb` does not contain.
        if (logger && ! label)
            continue;

        auto existing = links.find(*start);
        if (existing == links.end())
            links.emplace(*start, makespan_energy::MakespanLink{bound, label});
        else if (bound > existing->second.bound)
            existing->second = makespan_energy::MakespanLink{bound, label};
    }

    // The comparison family says the same thing over an offset view: a model
    // written `start + length <= makespan`, and the `start <= makespan - length`
    // the FlatZinc reader recovers from a two-term int_lin_le. A view has its own
    // BinEnc in the proof, so neither row is stated in the underlying variables'
    // bits --- but makespan_energy cites the link's row in *deview mode*, which
    // substitutes each BinEnc(V) term through the view's link axiom before the
    // cancellation, so both spellings resolve against the start's and the
    // makespan's own order-literal definitions exactly as the linear form's row
    // does. That is the same trick the difference-logic propagator uses on its
    // donors. A *negated* view is still not this shape at all --- `-start + c <=
    // makespan` bounds the wrong side --- and deview_difference_operand rejects
    // those for us.
    for (const auto & [c, label] : problem.each_constraint_of_type_with_proof_data<ReifiedCompareLessThanOrMaybeEqual>(logger)) {
        if (! std::holds_alternative<reif::MustHold>(c.reification_condition()))
            continue;

        auto left = deview_difference_operand(c.left_variable());
        auto right = deview_difference_operand(c.right_variable());
        if (! left || ! right || ! left->variable || ! right->variable)
            continue;

        // The makespan on the right, and not on both: aliasing states `0 >= bound`,
        // which is a fact about the model rather than about any task, and is the
        // degenerate case the linear branch above declines for the same reason.
        if (IntegerVariableID{*right->variable} != makespan || IntegerVariableID{*left->variable} == makespan)
            continue;

        // `left <= right` states `left - right <= 0`, and the strict spelling `<=
        // -1`. With left = start + cl and right = makespan + cr that is `start -
        // makespan <= (or_equal ? 0 : -1) - cl + cr`, so the length the energy
        // argument wants out of `makespan - start >= length` is its negation.
        auto bound = left->offset - right->offset + (c.or_equal() ? 0_i : 1_i);
        if (bound <= 0_i)
            continue;

        if (logger && ! label)
            continue;

        auto start = IntegerVariableID{*left->variable};
        auto existing = links.find(start);
        if (existing == links.end())
            links.emplace(start, makespan_energy::MakespanLink{bound, label});
        else if (bound > existing->second.bound)
            existing->second = makespan_energy::MakespanLink{bound, label};
    }

    return links;
}
