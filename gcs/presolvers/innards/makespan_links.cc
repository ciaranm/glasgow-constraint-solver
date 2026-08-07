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

    return links;
}
