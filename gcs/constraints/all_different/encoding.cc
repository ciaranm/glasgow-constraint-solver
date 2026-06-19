#include <gcs/constraints/all_different/encoding.hh>
#include <gcs/innards/assertion_hints.hh>
#include <gcs/innards/inference_tracker.hh>
#include <gcs/innards/proofs/proof_logger.hh>
#include <gcs/innards/proofs/proof_model.hh>
#include <gcs/innards/propagators.hh>

using std::map;
using std::string;
using std::to_string;
using std::vector;

using namespace gcs;
using namespace gcs::innards;

auto gcs::innards::define_clique_not_equals_encoding(ProofModel & model, const ConstraintID & constraint_id, const vector<gcs::IntegerVariableID> & vars) -> void
{
    auto id_label = as_string(constraint_id);

    for (unsigned i = 0; i < vars.size(); ++i)
        for (unsigned j = i + 1; j < vars.size(); ++j) {
            // Conform to cake_pb_cp's naming so workflow-2 byte-matches (#354):
            // the pair selector is the position-indexed x[id][i_j] (cake's
            // Indices [i;j] flag), TRUE meaning vars[i] > vars[j] (the "higher"
            // half), with the "lower" half reified on its negation. cake labels
            // the pair the same way: @c[id][<i>lt<j>] is the lower half
            // (vars[i] < vars[j]), @c[id][<i>gt<j>] the higher. The proof never
            // references these selectors by name (the propagator's justifications
            // RUP over the variable literals), so the name/polarity are free to
            // match cake without touching any proof step.
            // Explicit vector (not a braced list): with the scalar b[id][role]
            // overload also present, a braced {i, j} is ambiguous against
            // std::string's (count, char) constructor.
            auto selector = model.create_proof_flag(constraint_id,
                vector<long long>{static_cast<long long>(i), static_cast<long long>(j)});
            model.add_labelled_constraint(id_label, to_string(i) + "lt" + to_string(j),
                "AllDifferent", "not equals because lower", WPBSum{} + 1_i * vars[i] + -1_i * vars[j] <= -1_i, HalfReifyOnConjunctionOf{! selector});
            model.add_labelled_constraint(id_label, to_string(i) + "gt" + to_string(j),
                "AllDifferent", "not equals because higher", WPBSum{} + -1_i * vars[i] + 1_i * vars[j] <= -1_i, HalfReifyOnConjunctionOf{selector});
        }
}

auto gcs::innards::install_clique_duplicate_contradiction_initialiser(
    Propagators & propagators) -> void
{
    propagators.install_initialiser(
        [](
            State &, auto & inference, ProofLogger * const logger) -> void {
            inference.contradiction(logger, JustifyUsingRUP{}, ReasonFunction{});
        },
        InitialiserPriority::SimpleDefinition);
}

auto gcs::innards::define_clique_not_equals_except_encoding(ProofModel & model,
    const vector<gcs::IntegerVariableID> & vars,
    const vector<gcs::Integer> & excluded) -> map<IntegerVariableID, ProofFlag>
{
    map<IntegerVariableID, ProofFlag> duplicate_selectors;

    for (unsigned i = 0; i < vars.size(); ++i)
        for (unsigned j = i + 1; j < vars.size(); ++j) {
            auto selector = model.create_proof_flag("notequals_except");
            HalfReifyOnConjunctionOf lower_conj{selector};
            HalfReifyOnConjunctionOf higher_conj{! selector};
            for (const auto & s : excluded) {
                lower_conj.emplace_back(vars[i] != s);
                lower_conj.emplace_back(vars[j] != s);
                higher_conj.emplace_back(vars[i] != s);
                higher_conj.emplace_back(vars[j] != s);
            }
            model.add_constraint("AllDifferentExcept", "not equals because lower",
                WPBSum{} + 1_i * vars[i] + -1_i * vars[j] <= -1_i, lower_conj);
            model.add_constraint("AllDifferentExcept", "not equals because higher",
                WPBSum{} + -1_i * vars[i] + 1_i * vars[j] <= -1_i, higher_conj);

            if (vars[i] == vars[j])
                duplicate_selectors.insert_or_assign(vars[i], selector);
        }

    return duplicate_selectors;
}
