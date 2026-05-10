#include <gcs/constraints/all_different/encoding.hh>
#include <gcs/innards/inference_tracker.hh>
#include <gcs/innards/proofs/proof_logger.hh>
#include <gcs/innards/proofs/proof_model.hh>
#include <gcs/innards/propagators.hh>

#include <utility>

using std::map;
using std::move;
using std::vector;

using namespace gcs;
using namespace gcs::innards;

auto gcs::innards::define_clique_not_equals_encoding(ProofModel & model, const vector<gcs::IntegerVariableID> & vars) -> map<IntegerVariableID, ProofFlag>
{
    map<IntegerVariableID, ProofFlag> duplicate_selectors;

    for (unsigned i = 0; i < vars.size(); ++i)
        for (unsigned j = i + 1; j < vars.size(); ++j) {
            auto selector = model.create_proof_flag("notequals");
            model.add_constraint("AllDifferent", "not equals because lower", WPBSum{} + 1_i * vars[i] + -1_i * vars[j] <= -1_i, HalfReifyOnConjunctionOf{selector});
            model.add_constraint("AllDifferent", "not equals because higher", WPBSum{} + -1_i * vars[i] + 1_i * vars[j] <= -1_i, HalfReifyOnConjunctionOf{! selector});

            if (vars[i] == vars[j])
                duplicate_selectors.insert_or_assign(vars[i], selector);
        }

    return duplicate_selectors;
}

auto gcs::innards::install_clique_duplicate_contradiction_initialiser(
    Propagators & propagators,
    map<IntegerVariableID, ProofFlag> duplicate_selectors) -> void
{
    propagators.install_initialiser(
        [duplicate_selectors = move(duplicate_selectors)](
            State &, auto & inference, ProofLogger * const logger) -> void {
            if (logger && ! duplicate_selectors.empty()) {
                auto & [_, selector] = *duplicate_selectors.begin();
                inference.contradiction(logger,
                    JustifyExplicitlyThenRUP{
                        [logger, selector](const ReasonFunction &) -> void {
                            // For the duplicated pair (i, j) with vars[i] = vars[j], the encoding
                            // emitted:
                            //   selector  -> (vars[i] - vars[j] <= -1)  i.e.  selector  -> false
                            //   !selector -> (vars[j] - vars[i] <= -1)  i.e.  !selector -> false
                            // RUP each polarity from its own half-reification, then RUP false.
                            logger->emit(RUPProofRule{},
                                WPBSum{} + 1_i * selector >= 1_i, ProofLevel::Temporary);
                            logger->emit(RUPProofRule{},
                                WPBSum{} + 1_i * (! selector) >= 1_i, ProofLevel::Temporary);
                        }},
                    ReasonFunction{});
            }
            else {
                inference.contradiction(logger, JustifyUsingRUP{}, ReasonFunction{});
            }
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
