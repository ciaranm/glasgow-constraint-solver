#include <gcs/constraints/all_different/encoding.hh>
#include <gcs/innards/inference_tracker.hh>
#include <gcs/innards/proofs/proof_logger.hh>
#include <gcs/innards/proofs/proof_model.hh>
#include <gcs/innards/propagators.hh>

#include <utility>

using std::map;
using std::move;
using std::optional;
using std::pair;
using std::vector;

using namespace gcs;
using namespace gcs::innards;

// OPB-ENCODING-BEGIN: all_different
//   s-expr:  all_different (x_0, x_1, ..., x_{n-1})
//   Clauses (for each pair (i, j) with 0 <= i < j < n):
//     ("AllDifferent", "not equals because lower")
//         1*x_i + -1*x_j <= -1         half-reified on { notequals_{i,j} }
//     ("AllDifferent", "not equals because higher")
//         -1*x_i + 1*x_j <= -1         half-reified on { !notequals_{i,j} }
//   Bounds:                 (none)
//   CP literals referenced: (none)
//   Auxiliary PB flags introduced (one per pair):
//     notequals_{i,j} -- fresh PB variable; case-split guard for
//                        x_i != x_j. Source allocates each as
//                        create_proof_flag("notequals"); a per-pair
//                        distinguishing protocol is TBD.
//   Notes:
//     Standard pairwise disequality clique. Each pair gets its own fresh
//     "notequals" flag and the same two-clause case-split used by the
//     scalar `not_equals` encoding: notequals_{i,j} forces x_i < x_j,
//     its negation forces x_i > x_j, together excluding x_i = x_j.
// OPB-ENCODING-END
auto gcs::innards::define_clique_not_equals_encoding(ProofModel & model, const vector<gcs::IntegerVariableID> & vars) -> optional<pair<IntegerVariableID, ProofFlag>>
{
    optional<pair<IntegerVariableID, ProofFlag>> duplicate_witness;

    for (unsigned i = 0; i < vars.size(); ++i)
        for (unsigned j = i + 1; j < vars.size(); ++j) {
            auto selector = model.create_proof_flag("notequals");
            model.add_constraint("AllDifferent", "not equals because lower", WPBSum{} + 1_i * vars[i] + -1_i * vars[j] <= -1_i, HalfReifyOnConjunctionOf{selector});
            model.add_constraint("AllDifferent", "not equals because higher", WPBSum{} + -1_i * vars[i] + 1_i * vars[j] <= -1_i, HalfReifyOnConjunctionOf{! selector});

            if (vars[i] == vars[j] && ! duplicate_witness)
                duplicate_witness = pair{vars[i], selector};
        }

    return duplicate_witness;
}

auto gcs::innards::install_clique_duplicate_contradiction_initialiser(
    Propagators & propagators,
    optional<pair<IntegerVariableID, ProofFlag>> duplicate_witness) -> void
{
    propagators.install_initialiser(
        [duplicate_witness = move(duplicate_witness)](
            State &, auto & inference, ProofLogger * const logger) -> void {
            if (logger && duplicate_witness) {
                const auto & selector = duplicate_witness->second;
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
