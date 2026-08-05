#include <gcs/innards/proofs/am1_from_pairs.hh>
#include <gcs/innards/proofs/pol_builder.hh>
#include <gcs/innards/proofs/proof_error.hh>
#include <gcs/innards/proofs/proof_logger.hh>
#include <gcs/innards/proofs/pseudo_boolean.hh>

#include <cstddef>
#include <string>
#include <utility>
#include <variant>
#include <vector>

using namespace gcs;
using namespace gcs::innards;

using std::move;
using std::size_t;
using std::to_string;
using std::vector;

auto gcs::innards::recover_am1_from_pairs(ProofLogger & logger, const vector<ProofLiteralOrFlag> & members,
    const vector<vector<ProofLine>> & at_most_ones, ProofLevel level, Am1FromPairsMutation mutation) -> ProofLine
{
    auto k = members.size();
    if (k < 2)
        throw ProofError{"a clique needs at least two members, not " + to_string(k)};
    if (at_most_ones.size() != k)
        throw ProofError{"clique derivation: " + to_string(k) + " members but " + to_string(at_most_ones.size()) + " rows of at-most-ones"};
    for (size_t j = 0; j < k; ++j)
        if (at_most_ones[j].size() != j)
            throw ProofError{"clique derivation: member " + to_string(j) + " has " + to_string(at_most_ones[j].size()) +
                " at-most-ones, needing one per earlier member (" + to_string(j) + ")"};

    auto drop_one = std::holds_alternative<am1_from_pairs_mutation::DropAnAtMostOne>(mutation);
    auto claim_one_more = std::holds_alternative<am1_from_pairs_mutation::ClaimOneMore>(mutation);
    auto skip_final_division = std::holds_alternative<am1_from_pairs_mutation::SkipFinalDivision>(mutation);
    if ((drop_one || skip_final_division) && k < 3)
        throw ProofError{"clique derivation: this mutation needs a merge to corrupt, so at least three members"};

    logger.emit_proof_comment("clique at-most-one over " + to_string(k) + " members");

    // The induction goes one proof level deeper than the caller's own, and is
    // forgotten on the way out. Only the pin below is ever cited again: every
    // line between here and it exists to reach it, and at Top every one of them
    // would stay live for the rest of the proof, taxing every later unhinted RUP
    // (issue #666). The extra depth rather than plain Temporary is what stops
    // the forget taking the caller's scope with it, since a caller inside a
    // JustifyExplicitly is already using its own Temporary depth.
    auto saved_level = logger.proof_level();
    logger.enter_proof_level(saved_level + 1);

    // The base case is not a derivation: the at-most-one for the first pair
    // already is the clique inequality for those two.
    auto current = at_most_ones[1][0];

    if (std::holds_alternative<am1_from_pairs_mutation::NaiveOneShot>(mutation)) {
        // Everything at once. Each member appears in `k - 1` pairs, so this
        // sums to `(k-1) * sum ~a_p >= k(k-1)/2`, and the division lands on
        // `ceil(k/2)` --- the answer for two and three members, and short of
        // `k - 1` for every larger clique.
        PolBuilder naive;
        for (size_t j = 1; j < k; ++j)
            for (size_t i = 0; i < j; ++i)
                naive.add(at_most_ones[j][i]);
        if (k > 2)
            naive.divide_by(Integer{static_cast<long long>(k) - 1});
        current = naive.emit(logger, ProofLevel::Temporary);
    }

    // Then one member at a time. At the top of each pass `current` says
    // `sum_{i<m} ~a_i >= m - 1` over the first `m`, and the pass extends it to
    // `m + 1`.
    for (size_t m = 2; ! std::holds_alternative<am1_from_pairs_mutation::NaiveOneShot>(mutation) && m < k; ++m) {
        PolBuilder merge;

        // The `m` at-most-ones tying the new member to the ones already in.
        // Summed, they say `m*~a_m + sum_{i<m} ~a_i >= m`, which on its own is
        // far too weak --- it permits every earlier member being active.
        // Dropped from the *first* merge rather than the last, so that the
        // resulting weakness has every later pass to propagate through: if
        // anything downstream were quietly repairing it, this is the version
        // that would show it.
        for (size_t i = 0; i < m; ++i) {
            if (drop_one && m == 2 && i == 0)
                continue;
            merge.add(at_most_ones[m][i]);
        }

        // What fixes that is `m - 1` copies of the clique so far, which
        // contributes `(m-1)^2` to the degree while raising the earlier
        // members' coefficients to `m`, matching the new member's.
        merge.add(current, Integer{static_cast<long long>(m) - 1});

        // `m + (m-1)^2 = m(m-1) + 1`, so the division rounds the degree up to
        // exactly `m`. One short of that and it would round down to `m - 1`
        // and the induction would not advance.
        if (! (skip_final_division && m == k - 1))
            merge.divide_by(Integer{static_cast<long long>(m)});
        current = merge.emit(logger, ProofLevel::Temporary);
    }

    // Pin what came back. Every step above is sound whatever was fed into it,
    // so a merge that lost an input, or was scaled wrongly, lands on a weaker
    // line and the proof sails on --- this is the step that says the line is
    // the one that was asked for. Syntactic, so a weaker line does not pass.
    WPBSum clique;
    for (const auto & member : members)
        add_term_to(clique, 1_i, member);

    // Back at the caller's level to pin, while the induction is still alive for
    // VeriPB to resolve the reference against, and only then drop it.
    logger.enter_proof_level(saved_level);
    auto result = logger.emit(ImpliesProofRule{current}, move(clique) <= (claim_one_more ? 0_i : 1_i), level);
    logger.forget_proof_level(saved_level + 2);
    return result;
}
