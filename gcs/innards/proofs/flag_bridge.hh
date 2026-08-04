#ifndef GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_INNARDS_PROOFS_FLAG_BRIDGE_HH
#define GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_INNARDS_PROOFS_FLAG_BRIDGE_HH

#include <gcs/innards/proofs/proof_line.hh>
#include <gcs/innards/proofs/proof_logger-fwd.hh>
#include <gcs/innards/proofs/proof_only_variables.hh>

#include <vector>

namespace gcs::innards
{
    /**
     * \brief Derive `from -> to`, as the line `~from + to >= 1`, for two flags
     * fully reified on inequalities over the same terms.
     *
     * One `pol`, and it is worth seeing why it is only one. A fully reified flag
     * emits `g -> ineq` under `[r]` and `ineq -> g` under `[f]`. Adding `from`'s
     * `[r]` to `to`'s `[f]` puts the two inequalities in with opposite signs, so
     * their terms cancel --- including all the bits of any integer variable they
     * mention --- and what is left after saturation is the two-literal clause.
     * No order literals, no bit reasoning, no dependence on what the conditions
     * actually say.
     *
     * What it does depend on is the terms cancelling and the constants leaving
     * something behind: for `from <-> (e <= p)` and `to <-> (e <= q)` over the
     * same expression `e`, the sum has degree `q - p + 1`, so the derivation
     * goes through exactly when `q >= p` --- which is exactly when the
     * implication is true. Identical conditions are the case this exists for,
     * and give a degree of one; a `to` whose condition is strictly weaker also
     * works, and a stronger one correctly does not.
     *
     * There is no way for this to derive something false, since every step is a
     * `pol`. What a caller has to check is that the line it got back says what
     * it wanted --- pin it, as everything else in this directory does.
     *
     * This is what lets one constraint's proof speak about another's flags ---
     * the multi-donor bridging sketched in the derived-Cumulative writeup, and
     * what an inferred constraint over tasks drawn from several resources needs
     * before it can say anything about them at all.
     *
     * \ingroup Innards
     */
    [[nodiscard]] auto derive_flag_bridge(ProofLogger &, const ProofFlag & from, const ProofFlag & to, ProofLevel) -> ProofLine;

    /**
     * \brief As derive_flag_bridge, for two flags each fully reified
     * as the *conjunction* of some other flags: derive `from -> to`, given that
     * the conjuncts correspond in order and each corresponding pair is reified
     * on the same inequality.
     *
     * The conjuncts cannot be bridged by the one-`pol` trick directly, because
     * `from` and `to` are reified on conditions that mention *different* flags
     * and so do not cancel. What does work is bridging each conjunct --- those
     * do reify the same inequality --- and then adding `from`'s `[r]` half, the
     * conjunct bridges, and `to`'s `[f]` half: each conjunct then appears with
     * both signs and drops out, leaving `~from + to` after saturation.
     *
     * This is `Cumulative`'s `active <-> before /\ after` exactly, which is what
     * it exists for.
     *
     * \ingroup Innards
     */
    [[nodiscard]] auto derive_conjunction_flag_bridge(ProofLogger &, const ProofFlag & from, const std::vector<ProofFlag> & from_conjuncts,
        const ProofFlag & to, const std::vector<ProofFlag> & to_conjuncts, ProofLevel) -> ProofLine;
}

#endif
