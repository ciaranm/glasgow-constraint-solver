#ifndef GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_INNARDS_PROOFS_FLAG_BRIDGE_HH
#define GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_INNARDS_PROOFS_FLAG_BRIDGE_HH

#include <gcs/innards/proofs/proof_line.hh>
#include <gcs/innards/proofs/proof_logger-fwd.hh>
#include <gcs/innards/proofs/proof_only_variables.hh>
#include <gcs/integer.hh>

#include <optional>
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
    [[nodiscard]] auto recover_flag_bridge(ProofLogger &, const ProofFlag & from, const ProofFlag & to, ProofLevel) -> ProofLine;

    /**
     * \brief As recover_flag_bridge, for two flags each fully reified
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
    [[nodiscard]] auto recover_conjunction_flag_bridge(ProofLogger &, const ProofFlag & from, const std::vector<ProofFlag> & from_conjuncts,
        const ProofFlag & to, const std::vector<ProofFlag> & to_conjuncts, ProofLevel) -> ProofLine;

    /**
     * \brief One term of a row being carried onto other flags: its coefficient,
     * the flag it is to end up over, and the bridge saying that flag implies the
     * one the row actually mentions.
     *
     * The bridge points that way round and not the other, which is worth being
     * clear about because both directions exist and only one is sound here. To
     * turn `sum c_j b_j <= C` into `sum c_j a_j <= C` the sum has to be able to
     * grow, so each `a_j` has to imply its `b_j`: a point where the new flag
     * holds is one where the old one did, and so one the row already spoke
     * about. Bridging the other way would say the row constrains points it never
     * saw.
     *
     * There is nothing to carry when a term is already over the flag wanted,
     * which is the usual case for whichever constraint the row belongs to, so
     * the bridge is optional and a term without one is left where it is.
     *
     * \ingroup Innards
     */
    struct BridgedRowTerm
    {
        Integer coefficient;
        ProofFlag flag;
        std::optional<ProofLine> implies_row_flag;
    };

    /**
     * \brief Recover a capacity row over another constraint's flags: the same
     * inequality, said in flags that mean the same thing.
     *
     * A row belonging to one Cumulative mentions that constraint's own activity
     * flags, and a derivation combining rows from several of them --- a cut
     * lifted over more than one resource, which is what Sidorov's Equation 4
     * produces --- needs them all over one set. This is what makes that
     * possible, and it is one `pol`: weaken the row down to the terms wanted,
     * then add `c_j` copies of each term's bridge, which puts each flag in with
     * both signs so that all of them cancel and the constants leave the same
     * right-hand side behind.
     *
     * `weaken_out` names the row's other terms, and is for shape rather than for
     * soundness: a term left in survives into the `pol` with its own flag, which
     * the pin below then drops again, so what a caller gets is the same row
     * either way and only the working is wider. Passing a flag the row does not
     * mention is what `w` rejects, so a wrong list is an error rather than a
     * silent weakening.
     *
     * The result is pinned with an `ia` against the row asked for, so what comes
     * back is literal-exact whatever shape the `pol` landed on --- and a bridge
     * pointing the wrong way, or a coefficient that does not match the row's, is
     * refused here rather than several thousand lines later.
     *
     * \ingroup Innards
     */
    [[nodiscard]] auto recover_bridged_row(ProofLogger &, ProofLine row, const std::vector<BridgedRowTerm> & terms,
        const std::vector<ProofFlag> & weaken_out, Integer capacity, ProofLevel) -> ProofLine;
}

#endif
