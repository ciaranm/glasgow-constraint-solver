#include <gcs/constraints/innards/recover_am1.hh>
#include <gcs/exception.hh>
#include <gcs/innards/proofs/names_and_ids_tracker.hh>
#include <gcs/innards/proofs/pol_builder.hh>
#include <gcs/innards/proofs/simplify_literal.hh>

#include <gcs/proof.hh>
#include <util/enumerate.hh>
#include <util/overloaded.hh>

#include <optional>
#include <sstream>
#include <type_traits>
#include <utility>
#include <variant>

using namespace gcs;
using namespace gcs::innards;

using std::function;
using std::holds_alternative;
using std::is_same_v;
using std::nullopt;
using std::optional;
using std::pair;
using std::vector;

template <typename Literal_>
[[nodiscard]] auto gcs::innards::recover_am1(ProofLogger & logger, ProofLevel level, const vector<Literal_> & atoms,
    const function<auto(const Literal_ &, const Literal_ &)->ProofLine> & pair_ne) -> ProofLine
{
    if (logger.get_assertion_level() > AssertionLevel::Off)
        return ProofLine{};

    if (atoms.size() < 2)
        // An at-most-one over fewer than two atoms is vacuous; the caller should
        // handle it directly rather than ask the helper to fold zero pairwise
        // lines into a pol. Needing at least two atoms is part of the helper's
        // API, not something we expect to relax, so this is unexpected rather
        // than unimplemented.
        throw UnexpectedException{"recover_am1 needs at least two atoms"};

    if constexpr (is_same_v<Literal_, IntegerVariableCondition>) {
        // If ≥2 atoms simplify to FalseLiteral (e.g. literals over constants
        // that don't satisfy the condition), the AM1 they're meant to
        // capture is genuinely violated by the input: literal-as-PB gives
        // ≥2 of them as 0, so Σ atoms ≥ n - 1 fails. Folding pair_ne lines
        // via the usual pol expression doesn't recover a valid line —
        // pair_ne over two false atoms emits a direct `0 ≥ 1` contradiction,
        // and the pol summation embeds it in a malformed expression that
        // VeriPB rejects at parse. Short-circuit: emit a `0 ≥ 1`
        // contradiction at the caller-supplied level directly (RUP-derivable
        // because the OPB has unit clauses forcing the same variable to
        // multiple values) and return that as the "AM1" line. Downstream
        // consumers fold this into further pol expressions to derive a
        // stronger contradiction — the correct outcome, since the input is
        // infeasible. Issue #171.
        unsigned n_false = 0;
        for (const auto & atom : atoms) {
            if (holds_alternative<FalseLiteral>(simplify_literal(logger.names_and_ids_tracker(), atom))) {
                if (++n_false >= 2)
                    return logger.emit(RUPProofRule{}, WPBSum{} >= 1_i, level);
            }
        }
    }

    // Detect a complementary literal pair among the atoms: two atoms that are the
    // same underlying proof literal with opposite polarity. This arises when a
    // bit-aliased two-value variable contributes two of the atoms -- e.g. a
    // {0,1}-domain variable whose (== 1)/(== 0) atoms *are* the single bit b0 /
    // ~b0, so an at-most-one over {var == 0, var == 1, ...} contains {~b0, b0}.
    // The generic pairwise->global fold below is not tight in that case: the
    // tautological pair line (b0 + ~b0 >= 1) normalises to a constant
    // mid-derivation, and the ceiling-division renormalisation then discards a
    // unit, yielding a loose at-most-one that leaves a residual literal in any pol
    // that sums it (issue #557; a sibling of the #554 gevar-aliasing bug). Only
    // GlobalCardinality passes several value-conditions on the *same* variable, so
    // it is the only caller that can hit this; every other caller passes
    // conditions over distinct variables, finds no pair, and takes the generic
    // path with byte-identical output. A "not found" lookup means the literal is
    // unaliased/fresh and so cannot be half of a pair, which is the safe default.
    auto atom_xliteral = [&](const Literal_ & atom) -> optional<XLiteral> {
        if constexpr (is_same_v<Literal_, ProofFlag>)
            return logger.names_and_ids_tracker().find_xliteral_for(atom);
        else
            return overloaded{//
                [](const TrueLiteral &) -> optional<XLiteral> { return nullopt; }, [](const FalseLiteral &) -> optional<XLiteral> { return nullopt; },
                [&](const auto & cond) -> optional<XLiteral> { return logger.names_and_ids_tracker().find_xliteral_for(cond); }}
                .visit(simplify_literal(logger.names_and_ids_tracker(), atom));
    };

    optional<pair<unsigned, unsigned>> complementary_pair;
    {
        vector<optional<XLiteral>> xs;
        xs.reserve(atoms.size());
        for (const auto & atom : atoms)
            xs.push_back(atom_xliteral(atom));
        for (unsigned i = 0; i < atoms.size() && ! complementary_pair; ++i)
            if (xs[i])
                for (unsigned j = i + 1; j < atoms.size(); ++j)
                    if (xs[j] && *xs[i] == ! *xs[j]) {
                        complementary_pair = pair<unsigned, unsigned>{i, j};
                        break;
                    }
    }

    // pair_ne callbacks typically emit intermediate proof lines at Temporary
    // level. Without isolation, those lines would share the caller's
    // Temporary depth (active_proof_level + 1) — and our cleanup at that
    // depth would wipe out the caller's scope along with our own
    // intermediates. (Concrete failure mode: when the caller is itself
    // inside a JustifyExplicitly{…, ThenRUP::Yes}, which uses depth active+1 for its
    // callback's Temporary lines, a naive forget at that same depth from
    // inside recover_am1 deletes the framework's just-emitted lines
    // mid-justification.)
    //
    // To isolate, we increase active_proof_level by one before emitting
    // pair_ne lines. They then record at the new active+1, one deeper
    // than the caller's Temporary depth, and forgetting that deeper depth
    // on exit cleans up only our own intermediates.
    //
    // The result itself is emitted *after* restoring the caller's level, so
    // it records at the level the caller asked for: Top callers (in
    // initialisers, caching the line for reuse) get depth 0 as before;
    // Temporary callers (e.g. inside a JustifyExplicitly{…, ThenRUP::Yes} that folds
    // the result into a further pol) get the caller's Temporary depth, so
    // the line survives our own deeper cleanup and is reclaimed when the
    // caller's scope is forgotten.
    auto saved_level = logger.proof_level();
    logger.enter_proof_level(saved_level + 1);

    // Build the at-most-one via PolBuilder rather than a hand-written pol
    // string: PolBuilder defers stringifying the pair_ne line references to
    // emit time and renders them as *relative* (negative) indices. A literal
    // stringstream would bake in absolute line numbers, which break under
    // workflow-2 when cake_pb_cp re-derives the OPB with a different constraint
    // count.
    PolBuilder am1;
    if (complementary_pair && atoms.size() >= 3) {
        // Block scheme for the degenerate complementary-pair case (issue #557).
        // With a pair (p, q) where atoms[q] == !atoms[p], every other atom a_k is
        // forced false: pair_ne(a_k, a_p) + pair_ne(a_k, a_q) = 2 ~a_k + (~a_p +
        // ~a_q), and because the pair is complementary the bracket folds to the
        // constant 1, so dividing by 2 gives exactly ~a_k >= 1. Accumulating each
        // further other atom the same way (multiply the running sum by 2, add its
        // two pair lines, divide by 2) keeps every coefficient at exactly the
        // divisor and never rounds a unit away -- the property the generic fold
        // loses. The result is the tight Sum_{k != p, q} ~a_k >= n - 2, which is
        // the PB-normal form of the global at-most-one Sum ~a >= n - 1 (the pair
        // itself contributes the folded-away +1). With n >= 3 there is at least
        // one other atom, so the builder is never empty. (n == 2 with a pair is
        // left to the generic fold below, which already yields the correct trivial
        // 0 >= 0.) Two or more pairs -- unreachable from in-tree callers -- still
        // come out exactly, as the infeasible-strength 0 >= 1.
        auto [p, q] = *complementary_pair;
        bool first = true;
        for (unsigned k = 0; k < atoms.size(); ++k) {
            if (k == p || k == q)
                continue;
            if (! first)
                am1.multiply_by(2_i);
            am1.add(pair_ne(atoms[k], atoms[p]));
            am1.add(pair_ne(atoms[k], atoms[q]));
            am1.divide_by(2_i);
            first = false;
        }
    }
    else {
        for (unsigned i1 = 1; i1 < atoms.size(); ++i1) {
            if (i1 != 1)
                am1.multiply_by(Integer{static_cast<long long>(i1 + 1)});
            for (unsigned i2 = 0; i2 < i1; ++i2)
                am1.add(pair_ne(atoms[i1], atoms[i2]));
            am1.divide_by(Integer{static_cast<long long>(i1 + 2)});
        }
    }

    // Restore the caller's level, then emit the result there (its level is
    // resolved at emit time) while the pair_ne lines are still alive — VeriPB
    // resolves the line-number references during this emit. Finally forget the
    // inner scope, which removes only our deeper pair_ne intermediates and
    // leaves the result (at the caller's level) intact.
    logger.enter_proof_level(saved_level);
    auto result = am1.emit(logger, level);
    logger.forget_proof_level(saved_level + 2);
    return result;
}

template auto gcs::innards::recover_am1<IntegerVariableCondition>(ProofLogger &, ProofLevel, const vector<IntegerVariableCondition> &,
    const function<auto(const IntegerVariableCondition &, const IntegerVariableCondition &)->ProofLine> &) -> ProofLine;

template auto gcs::innards::recover_am1<ProofFlag>(
    ProofLogger &, ProofLevel, const vector<ProofFlag> &, const function<auto(const ProofFlag &, const ProofFlag &)->ProofLine> &) -> ProofLine;
