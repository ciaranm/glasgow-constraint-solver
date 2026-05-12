#include <gcs/constraints/innards/recover_am1.hh>
#include <gcs/exception.hh>
#include <gcs/innards/proofs/simplify_literal.hh>

#include <util/enumerate.hh>

#include <sstream>
#include <type_traits>
#include <variant>

using namespace gcs;
using namespace gcs::innards;

using std::function;
using std::holds_alternative;
using std::is_same_v;
using std::stringstream;
using std::vector;

template <typename Literal_>
[[nodiscard]] auto gcs::innards::recover_am1(
    ProofLogger & logger,
    ProofLevel level,
    const vector<Literal_> & atoms,
    const function<auto(const Literal_ &, const Literal_ &)->ProofLine> & pair_ne) -> ProofLine
{
    if (atoms.size() < 2)
        throw UnexpectedException{"recover_am1 requires at least 2 atoms"};

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
            if (holds_alternative<FalseLiteral>(simplify_literal(atom))) {
                if (++n_false >= 2)
                    return logger.emit(RUPProofRule{}, WPBSum{} >= 1_i, level);
            }
        }
    }

    // pair_ne callbacks typically emit intermediate proof lines at Temporary
    // level. When the caller wants the result at Top, we push an inner
    // temporary scope so those intermediates are cleaned up on return,
    // leaving only the result line. When the caller wants the result at
    // Temporary or Current, pushing an inner scope would also delete the
    // result line on forget — so in that case we skip the inner scope and
    // let the intermediates share the caller's scope (they'll be cleaned
    // up together when the caller's scope ends).
    bool use_inner_scope = (level == ProofLevel::Top);
    int inner_scope = 0;
    if (use_inner_scope)
        inner_scope = logger.temporary_proof_level();

    stringstream am1;
    for (unsigned i1 = 1; i1 < atoms.size(); ++i1) {
        vector<ProofLine> lines;
        for (unsigned i2 = 0; i2 < i1; ++i2)
            lines.push_back(pair_ne(atoms[i1], atoms[i2]));

        if (i1 == 1)
            am1 << "pol";
        else
            am1 << " " << (i1 + 1) << " *";

        for (const auto & [n, line] : enumerate(lines)) {
            am1 << " " << line;
            if (n != 0 || i1 != 1)
                am1 << " +";
        }

        am1 << " " << (i1 + 2) << " d";
    }
    am1 << ';';
    auto result = logger.emit_proof_line(am1.str(), level);

    if (use_inner_scope)
        logger.forget_proof_level(inner_scope);

    return result;
}

template auto gcs::innards::recover_am1<IntegerVariableCondition>(
    ProofLogger &, ProofLevel, const vector<IntegerVariableCondition> &, const function<auto(const IntegerVariableCondition &, const IntegerVariableCondition &)->ProofLine> &) -> ProofLine;

template auto gcs::innards::recover_am1<ProofFlag>(
    ProofLogger &, ProofLevel, const vector<ProofFlag> &, const function<auto(const ProofFlag &, const ProofFlag &)->ProofLine> &) -> ProofLine;
