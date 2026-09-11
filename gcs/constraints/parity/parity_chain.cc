#include <gcs/constraints/parity/parity_chain.hh>
#include <gcs/innards/proofs/proof_line.hh>
#include <gcs/innards/proofs/proof_model.hh>
#include <util/enumerate.hh>

#include <string>
#include <vector>

using namespace gcs;
using namespace gcs::innards;

using std::nullopt;
using std::optional;
using std::string;
using std::to_string;
using std::vector;

auto gcs::innards::define_parity_chain(ProofModel & model, const ConstraintID & id, const optional<long long> & row, const Literals & lits) -> void
{
    // cake_pb_cp's accumulator scheme, over the literals as cake reads them
    // (each operand tuple maps to the same ge / eq atom our proof uses):
    // x[id][0] channels the parity bit (always the constant 1 here, which cake
    // carries as its pinned-true n[1][ge1] atom; our rows fold it), x[id][k] =
    // x[id][k-1] XOR the k'th literal via four labelled clauses, and the acc
    // row pins the final accumulator to 0, i.e. 1 XOR (parity of the literals)
    // = 0.
    auto role_prefix = row ? "r" + to_string(*row) + "_" : string{};
    auto flag_values = [&](long long k) {
        vector<long long> values;
        if (row)
            values.push_back(*row);
        values.push_back(k);
        return values;
    };

    auto x0 = model.create_proof_flag(id, flag_values(0), nullopt);
    model.add_labelled_constraint(id, role_prefix + "0ge", WPBSum{} + 1_i * TrueLiteral{} + -1_i * x0 >= 0_i);
    model.add_labelled_constraint(id, role_prefix + "0le", WPBSum{} + 1_i * x0 + -1_i * TrueLiteral{} >= 0_i);
    PseudoBooleanTerm acc = x0, not_acc = ! x0;
    for (const auto & [k, l] : enumerate(lits)) {
        auto new_acc = model.create_proof_flag(id, flag_values(static_cast<long long>(k) + 1), nullopt);
        auto stem = role_prefix + to_string(k + 1);
        model.add_labelled_constraint(id, stem + "_0_0", WPBSum{} + 1_i * acc + 1_i * l + 1_i * ! new_acc >= 1_i);
        model.add_labelled_constraint(id, stem + "_1_1", WPBSum{} + 1_i * not_acc + 1_i * ! l + 1_i * ! new_acc >= 1_i);
        model.add_labelled_constraint(id, stem + "_1_0", WPBSum{} + 1_i * not_acc + 1_i * l + 1_i * new_acc >= 1_i);
        model.add_labelled_constraint(id, stem + "_0_1", WPBSum{} + 1_i * acc + 1_i * ! l + 1_i * new_acc >= 1_i);
        acc = new_acc;
        not_acc = ! new_acc;
    }
    model.add_labelled_constraint(id, role_prefix + "acc", WPBSum{} + -1_i * acc >= 0_i);
}
