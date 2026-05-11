#include <gcs/constraints/seq_precede_chain.hh>
#include <gcs/constraints/value_precede.hh>
#include <gcs/innards/proofs/names_and_ids_tracker.hh>
#include <gcs/innards/proofs/proof_model.hh>
#include <gcs/innards/propagators.hh>
#include <gcs/innards/state.hh>

#include <version>

#if defined(__cpp_lib_print) && defined(__cpp_lib_format)
#include <print>
#else
#include <fmt/ostream.h>
#endif

#include <memory>
#include <sstream>
#include <utility>

using namespace gcs;
using namespace gcs::innards;

using std::make_unique;
using std::move;
using std::string;
using std::stringstream;
using std::unique_ptr;
using std::vector;

#if defined(__cpp_lib_print) && defined(__cpp_lib_format)
using std::print;
#else
using fmt::print;
#endif

SeqPrecedeChain::SeqPrecedeChain(vector<IntegerVariableID> vars) :
    _vars(move(vars))
{
}

auto SeqPrecedeChain::clone() const -> unique_ptr<Constraint>
{
    return make_unique<SeqPrecedeChain>(_vars);
}

auto SeqPrecedeChain::install(Propagators & propagators, State & initial_state, ProofModel * const optional_model) && -> void
{
    auto n = _vars.size();
    if (n == 0)
        return;

    Integer max_upper = 0_i;
    for (const auto & v : _vars) {
        auto u = initial_state.upper_bound(v);
        if (u > max_upper)
            max_upper = u;
    }

    if (max_upper < 1_i)
        return;

    Integer n_as_int{static_cast<long long>(n)};
    Integer effective_max = (max_upper < n_as_int) ? max_upper : n_as_int;

    // If the declared domains can exceed effective_max, add explicit
    // upper-bound constraints. The chain encoding alone wouldn't rule out
    // values > effective_max — we'd lose soundness without these. The
    // bound is justified by the meta-argument that any value v requires
    // v distinct earlier positions to host 1..v-1, so v ≤ n.
    if (max_upper > effective_max) {
        for (const auto & v : _vars)
            propagators.define_bound(initial_state, optional_model, v, Bound::Upper, effective_max,
                "SeqPrecedeChain", "value bound");
    }

    if (effective_max < 2_i)
        return;

    vector<Integer> chain;
    for (Integer i = 1_i; i <= effective_max; ++i)
        chain.push_back(i);

    ValuePrecede{move(chain), move(_vars)}.install(propagators, initial_state, optional_model);
}

auto SeqPrecedeChain::s_exprify(const string & name, const ProofModel * const model) const -> string
{
    stringstream s;
    print(s, "{} seq_precede_chain (", name);
    for (const auto & var : _vars)
        print(s, " {}", model->names_and_ids_tracker().s_expr_name_of(var));
    print(s, ")");
    return s.str();
}
