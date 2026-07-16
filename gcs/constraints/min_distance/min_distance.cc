#include <gcs/constraints/min_distance/min_distance.hh>
#include <gcs/exception.hh>
#include <gcs/innards/inference_tracker.hh>
#include <gcs/innards/proofs/names_and_ids_tracker.hh>
#include <gcs/innards/proofs/proof_logger.hh>
#include <gcs/innards/proofs/proof_model.hh>
#include <gcs/innards/propagators.hh>
#include <gcs/innards/s_expr.hh>
#include <gcs/innards/state.hh>

#include <algorithm>
#include <map>
#include <optional>
#include <set>
#include <string>
#include <utility>
#include <vector>

using namespace gcs;
using namespace gcs::innards;

using std::make_unique;
using std::map;
using std::optional;
using std::pair;
using std::set;
using std::string;
using std::to_string;
using std::unique_ptr;
using std::vector;

MinDistance::MinDistance(vector<IntegerVariableID> x, IntegerVariableID z, ArrayParam<Matrix> distances, optional<ArrayParam<Matrix>> requirements) :
    _x(move(x)), _z(z), _distances(move(distances)), _requirements(move(requirements))
{
}

auto MinDistance::clone() const -> unique_ptr<Constraint>
{
    return make_unique<MinDistance>(_x, _z, _distances, _requirements);
}

auto MinDistance::install(Propagators & propagators, State & initial_state, ProofModel * const optional_model) && -> void
{
    if (! prepare(propagators, initial_state, optional_model))
        return;

    if (optional_model)
        define_proof_model(*optional_model);

    install_propagators(propagators);
}

auto MinDistance::prepare(Propagators & propagators, State & initial_state, ProofModel * const optional_model) -> bool
{
    const auto p = _x.size();
    if (p < 2)
        throw InvalidProblemDefinitionException{"min_distance requires at least two selected-point variables"};

    const auto & D = *_distances;
    const auto n = D.size();
    if (n == 0)
        throw InvalidProblemDefinitionException{"min_distance distance matrix must be non-empty"};
    for (std::size_t a = 0; a < n; ++a) {
        if (D[a].size() != n)
            throw InvalidProblemDefinitionException{"min_distance distance matrix must be square"};
        if (D[a][a] != 0_i)
            throw InvalidProblemDefinitionException{"min_distance distance matrix must have a zero diagonal"};
        for (std::size_t b = 0; b < n; ++b) {
            if (D[a][b] < 0_i)
                throw InvalidProblemDefinitionException{"min_distance distances must be non-negative"};
            if (D[a][b] != D[b][a])
                throw InvalidProblemDefinitionException{"min_distance distance matrix must be symmetric"};
        }
    }
    if (_requirements) {
        const auto & R = **_requirements;
        if (R.size() != p)
            throw InvalidProblemDefinitionException{"min_distance requirements matrix must be p x p"};
        for (std::size_t i = 0; i < p; ++i) {
            if (R[i].size() != p)
                throw InvalidProblemDefinitionException{"min_distance requirements matrix must be p x p"};
            for (std::size_t j = i + 1; j < p; ++j)
                if (R[i][j] < 0_i)
                    throw InvalidProblemDefinitionException{"min_distance requirements must be non-negative"};
        }
    }

    // Restrict every selected-point variable to the site index range [0, n-1]
    // (mirroring how Element clamps its index variables to the array bounds),
    // emitting the definitional OPB bounds and a RUP initialiser to prune
    // anything outside. A no-op when the variable is already within range.
    for (const auto & x : _x) {
        propagators.define_bound(initial_state, optional_model, x, Bound::Lower, 0_i);
        propagators.define_bound(initial_state, optional_model, x, Bound::Upper, Integer(static_cast<long long>(n) - 1));
    }

    // Record, per position, which site indices it can still take (within the
    // site range), the union of those, and z's initial bounds, for the proof
    // model (which does not receive the State).
    _position_sites.assign(p, {});
    vector<bool> is_site(n, false);
    for (std::size_t i = 0; i < p; ++i)
        for (std::size_t a = 0; a < n; ++a) {
            auto site = Integer(static_cast<long long>(a));
            if (initial_state.in_domain(_x[i], site)) {
                _position_sites[i].push_back(site);
                is_site[a] = true;
            }
        }
    for (std::size_t a = 0; a < n; ++a)
        if (is_site[a])
            _sites.push_back(Integer(static_cast<long long>(a)));

    auto z_bounds = initial_state.bounds(_z);
    _z_lower = z_bounds.first;
    _z_upper = z_bounds.second;

    return true;
}

auto MinDistance::define_proof_model(ProofModel & model) -> void
{
    const auto p = _x.size();
    const auto & D = *_distances;
    const auto z_lo = _z_lower, z_hi = _z_upper;
    const auto pbig = Integer(static_cast<long long>(p));

    auto d_at = [&](Integer a, Integer b) -> Integer { return D[a.raw_value][b.raw_value]; };

    // Positions that can take each candidate site.
    map<Integer, vector<std::size_t>> positions_at;
    for (std::size_t i = 0; i < p; ++i)
        for (const auto & a : _position_sites[i])
            positions_at[a].push_back(i);

    // u_a <-> OR_i [x_i == a]  (arc-consistent full reif).
    map<Integer, ProofFlag> u;
    for (const auto & a : _sites) {
        WPBSum orsum;
        for (auto i : positions_at[a])
            orsum += 1_i * (_x[i] == a);
        u.emplace(a, model.create_proof_flag_fully_reifying("mindist_u_" + to_string(a.raw_value), orsum >= 1_i));
    }

    // Per-site count: count_a <= 1 + (p-1)[z<=0]. This is the diagonal pair
    // upper bound: two positions on the same site witness the distance
    // D[a,a] = 0, forcing z <= 0. Handle the constant-literal cases explicitly.
    for (const auto & a : _sites) {
        const auto & pos = positions_at[a];
        if (pos.size() < 2)
            continue; // no duplicate possible: constraint is vacuous
        if (z_hi <= 0_i)
            continue; // [z<=0] is forced true: constraint is vacuous
        WPBSum count;
        for (auto i : pos)
            count += 1_i * (_x[i] == a);
        if (z_lo >= 1_i)
            model.add_constraint(count <= 1_i); // [z<=0] impossible: plain at-most-one
        else {
            count += (pbig - 1_i) * (_z >= 1_i); // count_a + (p-1)[z>=1] <= p
            model.add_constraint(count <= pbig);
        }
    }

    // Pair clauses: ~u_a \/ ~u_b \/ [z <= D[a,b]] for candidate a < b. Omitted
    // only when tautological for z's whole initial domain (z_max <= D[a,b]).
    for (std::size_t ia = 0; ia < _sites.size(); ++ia)
        for (std::size_t ib = ia + 1; ib < _sites.size(); ++ib) {
            auto a = _sites[ia], b = _sites[ib];
            auto dab = d_at(a, b);
            if (z_hi <= dab)
                continue;
            model.add_constraint(WPBSum{} + 1_i * (! u.at(a)) + 1_i * (! u.at(b)) + 1_i * (_z <= dab) >= 1_i);
        }

    // Requirement clauses: forbid x_i = a and x_j = b whenever D[a,b] < R_ij
    // (this includes the a == b diagonal, D[a,a] = 0 < R_ij, when R_ij > 0).
    if (_requirements) {
        const auto & R = **_requirements;
        for (std::size_t i = 0; i < p; ++i)
            for (std::size_t j = i + 1; j < p; ++j) {
                auto rij = R[i][j];
                if (rij <= 0_i)
                    continue;
                for (const auto & a : _position_sites[i])
                    for (const auto & b : _position_sites[j])
                        if (d_at(a, b) < rij)
                            model.add_constraint(WPBSum{} + 1_i * (_x[i] != a) + 1_i * (_x[j] != b) >= 1_i);
            }
    }

    // Min-attained ladder (the lower bound on z). Levels are the distinct
    // values { 0 } union { D[a,b] : candidate a < b }, sorted ascending. For
    // each level t_k we emit [z >= t_k] \/ m_k, where m_k says "some pair with a
    // strictly smaller distance is already attained"; so z is forced up to t_k
    // unless a smaller distance witness fires.
    set<Integer> level_set{0_i};
    for (std::size_t ia = 0; ia < _sites.size(); ++ia)
        for (std::size_t ib = ia + 1; ib < _sites.size(); ++ib)
            level_set.insert(d_at(_sites[ia], _sites[ib]));
    vector<Integer> levels(level_set.begin(), level_set.end());
    const auto num_levels = levels.size();

    if (! levels.empty() && z_lo < levels.back()) {
        map<Integer, ProofFlag> d;                // duplicate (distance-0) witnesses
        map<pair<Integer, Integer>, ProofFlag> w; // off-diagonal pair witnesses

        auto d_flag = [&](Integer a) -> ProofFlag {
            if (auto it = d.find(a); it != d.end())
                return it->second;
            WPBSum count;
            for (auto i : positions_at[a])
                count += 1_i * (_x[i] == a);
            auto f = model.create_proof_flag_fully_reifying("mindist_d_" + to_string(a.raw_value), count >= 2_i);
            d.emplace(a, f);
            return f;
        };
        auto w_flag = [&](Integer a, Integer b) -> ProofFlag {
            auto key = pair{a, b};
            if (auto it = w.find(key); it != w.end())
                return it->second;
            auto f = model.create_proof_flag_fully_reifying(
                "mindist_w_" + to_string(a.raw_value) + "_" + to_string(b.raw_value), WPBSum{} + 1_i * u.at(a) + 1_i * u.at(b) >= 2_i);
            w.emplace(key, f);
            return f;
        };
        auto witnesses_at = [&](Integer v) -> vector<ProofFlag> {
            vector<ProofFlag> ws;
            if (v == 0_i)
                for (const auto & a : _sites)
                    if (positions_at[a].size() >= 2)
                        ws.push_back(d_flag(a));
            for (std::size_t ia = 0; ia < _sites.size(); ++ia)
                for (std::size_t ib = ia + 1; ib < _sites.size(); ++ib) {
                    auto a = _sites[ia], b = _sites[ib];
                    if (d_at(a, b) == v)
                        ws.push_back(w_flag(a, b));
                }
            return ws;
        };

        optional<ProofFlag> m_acc; // m_k: some witness strictly below t_k fires; nullopt = definitely false
        for (std::size_t k = 0; k < num_levels; ++k) {
            auto t = levels[k];
            if (z_lo < t) {
                WPBSum clause;
                clause += 1_i * (_z >= t);
                if (m_acc)
                    clause += 1_i * (*m_acc);
                model.add_constraint(clause >= 1_i);
            }
            // Fold this level's witnesses into the accumulator for higher levels
            // (only needed while there is still a higher level to guard).
            if (k + 1 < num_levels) {
                auto ws = witnesses_at(t);
                if (! ws.empty()) {
                    WPBSum s;
                    if (m_acc)
                        s += 1_i * (*m_acc);
                    for (auto & f : ws)
                        s += 1_i * f;
                    m_acc = model.create_proof_flag_fully_reifying("mindist_m_" + to_string(t.raw_value), s >= 1_i);
                }
            }
        }
    }
}

auto MinDistance::install_propagators(Propagators & propagators) -> void
{
    const auto n = static_cast<long long>((*_distances).size());

    Triggers triggers;
    for (const auto & x : _x)
        triggers.on_instantiated.emplace_back(x);
    triggers.scope_only.emplace_back(_z);

    auto all_reason = generic_reason(_x);

    propagators.install(
        constraint_id(),
        [x = _x, z = _z, distances = _distances, requirements = _requirements, n, all_reason = std::move(all_reason)](
            const State & state, auto & inference, ProofLogger * const logger) -> PropagatorState {
            const auto & D = *distances;
            const auto p = x.size();

            vector<optional<Integer>> value(p);
            bool all_assigned = true;
            for (std::size_t i = 0; i < p; ++i) {
                value[i] = state.optional_single_value(x[i]);
                if (! value[i])
                    all_assigned = false;
            }

            // For every pair whose endpoints are both fixed: check the pairwise
            // requirement, then tighten z <= D[a,b]. Both are plain RUP from the
            // encoding, reasoned over just the two fixed endpoints.
            for (std::size_t i = 0; i < p; ++i) {
                if (! value[i])
                    continue;
                auto a = value[i]->raw_value;
                if (a < 0 || a >= n)
                    continue; // defensive: the site-range initialiser keeps x within [0, n-1]
                for (std::size_t j = i + 1; j < p; ++j) {
                    if (! value[j])
                        continue;
                    auto b = value[j]->raw_value;
                    if (b < 0 || b >= n)
                        continue;
                    auto dab = D[a][b];
                    auto reason = generic_reason(vector<IntegerVariableID>{x[i], x[j]});
                    if (requirements && dab < (**requirements)[i][j])
                        inference.contradiction(logger, JustifyUsingRUP{}, reason);
                    inference.infer_less_than(logger, z, dab + 1_i, JustifyUsingRUP{}, reason);
                }
            }

            // Once every endpoint is fixed, z is exactly the minimum pairwise
            // distance: pin it from both sides (z <= mu is already covered above,
            // z >= mu is the min-attained ladder).
            if (all_assigned) {
                optional<Integer> mu;
                for (std::size_t i = 0; i < p; ++i) {
                    auto a = value[i]->raw_value;
                    if (a < 0 || a >= n)
                        return PropagatorState::Enable;
                    for (std::size_t j = i + 1; j < p; ++j) {
                        auto b = value[j]->raw_value;
                        if (b < 0 || b >= n)
                            return PropagatorState::Enable;
                        auto dab = D[a][b];
                        mu = mu ? std::min(*mu, dab) : dab;
                    }
                }
                if (mu) {
                    inference.infer_greater_than_or_equal(logger, z, *mu, JustifyUsingRUP{}, all_reason);
                    inference.infer_less_than(logger, z, *mu + 1_i, JustifyUsingRUP{}, all_reason);
                }
            }

            return PropagatorState::Enable;
        },
        triggers);
}

auto MinDistance::constraint_type() const -> string
{
    return "min_distance";
}

auto MinDistance::s_expr(const ProofModel * const model) const -> SExpr
{
    auto & tracker = model->names_and_ids_tracker();

    vector<SExpr> xs;
    for (const auto & x : _x)
        xs.push_back(tracker.s_expr_term_of(x));

    auto matrix_expr = [](const Matrix & m) -> SExpr {
        vector<SExpr> rows;
        for (const auto & row : m) {
            vector<SExpr> entries;
            for (const auto & e : row)
                entries.push_back(SExpr::atom(e.to_string()));
            rows.push_back(SExpr::list(std::move(entries)));
        }
        return SExpr::list(std::move(rows));
    };

    vector<SExpr> term{SExpr::atom(as_string(_constraint_id)), SExpr::atom(constraint_type()), SExpr::list(std::move(xs)), tracker.s_expr_term_of(_z),
        matrix_expr(*_distances)};
    if (_requirements)
        term.push_back(matrix_expr(**_requirements));
    return SExpr::list(std::move(term));
}
