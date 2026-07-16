#include <gcs/constraints/min_distance/min_distance.hh>
#include <gcs/exception.hh>
#include <gcs/innards/inference_tracker.hh>
#include <gcs/innards/proofs/names_and_ids_tracker.hh>
#include <gcs/innards/proofs/pol_builder.hh>
#include <gcs/innards/proofs/proof_logger.hh>
#include <gcs/innards/proofs/proof_model.hh>
#include <gcs/innards/propagators.hh>
#include <gcs/innards/reason.hh>
#include <gcs/innards/s_expr.hh>
#include <gcs/innards/state.hh>

#include <algorithm>
#include <cstdint>
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

MinDistance::MinDistance(vector<IntegerVariableID> x, IntegerVariableID z, ArrayParam<Matrix> distances, optional<ArrayParam<Matrix>> requirements,
    MinDistancePropagation propagation) :
    _x(move(x)), _z(z), _distances(move(distances)), _requirements(move(requirements)), _propagation(propagation)
{
}

auto MinDistance::clone() const -> unique_ptr<Constraint>
{
    return make_unique<MinDistance>(_x, _z, _distances, _requirements, _propagation);
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
    if (_propagation == MinDistancePropagation::CheckOnly) {
        install_check_only_propagator(propagators);
        return;
    }
    const bool pair_support = _propagation == MinDistancePropagation::PairSupport || _propagation == MinDistancePropagation::PairSupportMatch;
    install_forward_propagator(propagators, pair_support);
    // The matching upper-bound pass (paper Section 4.4) is posted as a separate
    // propagator alongside the base ForwardBound / PairSupport kernel; the base
    // kernel still handles all lower-bound support work.
    if (_propagation == MinDistancePropagation::ForwardBoundMatch || _propagation == MinDistancePropagation::PairSupportMatch)
        install_matching_propagator(propagators);
}

auto MinDistance::install_check_only_propagator(Propagators & propagators) -> void
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

auto MinDistance::install_forward_propagator(Propagators & propagators, bool pair_support) -> void
{
    const auto n = static_cast<long long>((*_distances).size());

    // Real propagation reacts to any domain change of a selected point (a value
    // removed from x_j can lose a support) and to a rise in z's lower bound
    // (which raises the T_ij threshold and invalidates supports); on_bounds on z
    // covers the lower-bound wake.
    Triggers triggers;
    for (const auto & x : _x)
        triggers.on_change.emplace_back(x);
    triggers.on_bounds.emplace_back(_z);

    auto all_reason = generic_reason(_x);

    propagators.install(
        constraint_id(),
        [x = _x, z = _z, distances = _distances, requirements = _requirements, n, pair_support, all_reason = std::move(all_reason)](
            const State & state, auto & inference, ProofLogger * const logger) -> PropagatorState {
            const auto & D = *distances;
            const auto p = x.size();
            const bool has_reqs = requirements.has_value();

            auto in_range = [&](Integer v) { return v.raw_value >= 0 && v.raw_value < n; };
            auto r_at = [&](std::size_t i, std::size_t j) -> Integer { return has_reqs ? (**requirements)[i][j] : 0_i; };
            auto d_at = [&](Integer a, Integer b) -> Integer { return D[a.raw_value][b.raw_value]; };

            // z's lower bound at the top of this wake feeds every threshold. If a
            // later inference here raises it (the full-assignment pin does), the
            // on_bounds trigger re-queues us and we recompute with the new value.
            const auto z_min = state.lower_bound(z);

            for (std::size_t i = 0; i < p; ++i)
                for (std::size_t j = i + 1; j < p; ++j) {
                    const auto rij = r_at(i, j);
                    const auto tij = std::max(rij, z_min);

                    // (1) Assigned-endpoint forward prune (paper Section 4.1). When
                    // one endpoint is fixed to a, remove every b from the other
                    // endpoint's domain with D[a,b] < T_ij. Plain RUP: {x_i = a},
                    // plus z >= z_min when the z part of the threshold binds (the R
                    // forbidden-pair clause carries the R part on its own).
                    auto forward_prune = [&](std::size_t assigned_pos, std::size_t other_pos) {
                        auto av = state.optional_single_value(x[assigned_pos]);
                        if (! av || ! in_range(*av))
                            return;
                        auto a = *av;
                        vector<Integer> other_dom;
                        state.for_each_value_immutable(x[other_pos], [&](Integer b) { other_dom.push_back(b); });
                        for (auto b : other_dom) {
                            if (! in_range(b) || d_at(a, b) >= tij)
                                continue;
                            ReasonLiterals rlits{x[assigned_pos] == a};
                            if (! (has_reqs && d_at(a, b) < rij))
                                rlits.push_back(z >= z_min);
                            inference.infer_not_equal(logger, x[other_pos], b, JustifyUsingRUP{}, ExplicitReason{std::move(rlits)});
                        }
                    };
                    forward_prune(i, j);
                    forward_prune(j, i);

                    // (2) Pairwise objective upper bound (paper Section 4.1):
                    //   u_ij = max{ D[a,b] : a in dom(x_i), b in dom(x_j), D[a,b] >= R_ij }.
                    // If the set is empty (or its max is below z_min) the pair cannot
                    // be satisfied and the node fails; otherwise tighten z <= u_ij.
                    optional<Integer> u;
                    state.for_each_value_immutable(x[i], [&](Integer a) {
                        if (! in_range(a))
                            return;
                        state.for_each_value_immutable(x[j], [&](Integer b) {
                            if (! in_range(b))
                                return;
                            auto dab = d_at(a, b);
                            if (dab >= rij)
                                u = u ? std::max(*u, dab) : dab;
                        });
                    });

                    // Loop the smaller endpoint domain in the explicit per-value
                    // derivation (both work by symmetry; the smaller one is cheaper).
                    auto loop_pos = state.domain_size(x[i]) <= state.domain_size(x[j]) ? i : j;

                    if (! u || *u < z_min) {
                        // Pair infeasible. For each a in dom(x_loop), every b in the
                        // other domain dies (R clause when D[a,b] < R_ij; else the
                        // pair clause with z >= z_min), so ~[x_loop = a]; then x_loop's
                        // at-least-one closes the contradiction. Item 4 of the spec.
                        const bool z_guards = u.has_value(); // empty set is pure-R, no z role
                        auto emit_infeasible = [&, loop_pos](const ReasonLiterals & reason) {
                            state.for_each_value_immutable(x[loop_pos], [&](Integer a) {
                                if (! in_range(a))
                                    return;
                                logger->emit_rup_proof_line_under_reason(reason, WPBSum{} + 1_i * (x[loop_pos] != a) >= 1_i, ProofLevel::Temporary);
                            });
                        };
                        Reason reason = generic_reason(vector<IntegerVariableID>{x[i], x[j]});
                        if (z_guards)
                            reason = with_extra(std::move(reason), ReasonLiterals{z >= z_min});
                        inference.contradiction(logger, JustifyExplicitly{emit_infeasible, ThenRUP::Yes}, reason);
                    }
                    else if (*u < state.upper_bound(z)) {
                        auto uu = *u;
                        // Item 3 of the spec: for each a in dom(x_loop) derive
                        // ~[x_loop = a] \/ [z <= u_ij]; the z bound needed to kill each
                        // partner b comes free from negating [z <= u_ij], so the reason
                        // is just the two endpoint domains.
                        auto emit_ub = [&, loop_pos, uu](const ReasonLiterals & reason) {
                            state.for_each_value_immutable(x[loop_pos], [&](Integer a) {
                                if (! in_range(a))
                                    return;
                                logger->emit_rup_proof_line_under_reason(
                                    reason, WPBSum{} + 1_i * (x[loop_pos] != a) + 1_i * (z <= uu) >= 1_i, ProofLevel::Temporary);
                            });
                        };
                        inference.infer_less_than(
                            logger, z, uu + 1_i, JustifyExplicitly{emit_ub, ThenRUP::Yes}, generic_reason(vector<IntegerVariableID>{x[i], x[j]}));
                    }

                    // (3) Pair-support scan (paper Section 4.2), PairSupport only.
                    // Remove a from an endpoint's domain when no value of the other
                    // endpoint supports it (D[a,b] >= T_ij). Plain RUP: assuming
                    // [x_from = a], every b in dom(x_to) dies, and x_to's
                    // at-least-one closes it. Item 2 of the spec.
                    if (pair_support) {
                        const bool z_binds = z_min > rij;
                        auto support_scan = [&](std::size_t from_pos, std::size_t to_pos) {
                            vector<Integer> from_dom;
                            state.for_each_value_immutable(x[from_pos], [&](Integer a) { from_dom.push_back(a); });
                            for (auto a : from_dom) {
                                if (! in_range(a) || ! state.in_domain(x[from_pos], a))
                                    continue;
                                bool supported = false;
                                state.for_each_value_immutable(x[to_pos], [&](Integer b) {
                                    if (in_range(b) && d_at(a, b) >= tij) {
                                        supported = true;
                                        return false;
                                    }
                                    return true;
                                });
                                if (! supported) {
                                    Reason reason = generic_reason(vector<IntegerVariableID>{x[to_pos]});
                                    if (z_binds)
                                        reason = with_extra(std::move(reason), ReasonLiterals{z >= z_min});
                                    inference.infer_not_equal(logger, x[from_pos], a, JustifyUsingRUP{}, reason);
                                }
                            }
                        };
                        support_scan(i, j);
                        support_scan(j, i);
                    }
                }

            // Once every endpoint is fixed, pin z to the exact minimum pairwise
            // distance. The forward bounds above supply z <= mu; z >= mu is the
            // min-attained ladder (plain RUP, reasoned over all of x). This is what
            // makes a full assignment with z < mu unacceptable.
            bool all_assigned = true;
            for (std::size_t i = 0; i < p; ++i)
                if (! state.optional_single_value(x[i]))
                    all_assigned = false;
            if (all_assigned) {
                optional<Integer> mu;
                for (std::size_t i = 0; i < p; ++i) {
                    auto a = state.optional_single_value(x[i]).value();
                    if (! in_range(a))
                        return PropagatorState::Enable;
                    for (std::size_t j = i + 1; j < p; ++j) {
                        auto b = state.optional_single_value(x[j]).value();
                        if (! in_range(b))
                            return PropagatorState::Enable;
                        auto dab = d_at(a, b);
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

auto MinDistance::install_matching_propagator(Propagators & propagators) -> void
{
    const auto n = static_cast<long long>((*_distances).size());
    const auto p = _x.size();

    // Sorted distinct off-diagonal distances of D: the candidate levels for the
    // conflict-matching test (paper Algorithm 1). Precomputed once here.
    set<Integer> level_set;
    {
        const auto & D = *_distances;
        for (long long a = 0; a < n; ++a)
            for (long long b = a + 1; b < n; ++b)
                level_set.insert(D[a][b]);
    }
    vector<Integer> levels(level_set.begin(), level_set.end());

    // positions_at[a] = the positions whose *root* domain contains site a (from
    // _position_sites, frozen at prepare()). The counting derivation ranges the
    // literals over exactly these positions --- mirroring the encoding's u/count
    // reifications and each variable's at-least-one --- so absent [x_i = a]
    // literals (a not in x_i's root domain) never appear anywhere.
    vector<vector<std::uint32_t>> positions_at(static_cast<std::size_t>(n));
    for (std::size_t i = 0; i < p; ++i)
        for (const auto & a : _position_sites[i])
            positions_at[static_cast<std::size_t>(a.raw_value)].push_back(static_cast<std::uint32_t>(i));

    // Wake on any selected-point domain change (the active site set shrinks) and
    // on z-bound changes (they move the candidate-level window).
    Triggers triggers;
    for (const auto & x : _x)
        triggers.on_change.emplace_back(x);
    triggers.on_bounds.emplace_back(_z);

    propagators.install(
        constraint_id(),
        [x = _x, z = _z, distances = _distances, n, p, levels = std::move(levels), positions_at = std::move(positions_at)](
            const State & state, auto & inference, ProofLogger * const logger) -> PropagatorState {
            const auto & D = *distances;
            auto d_at = [&](Integer a, Integer b) -> Integer { return D[a.raw_value][b.raw_value]; };

            // Active site set A = union of the current selected-point domains
            // (site values only, ascending).
            vector<char> present(static_cast<std::size_t>(n), 0);
            for (std::size_t i = 0; i < p; ++i)
                state.for_each_value_immutable(x[i], [&](Integer v) {
                    if (v.raw_value >= 0 && v.raw_value < n)
                        present[static_cast<std::size_t>(v.raw_value)] = 1;
                });
            vector<Integer> A;
            for (long long a = 0; a < n; ++a)
                if (present[static_cast<std::size_t>(a)])
                    A.push_back(Integer{a});
            if (A.empty())
                return PropagatorState::Enable;

            const auto z_min = state.lower_bound(z);
            const auto z_max = state.upper_bound(z);

            // Candidate levels: distinct distances t with max(z_min, 1) <= t <= z_max.
            // The level 0 is never worth testing (every placement has non-negative
            // pairwise distance, so z >= 0 is not refutable); t = z_min (>= 1) is
            // kept so an unachievable current lower bound fails the node.
            const auto t_low = std::max(z_min, 1_i);
            if (t_low > z_max)
                return PropagatorState::Enable;
            auto lo_it = std::lower_bound(levels.begin(), levels.end(), t_low);
            auto hi_it = std::upper_bound(levels.begin(), levels.end(), z_max);
            if (lo_it >= hi_it)
                return PropagatorState::Enable;
            const std::size_t lo = static_cast<std::size_t>(lo_it - levels.begin());
            const std::size_t hi = static_cast<std::size_t>(hi_it - levels.begin()) - 1;

            // Greedy maximal matching on the conflict graph G_t[A] (edge (a, b),
            // a < b in A, iff D[a,b] < t). Deterministic edge order (A-order),
            // scratch reused across the binary-search probes.
            vector<char> matched(A.size(), 0);
            vector<pair<std::size_t, std::size_t>> edges;
            auto build_matching = [&](Integer t) {
                std::fill(matched.begin(), matched.end(), static_cast<char>(0));
                edges.clear();
                for (std::size_t ia = 0; ia < A.size(); ++ia) {
                    if (matched[ia])
                        continue;
                    for (std::size_t ib = ia + 1; ib < A.size(); ++ib)
                        if (! matched[ib] && d_at(A[ia], A[ib]) < t) {
                            matched[ia] = matched[ib] = 1;
                            edges.emplace_back(ia, ib);
                            break;
                        }
                }
            };
            auto refuted_at = [&](Integer t) {
                build_matching(t);
                return static_cast<long long>(A.size()) - static_cast<long long>(edges.size()) < static_cast<long long>(p);
            };

            // Binary-search the level window for the smallest refuted level. The
            // greedy matching is only weakly monotone, so this is a heuristic for a
            // good level, not a proof of monotonicity; every refutation is certified
            // in its own right (paper Section 4.4).
            std::optional<std::size_t> refuted_idx;
            std::size_t left = lo, right = hi;
            while (left <= right) {
                std::size_t mid = left + (right - left) / 2;
                if (refuted_at(levels[mid])) {
                    refuted_idx = mid;
                    if (mid == 0)
                        break;
                    right = mid - 1;
                }
                else
                    left = mid + 1;
            }
            if (! refuted_idx)
                return PropagatorState::Enable;

            const auto t = levels[*refuted_idx];
            // Rebuild the matching at the chosen level for the justification
            // (deterministic, so identical to the probe that found it).
            build_matching(t);
            vector<Integer> unmatched;
            for (std::size_t ia = 0; ia < A.size(); ++ia)
                if (! matched[ia])
                    unmatched.push_back(A[ia]);

            // C = sum of guard coefficients across the per-edge and per-unmatched
            // at-most-ones: |L_ab| - 1 per edge (2p - 1 when every position can take
            // both sites), |P_c| - 1 per unmatched site. Dividing the final sum by C
            // leaves the guard g = [z <= t-1] with coefficient exactly one.
            auto lit_count = [&](Integer site) { return positions_at[static_cast<std::size_t>(site.raw_value)].size(); };
            Integer sum_c = 0_i;
            for (const auto & [ia, ib] : edges)
                sum_c += Integer{static_cast<long long>(lit_count(A[ia]) + lit_count(A[ib])) - 1};
            for (const auto & c : unmatched)
                sum_c += Integer{static_cast<long long>(lit_count(c)) - 1};
            if (sum_c < 1_i)
                return PropagatorState::Enable; // no guard-bearing constraint (cannot happen on a refutation)

            const auto t_minus_1 = t - 1_i;
            const auto guard = (z <= t_minus_1); // g = ~[z >= t]

            // Emit the guarded counting derivation (verified prototype shape). Runs
            // synchronously inside the infer below, so the [&] captures of the local
            // matching state are live throughout.
            auto emit = [&](const ReasonLiterals &) {
                auto & tracker = logger->names_and_ids_tracker();

                // A guarded at-most-one over a literal set L = { [x_pos = site] }.
                // Per unordered pair emit ~l_r \/ ~l_s \/ g by RUP (cross-site via
                // the pair clause + z order; same-site via the per-site count
                // constraint + z order; same-position via the variable's at-most-one),
                // then combine with the all_different PolBuilder layer recurrence, so
                // g rides through the ceil-divisions with an exact coefficient:
                // Sum_{l in L} ~l + (|L|-1) g >= |L|-1.
                auto emit_am1 = [&](const vector<pair<std::uint32_t, Integer>> & lits) -> std::optional<ProofLine> {
                    if (lits.size() < 2) {
                        // A single-literal site contributes nothing to the counting
                        // beyond cancelling its own at-least-one term; the trivially
                        // true ~[x_pos = site] >= 0 does exactly that.
                        if (lits.size() == 1)
                            return logger->emit_rup_proof_line(WPBSum{} + 1_i * (x[lits[0].first] != lits[0].second) >= 0_i, ProofLevel::Temporary);
                        return std::nullopt;
                    }
                    PolBuilder am1;
                    int layer = 0;
                    for (std::size_t i = 1; i < lits.size(); ++i) {
                        if (++layer >= 2)
                            am1.multiply_by(Integer{layer});
                        for (std::size_t j = 0; j < i; ++j) {
                            auto ne = logger->emit_rup_proof_line(
                                WPBSum{} + 1_i * (x[lits[i].first] != lits[i].second) + 1_i * (x[lits[j].first] != lits[j].second) + 1_i * guard >=
                                    1_i,
                                ProofLevel::Temporary);
                            am1.add(ne);
                        }
                        am1.divide_by(Integer{layer + 1});
                    }
                    return am1.emit(*logger, ProofLevel::Temporary);
                };

                PolBuilder final_pol;
                vector<pair<std::uint32_t, Integer>> lits;
                for (const auto & [ia, ib] : edges) {
                    lits.clear();
                    for (auto pos : positions_at[static_cast<std::size_t>(A[ia].raw_value)])
                        lits.emplace_back(pos, A[ia]);
                    for (auto pos : positions_at[static_cast<std::size_t>(A[ib].raw_value)])
                        lits.emplace_back(pos, A[ib]);
                    if (auto line = emit_am1(lits))
                        final_pol.add(*line);
                }
                for (const auto & c : unmatched) {
                    lits.clear();
                    for (auto pos : positions_at[static_cast<std::size_t>(c.raw_value)])
                        lits.emplace_back(pos, c);
                    if (auto line = emit_am1(lits))
                        final_pol.add(*line);
                }
                for (std::size_t i = 0; i < p; ++i)
                    final_pol.add(tracker.need_constraint_saying_variable_takes_at_least_one_value(x[i]));
                final_pol.divide_by(sum_c);
                final_pol.emit(*logger, ProofLevel::Temporary);
            };

            if (t <= z_min)
                // The refuted level is at (or below) z's lower bound: z < t is
                // incompatible with z >= z_min, so the node fails. The pol still
                // derives g = [z <= t-1]; with z >= z_min in the reason it closes by
                // RUP (g is domain-false there).
                inference.contradiction(logger, JustifyExplicitly{emit, ThenRUP::Yes}, with_extra(generic_reason(x), ReasonLiterals{z >= z_min}));
            else
                inference.infer_less_than(logger, z, t, JustifyExplicitly{emit, ThenRUP::Yes}, generic_reason(x));

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
