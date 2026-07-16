#ifndef GLASGOW_CONSTRAINT_SOLVER_GUARD_EXAMPLES_P_DISPERSION_INSTANCE_HH
#define GLASGOW_CONSTRAINT_SOLVER_GUARD_EXAMPLES_P_DISPERSION_INSTANCE_HH

// Instance model, generators and readers for the p-dispersion example.
//
// A p-dispersion instance is a set of n candidate sites (indexed 0..n-1) with a
// symmetric non-negative integer distance matrix D with zero diagonal. The
// p-dispersion problem selects p of the sites so that the closest selected pair
// is as far apart as possible (maximise the minimum pairwise distance).
//
// The p-dispersion problem with distance constraints (PDDP) additionally gives,
// for each pair of selected positions (i, j) with i < j, a lower-bound
// requirement r_ij: the chosen sites for positions i and j must be at distance
// > r_ij, i.e. D[x_i][x_j] >= r_ij + 1. Following the paper we store the raw
// r_ij and the model performs the +1 conversion (R_ij = r_ij + 1).

#include <gcs/integer.hh>

#include <cmath>
#include <cstdint>
#include <fstream>
#include <map>
#include <optional>
#include <random>
#include <set>
#include <sstream>
#include <stdexcept>
#include <string>
#include <utility>
#include <vector>

namespace p_dispersion
{
    struct Instance
    {
        int n = 0; ///< Number of candidate sites, indexed 0..n-1.

        /// Symmetric distance matrix, n x n, zero diagonal, non-negative.
        std::vector<std::vector<gcs::Integer>> distance;

        /// Optional number of positions to select, when fixed by the instance
        /// file (PDDP instances that bundle per-pair requirements). When unset,
        /// p comes from the command line.
        std::optional<int> p;

        /// Optional raw per-position-pair requirements r_ij (paper's r_ij; the
        /// model posts D[x_i][x_j] >= r_ij + 1). Upper triangular and sized p x
        /// p when present: reqs[i][j] is used only for i < j. Empty for a plain
        /// p-dispersion instance.
        std::vector<std::vector<long>> reqs;

        /// Optional integer coordinates of each site, for grid / random-Euclidean
        /// instances (kept only for reporting; not used by the model).
        std::vector<std::pair<long, long>> coords;

        std::string description;
    };

    /// Largest entry of the distance matrix (the tightest possible upper bound
    /// on the minimum pairwise distance).
    [[nodiscard]] inline auto max_distance(const Instance & inst) -> gcs::Integer
    {
        auto best = gcs::Integer{0};
        for (const auto & row : inst.distance)
            for (const auto & d : row)
                if (d > best)
                    best = d;
        return best;
    }

    // Rounding convention for Euclidean instances: we take the true Euclidean
    // distance and round to the NEAREST integer (std::llround). This keeps the
    // distance matrix symmetric with a zero diagonal and non-negative integer
    // entries. Rounding (rather than truncating) is the more common choice for
    // GKD-style geometric MDPLIB instances; it can introduce ties, which is
    // fine for the objective. This choice is documented in the example README.
    [[nodiscard]] inline auto euclidean_rounded(long dx, long dy) -> gcs::Integer
    {
        return gcs::Integer{static_cast<long long>(std::llround(std::sqrt(static_cast<double>(dx * dx + dy * dy))))};
    }

    // Build an instance whose candidate sites are the W x H integer grid points
    // (w, h) for 0 <= w < W, 0 <= h < H, so n = W * H. Distances are the
    // rounded Euclidean distances between grid points.
    [[nodiscard]] inline auto make_grid(int width, int height) -> Instance
    {
        if (width < 1 || height < 1)
            throw std::runtime_error{"grid dimensions must be positive"};

        Instance inst;
        inst.n = width * height;
        inst.description = "grid " + std::to_string(width) + "x" + std::to_string(height);

        inst.coords.reserve(inst.n);
        for (int w = 0; w < width; ++w)
            for (int h = 0; h < height; ++h)
                inst.coords.emplace_back(w, h);

        inst.distance.assign(inst.n, std::vector<gcs::Integer>(inst.n, gcs::Integer{0}));
        for (int a = 0; a < inst.n; ++a)
            for (int b = a + 1; b < inst.n; ++b) {
                auto d = euclidean_rounded(inst.coords[a].first - inst.coords[b].first, inst.coords[a].second - inst.coords[b].second);
                inst.distance[a][b] = d;
                inst.distance[b][a] = d;
            }

        return inst;
    }

    // Build an instance of n sites placed uniformly at random with integer
    // coordinates in [0, span] x [0, span], distances rounded Euclidean.
    [[nodiscard]] inline auto make_random_euclidean(int n, std::uint_fast32_t seed, long span = 1000) -> Instance
    {
        if (n < 1)
            throw std::runtime_error{"random-euclidean needs at least one site"};

        Instance inst;
        inst.n = n;
        inst.description = "random-euclidean n=" + std::to_string(n) + " seed=" + std::to_string(seed) + " span=" + std::to_string(span);

        std::mt19937 rng{seed};
        std::uniform_int_distribution<long> coord{0, span};
        inst.coords.reserve(n);
        for (int i = 0; i < n; ++i)
            inst.coords.emplace_back(coord(rng), coord(rng));

        inst.distance.assign(n, std::vector<gcs::Integer>(n, gcs::Integer{0}));
        for (int a = 0; a < n; ++a)
            for (int b = a + 1; b < n; ++b) {
                auto d = euclidean_rounded(inst.coords[a].first - inst.coords[b].first, inst.coords[a].second - inst.coords[b].second);
                inst.distance[a][b] = d;
                inst.distance[b][a] = d;
            }

        return inst;
    }

    // Read an instance from the p-dispersion / maximum-diversity benchmark
    // formats used by Ploskas, Stergiou and Tsouros (the CP 2023 / CP 2024 /
    // ModRef 2025 PDDP library) and the original MDPLIB. All share a common
    // shape: a header line, then C(n,2) pairwise-distance triples "i j d_ij",
    // optionally followed by extra data. We support:
    //
    //   * PDDP "Format A"  header "n p", then C(n,2) distances, then C(p,2)
    //     per-position-pair requirement triples "i j r_ij" (indices 0..p-1).
    //     Distances may be integer (RANDOM class) or real (MDPLIB GKD/MDG/SOM);
    //     the RANDOM distance block uses arbitrary scattered site IDs, which we
    //     remap to 0..n-1 by sorted order.
    //   * Original MDPLIB "Format B"  header "n m", then C(n,2) distances,
    //     0-indexed contiguous, no requirements (m is a class parameter we
    //     ignore).
    //   * GKD "coor" files  header "n", then C(n,2) distances, then n "x y"
    //     coordinate lines, which we ignore.
    //
    // Real distances are rounded to the nearest integer (std::llround). The
    // format is inferred from the header and the exact number of trailing
    // tokens, so no explicit format flag is needed.
    [[nodiscard]] inline auto read_instance_stream(std::istream & in, const std::string & description) -> Instance
    {
        Instance inst;
        inst.description = description;

        // First non-empty line: n, and an optional second integer (p or m).
        std::string first;
        while (std::getline(in, first))
            if (first.find_first_not_of(" \t\r\n") != std::string::npos)
                break;
        std::istringstream hs{first};
        long n = 0, second = -1;
        if (! (hs >> n) || n <= 0)
            throw std::runtime_error{"could not read site count from instance"};
        hs >> second; // leaves second = -1 if absent
        inst.n = static_cast<int>(n);

        // Slurp every remaining whitespace-separated numeric token.
        std::vector<double> tok;
        for (double v; in >> v;)
            tok.push_back(v);

        const long n_pairs = n * (n - 1) / 2;
        if (static_cast<long>(tok.size()) < n_pairs * 3)
            throw std::runtime_error{"instance has fewer distance entries than the expected C(n,2)"};

        // First C(n,2) triples are the pairwise distances. Site IDs may be a
        // scattered set (RANDOM class), so collect and remap them to 0..n-1.
        struct Edge
        {
            long a, b;
            double d;
        };
        std::vector<Edge> edges;
        edges.reserve(n_pairs);
        std::set<long> ids;
        for (long k = 0; k < n_pairs; ++k) {
            auto a = static_cast<long>(std::llround(tok[3 * k]));
            auto b = static_cast<long>(std::llround(tok[3 * k + 1]));
            edges.push_back({a, b, tok[3 * k + 2]});
            ids.insert(a);
            ids.insert(b);
        }
        if (static_cast<long>(ids.size()) != n)
            throw std::runtime_error{"distance block does not mention exactly n distinct sites"};
        std::map<long, int> remap;
        {
            int idx = 0;
            for (auto id : ids)
                remap[id] = idx++;
        }

        inst.distance.assign(n, std::vector<gcs::Integer>(n, gcs::Integer{0}));
        for (const auto & e : edges) {
            int a = remap[e.a], b = remap[e.b];
            auto d = gcs::Integer{static_cast<long long>(std::llround(e.d))};
            inst.distance[a][b] = d;
            inst.distance[b][a] = d;
        }

        // PDDP (Format A): a p header plus exactly C(p,2) further triples means
        // the trailing block is the per-position-pair requirements r_ij.
        if (second >= 2) {
            long p = second;
            long r_pairs = p * (p - 1) / 2;
            long consumed = n_pairs * 3;
            if (r_pairs > 0 && static_cast<long>(tok.size()) - consumed == r_pairs * 3) {
                inst.p = static_cast<int>(p);
                inst.reqs.assign(p, std::vector<long>(p, -1));
                for (long k = 0; k < r_pairs; ++k) {
                    auto i = static_cast<long>(std::llround(tok[consumed + 3 * k]));
                    auto j = static_cast<long>(std::llround(tok[consumed + 3 * k + 1]));
                    auto r = static_cast<long>(std::llround(tok[consumed + 3 * k + 2]));
                    if (i < 0 || j < 0 || i >= p || j >= p)
                        throw std::runtime_error{"requirement index out of range"};
                    inst.reqs[i][j] = r;
                    inst.reqs[j][i] = r;
                }
            }
        }

        return inst;
    }

    [[nodiscard]] inline auto read_file(const std::string & path) -> Instance
    {
        std::ifstream in{path};
        if (! in)
            throw std::runtime_error{"could not open instance file: " + path};
        return read_instance_stream(in, "file " + path);
    }
}

#endif
