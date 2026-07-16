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
#include <limits>
#include <optional>
#include <random>
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

    // Read an MDPLIB-style distance instance. The supported format is the one
    // used by the maximum-diversity / p-dispersion literature (GKD, MDG, SOM
    // classes): the first line holds the number of sites n (optionally followed
    // by a second integer that we ignore), then one line per distinct pair,
    // "i j d", where i and j are site indices and d is their distance. Indices
    // may be 0- or 1-based; we detect which by looking at the range actually
    // used. Distances may be written as integers or reals; a real distance is
    // rounded to the nearest integer. Missing pairs default to distance 0.
    [[nodiscard]] inline auto read_mdplib(std::istream & in, const std::string & description) -> Instance
    {
        Instance inst;
        inst.description = description;

        std::string line;
        // First non-empty line: n (and optional extra token we ignore).
        while (std::getline(in, line)) {
            std::istringstream iss{line};
            long n = 0;
            if (iss >> n) {
                if (n <= 0)
                    throw std::runtime_error{"instance has non-positive site count"};
                inst.n = static_cast<int>(n);
                break;
            }
        }
        if (inst.n == 0)
            throw std::runtime_error{"could not read site count from instance"};

        // Read all "i j d" triples first, then decide on the index base.
        struct Triple
        {
            long i, j;
            double d;
        };
        std::vector<Triple> triples;
        long min_index = std::numeric_limits<long>::max();
        long max_index = std::numeric_limits<long>::min();
        while (std::getline(in, line)) {
            std::istringstream iss{line};
            long i = 0, j = 0;
            double d = 0.0;
            if (! (iss >> i >> j >> d))
                continue;
            min_index = std::min({min_index, i, j});
            max_index = std::max({max_index, i, j});
            triples.push_back({i, j, d});
        }

        // 1-based if the largest index reaches n and nothing hits 0.
        long base = (min_index >= 1 && max_index >= inst.n) ? 1 : 0;

        inst.distance.assign(inst.n, std::vector<gcs::Integer>(inst.n, gcs::Integer{0}));
        for (const auto & t : triples) {
            long i = t.i - base, j = t.j - base;
            if (i < 0 || j < 0 || i >= inst.n || j >= inst.n)
                throw std::runtime_error{"instance pair index out of range"};
            auto d = gcs::Integer{static_cast<long long>(std::llround(t.d))};
            inst.distance[i][j] = d;
            inst.distance[j][i] = d;
        }
        for (int i = 0; i < inst.n; ++i)
            inst.distance[i][i] = gcs::Integer{0};

        return inst;
    }

    [[nodiscard]] inline auto read_file(const std::string & path) -> Instance
    {
        std::ifstream in{path};
        if (! in)
            throw std::runtime_error{"could not open instance file: " + path};
        return read_mdplib(in, "file " + path);
    }
}

#endif
