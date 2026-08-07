#ifndef GLASGOW_CONSTRAINT_SOLVER_GUARD_EXAMPLES_TABLE_LAYOUT_TABLE_LAYOUT_INSTANCE_HH
#define GLASGOW_CONSTRAINT_SOLVER_GUARD_EXAMPLES_TABLE_LAYOUT_TABLE_LAYOUT_INSTANCE_HH

// Instance model, generator and .dzn reader for the table-layout example.
//
// An instance is a rows x cols grid of cells. Cell (r, c) may be laid out in
// any of several configurations; configuration l gives it width[r][c][l]
// pixels of width and height[r][c][l] pixels of height. Different cells may
// have different numbers of configurations, so the arrays are rectangular and
// PADDED WITH A NEGATIVE VALUE: width[r][c][l] < 0 means "cell (r, c) has
// fewer than l + 1 configurations", and l is then not a legal configuration
// for that cell. This is the convention of the MiniZinc Challenge 2023
// TableLayout.mzn data files, which this reader accepts unchanged; in that
// model the padding is excluded implicitly, because cellwidth's declared
// domain starts at the smallest non-negative width. Here it is excluded
// explicitly, in legal_configurations() below, which is the single place that
// knows about it.

#include <examples/dzn.hh>

#include <gcs/integer.hh>

#include <algorithm>
#include <cstddef>
#include <cstdint>
#include <random>
#include <stdexcept>
#include <string>
#include <tuple>
#include <vector>

namespace table_layout
{
    struct Instance
    {
        int rows = 0;
        int cols = 0;
        int maxconfig = 0;

        /// Budget for the total width of the layout: the column widths must sum
        /// to at most this.
        long pixelwidth = 0;

        /// width[r][c][l] and height[r][c][l] for l in 0 .. maxconfig - 1
        /// (MiniZinc's CONFIGS = 1 .. maxconfig). Negative entries are padding;
        /// see the file header.
        std::vector<std::vector<std::vector<long>>> width, height;

        std::string description;
    };

    /// The configurations that cell (r, c) actually has, as (l, width, height)
    /// triples with l the MiniZinc-style one-based configuration number. This is
    /// the only place that interprets the negative padding convention, and it is
    /// deliberately conservative: a configuration counts only if both its width
    /// and its height are non-negative.
    [[nodiscard]] inline auto legal_configurations(const Instance & inst, int r, int c) -> std::vector<std::tuple<long, long, long>>
    {
        std::vector<std::tuple<long, long, long>> result;
        for (int l = 0; l < inst.maxconfig; ++l)
            if (inst.width[r][c][l] >= 0 && inst.height[r][c][l] >= 0)
                result.emplace_back(l + 1, inst.width[r][c][l], inst.height[r][c][l]);
        return result;
    }

    /// Smallest and largest width and height over every legal configuration of
    /// every cell, which give the initial domains of the cell, row and column
    /// variables. Throws if some cell has no legal configuration at all.
    struct Extents
    {
        long min_width = 0, max_width = 0, min_height = 0, max_height = 0;
    };

    [[nodiscard]] inline auto extents(const Instance & inst) -> Extents
    {
        bool any = false;
        Extents e;
        for (int r = 0; r < inst.rows; ++r)
            for (int c = 0; c < inst.cols; ++c) {
                auto configs = legal_configurations(inst, r, c);
                if (configs.empty())
                    throw std::runtime_error{
                        "cell (" + std::to_string(r + 1) + ", " + std::to_string(c + 1) + ") has no legal configuration: every entry is padding"};
                for (const auto & [l, w, h] : configs) {
                    if (! any) {
                        e = Extents{w, w, h, h};
                        any = true;
                    }
                    e.min_width = std::min(e.min_width, w);
                    e.max_width = std::max(e.max_width, w);
                    e.min_height = std::min(e.min_height, h);
                    e.max_height = std::max(e.max_height, h);
                }
            }

        if (! any)
            throw std::runtime_error{"instance has no cells"};
        return e;
    }

    /// Generate an instance the way the Challenge data files look: every cell
    /// independently gets a uniformly random number of configurations between 1
    /// and maxconfig, and each configuration gets a width and a height drawn
    /// uniformly and independently from 1 .. max_cell_size. (The Challenge data
    /// really is uncorrelated in this way -- widths and heights within a cell
    /// are neither correlated nor sorted.)
    ///
    /// A pixelwidth of 0 means "choose one": cols * max_cell_size, matching the
    /// p1000_..._c10 Challenge instance, where each column can just about afford
    /// its widest cell.
    [[nodiscard]] inline auto make_random(int rows, int cols, int maxconfig, long pixelwidth, long max_cell_size, std::uint_fast32_t seed) -> Instance
    {
        if (rows < 1 || cols < 1)
            throw std::runtime_error{"rows and cols must be positive"};
        if (maxconfig < 1)
            throw std::runtime_error{"maxconfig must be positive"};
        if (max_cell_size < 1)
            throw std::runtime_error{"max-cell-size must be positive"};

        Instance inst;
        inst.rows = rows;
        inst.cols = cols;
        inst.maxconfig = maxconfig;
        inst.pixelwidth = pixelwidth > 0 ? pixelwidth : cols * max_cell_size;

        std::mt19937 rng{seed};
        std::uniform_int_distribution<int> how_many{1, maxconfig};
        std::uniform_int_distribution<long> size{1, max_cell_size};

        inst.width.assign(rows, std::vector<std::vector<long>>(cols, std::vector<long>(maxconfig, -1)));
        inst.height = inst.width;
        for (int r = 0; r < rows; ++r)
            for (int c = 0; c < cols; ++c) {
                auto n = how_many(rng);
                for (int l = 0; l < n; ++l) {
                    inst.width[r][c][l] = size(rng);
                    inst.height[r][c][l] = size(rng);
                }
            }

        inst.description = "random rows=" + std::to_string(rows) + " cols=" + std::to_string(cols) + " maxconfig=" + std::to_string(maxconfig) +
            " pixelwidth=" + std::to_string(inst.pixelwidth) + " max-cell-size=" + std::to_string(max_cell_size) + " seed=" + std::to_string(seed);
        return inst;
    }

    /// Read a TableLayout.mzn .dzn data file: the scalars pixelwidth, maxconfig,
    /// rows and cols, and the width and height arrays in row-major
    /// (ROWS, COLS, CONFIGS) order. The Challenge data writes the two arrays
    /// through an `array3d(ROWS, COLS, CONFIGS, [...])` wrapper, which the
    /// reader drops: the shape is given by the scalars, so it is checked
    /// against them below rather than taken from the literal.
    [[nodiscard]] inline auto read_dzn(const std::string & path) -> Instance
    {
        auto data = dzn::read(path);

        Instance inst;
        inst.pixelwidth = static_cast<long>(data.integer("pixelwidth"));
        inst.maxconfig = static_cast<int>(data.integer("maxconfig"));
        inst.rows = static_cast<int>(data.integer("rows"));
        inst.cols = static_cast<int>(data.integer("cols"));
        auto flat_width = data.integers("width"), flat_height = data.integers("height");

        if (inst.rows < 1 || inst.cols < 1 || inst.maxconfig < 1)
            throw std::runtime_error{"'" + path + "' does not give positive rows, cols and maxconfig"};
        auto expected = static_cast<std::size_t>(inst.rows) * inst.cols * inst.maxconfig;
        if (flat_width.size() != expected || flat_height.size() != expected)
            throw std::runtime_error{"'" + path + "' has width/height arrays of size " + std::to_string(flat_width.size()) + "/" +
                std::to_string(flat_height.size()) + ", expected " + std::to_string(expected)};

        inst.width.assign(inst.rows, std::vector<std::vector<long>>(inst.cols, std::vector<long>(inst.maxconfig, -1)));
        inst.height = inst.width;
        std::size_t at = 0;
        for (int r = 0; r < inst.rows; ++r)
            for (int c = 0; c < inst.cols; ++c)
                for (int l = 0; l < inst.maxconfig; ++l, ++at) {
                    inst.width[r][c][l] = static_cast<long>(flat_width[at]);
                    inst.height[r][c][l] = static_cast<long>(flat_height[at]);
                }

        inst.description = "dzn " + path + " rows=" + std::to_string(inst.rows) + " cols=" + std::to_string(inst.cols) +
            " maxconfig=" + std::to_string(inst.maxconfig) + " pixelwidth=" + std::to_string(inst.pixelwidth);
        return inst;
    }
}

#endif
