#ifndef GLASGOW_CONSTRAINT_SOLVER_GUARD_EXAMPLES_DZN_HH
#define GLASGOW_CONSTRAINT_SOLVER_GUARD_EXAMPLES_DZN_HH

// A small reader for MiniZinc `.dzn` data files, shared by the example
// programs. Header-only; not part of the library API.
//
// This handles the fragment of dzn the examples' data files actually use: a
// sequence of `name = value;` statements, `%` line comments, integer scalars,
// integer arrays in one and two dimensions, and arrays of integer sets. It is
// not a MiniZinc parser and does not try to be --- there are no expressions, no
// floats, no strings, no enums and no output items.
//
// Four examples (table_layout, seat_moving, nonogram, hitori) still carry their
// own readers, written before this existed and diverged in what they accept.
// Issue #664 tracks migrating them onto this; new examples should start here.

#include <cctype>
#include <cstddef>
#include <fstream>
#include <map>
#include <sstream>
#include <stdexcept>
#include <string>
#include <vector>

namespace dzn
{
    /// A parsed data file: the raw text of each `name = value` statement,
    /// comments removed, keyed by name. Values are left unparsed because what a
    /// value means depends on the model, not on the file.
    class Data
    {
    private:
        std::string _path;
        std::map<std::string, std::string> _values;

        [[nodiscard]] auto _raw(const std::string & name) const -> const std::string &
        {
            auto i = _values.find(name);
            if (i == _values.end())
                throw std::runtime_error{"'" + _path + "' does not define '" + name + "'"};
            return i->second;
        }

        [[noreturn]] auto _bad(const std::string & name, const std::string & why) const -> void
        {
            throw std::runtime_error{"'" + _path + "': " + name + " " + why};
        }

    public:
        Data(std::string path, std::map<std::string, std::string> values) : _path(std::move(path)), _values(std::move(values))
        {
        }

        [[nodiscard]] auto path() const -> const std::string &
        {
            return _path;
        }

        [[nodiscard]] auto contains(const std::string & name) const -> bool
        {
            return _values.contains(name);
        }

        /// An integer scalar.
        [[nodiscard]] auto integer(const std::string & name) const -> long long
        {
            const auto & text = _raw(name);
            std::istringstream in{text};
            long long value = 0;
            if (! (in >> value))
                _bad(name, "is not an integer: '" + text + "'");
            std::string trailing;
            if (in >> trailing)
                _bad(name, "has trailing text after the integer: '" + text + "'");
            return value;
        }

        /// A one-dimensional integer array. The `array1d(...)`, `array2d(...)`
        /// and `array3d(...)` wrappers are accepted and their index-set
        /// arguments ignored, so a wrapped array is read flat; use matrix() when
        /// the shape matters.
        [[nodiscard]] auto integers(const std::string & name) const -> std::vector<long long>
        {
            const auto & text = _raw(name);
            auto open = text.find('[');
            auto close = text.rfind(']');
            if (open == std::string::npos || close == std::string::npos || close < open)
                _bad(name, "is not an array: '" + text + "'");

            auto body = text.substr(open + 1, close - open - 1);
            // A 2-D literal is `[| a, b | c, d |]`; read flat, the row
            // separators are just more whitespace.
            for (auto & c : body)
                if (c == '|')
                    c = ' ';

            std::vector<long long> result;
            std::istringstream in{body};
            std::string item;
            while (std::getline(in, item, ',')) {
                std::istringstream one{item};
                long long value = 0;
                if (! (one >> value)) {
                    if (item.find_first_not_of(" \t\r\n") == std::string::npos)
                        continue;
                    _bad(name, "has a non-integer entry: '" + item + "'");
                }
                result.push_back(value);
            }
            return result;
        }

        /// A two-dimensional integer array written `[| a, b | c, d |]`, as
        /// `rows` rows of equal length. The row count is taken from the `|`
        /// separators rather than supplied, so a ragged literal is an error
        /// rather than a silent reshape.
        [[nodiscard]] auto matrix(const std::string & name) const -> std::vector<std::vector<long long>>
        {
            const auto & text = _raw(name);
            auto open = text.find('[');
            auto close = text.rfind(']');
            if (open == std::string::npos || close == std::string::npos || close < open)
                _bad(name, "is not an array: '" + text + "'");

            auto body = text.substr(open + 1, close - open - 1);
            auto first = body.find_first_not_of(" \t\r\n");
            if (first == std::string::npos || body[first] != '|')
                _bad(name, "is not a two-dimensional array literal: '" + text + "'");

            std::vector<std::vector<long long>> rows;
            std::istringstream in{body};
            std::string row;
            // The literal both opens and closes with '|', so splitting on it
            // gives an empty piece at each end; both are skipped as blank.
            while (std::getline(in, row, '|')) {
                if (row.find_first_not_of(" \t\r\n") == std::string::npos)
                    continue;
                std::vector<long long> entries;
                std::istringstream cells{row};
                std::string item;
                while (std::getline(cells, item, ',')) {
                    std::istringstream one{item};
                    long long value = 0;
                    if (! (one >> value)) {
                        if (item.find_first_not_of(" \t\r\n") == std::string::npos)
                            continue;
                        _bad(name, "has a non-integer entry: '" + item + "'");
                    }
                    entries.push_back(value);
                }
                rows.push_back(std::move(entries));
            }

            for (const auto & r : rows)
                if (r.size() != rows.front().size())
                    _bad(name, "has rows of differing lengths");
            return rows;
        }

        /// An array of integer sets, `[ {1, 2}, {}, {3} ]`. Each set comes back
        /// in the order written; nothing is sorted or deduplicated, because a
        /// model that cares can do either and one that does not should not pay
        /// for it.
        [[nodiscard]] auto sets(const std::string & name) const -> std::vector<std::vector<long long>>
        {
            const auto & text = _raw(name);
            auto open = text.find('[');
            auto close = text.rfind(']');
            if (open == std::string::npos || close == std::string::npos || close < open)
                _bad(name, "is not an array: '" + text + "'");

            std::vector<std::vector<long long>> result;
            auto body = text.substr(open + 1, close - open - 1);
            std::size_t at = 0;
            while (true) {
                auto brace = body.find('{', at);
                if (brace == std::string::npos)
                    break;
                auto end = body.find('}', brace);
                if (end == std::string::npos)
                    _bad(name, "has a set that is never closed");

                std::vector<long long> members;
                std::istringstream in{body.substr(brace + 1, end - brace - 1)};
                std::string item;
                while (std::getline(in, item, ',')) {
                    std::istringstream one{item};
                    long long value = 0;
                    if (! (one >> value)) {
                        if (item.find_first_not_of(" \t\r\n") == std::string::npos)
                            continue;
                        _bad(name, "has a non-integer set member: '" + item + "'");
                    }
                    members.push_back(value);
                }
                result.push_back(std::move(members));
                at = end + 1;
            }

            // Anything outside the braces other than separators means this is
            // not an array of sets, and reading it as one would quietly drop it.
            for (std::size_t i = 0, brace_depth = 0; i != body.size(); ++i) {
                if (body[i] == '{')
                    ++brace_depth;
                else if (body[i] == '}')
                    --brace_depth;
                else if (0 == brace_depth && ',' != body[i] && ! std::isspace(static_cast<unsigned char>(body[i])))
                    _bad(name, "is not an array of sets: '" + text + "'");
            }
            return result;
        }
    };

    /// Read a `.dzn` file. Line comments are stripped, then the text is split
    /// into `name = value;` statements. A statement without an `=` is ignored
    /// rather than rejected, so a data file carrying an `output` item or a
    /// bare `;` still reads.
    [[nodiscard]] inline auto read(const std::string & path) -> Data
    {
        std::ifstream infile{path};
        if (! infile)
            throw std::runtime_error{"cannot read '" + path + "'"};

        std::string text, line;
        while (std::getline(infile, line)) {
            auto comment = line.find('%');
            text += (comment == std::string::npos ? line : line.substr(0, comment));
            text += '\n';
        }

        auto trim = [](const std::string & s) -> std::string {
            auto first = s.find_first_not_of(" \t\r\n");
            if (first == std::string::npos)
                return {};
            return s.substr(first, s.find_last_not_of(" \t\r\n") - first + 1);
        };

        std::map<std::string, std::string> values;
        std::size_t pos = 0;
        while (true) {
            auto end = text.find(';', pos);
            if (end == std::string::npos)
                break;
            auto statement = text.substr(pos, end - pos);
            pos = end + 1;

            auto eq = statement.find('=');
            if (eq == std::string::npos)
                continue;
            auto name = trim(statement.substr(0, eq));
            if (name.empty())
                continue;
            if (! values.emplace(name, trim(statement.substr(eq + 1))).second)
                throw std::runtime_error{"'" + path + "' defines '" + name + "' twice"};
        }

        return Data{path, std::move(values)};
    }
}

#endif
