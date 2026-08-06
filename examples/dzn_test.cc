// A unit test for dzn.hh, which the rest of examples/ is not: the programs
// here are end-to-end proof checks, and this is the one exception, because the
// reader's whole job is to fail rather than silently mis-read a benchmark
// instance and there is no proof that would catch it doing otherwise.
//
// Every rejection case below is one the reader used to *accept*, with a number
// in the answer and no complaint.

#include "dzn.hh"

#include <cstdlib>
#include <exception>
#include <filesystem>
#include <fstream>
#include <iostream>
#include <string>
#include <vector>

using std::cerr;
using std::string;
using std::to_string;
using std::vector;

namespace
{
    auto failures = 0;

    auto fail(const string & what) -> void
    {
        cerr << "dzn test failure: " << what << "\n";
        ++failures;
    }

    auto as_text(const vector<long long> & v) -> string
    {
        string s{"{"};
        for (const auto & x : v)
            s += " " + to_string(x);
        return s + " }";
    }

    auto expect(const string & what, const vector<long long> & got, const vector<long long> & want) -> void
    {
        if (got != want)
            fail(what + ": got " + as_text(got) + " but wanted " + as_text(want));
    }

    auto expect_rejected(const string & what, const auto & read_it) -> void
    {
        try {
            read_it();
        }
        catch (const std::exception &) {
            return;
        }
        fail(what + ": accepted, so it would have been read as something it is not");
    }
}

auto main(int, char *[]) -> int
{
    // In the working directory, like the proof files the other entries here
    // write, and with a name no other test uses.
    const string path = "dzn_test_data.dzn";
    {
        std::ofstream data{path};
        data << "% a comment, which is not a statement\n";
        data << "scalar = 7;\n";
        data << "flat = [1, 2, 3, 4];\n";
        data << "flat_wrapped = array1d(1..4, [5, 6, 7, 8]);\n";
        data << "flat_2d = [| 1, 2 | 3, 4 |];\n";
        data << "flat_empty = [];\n";
        data << "flat_trailing_comma = [1, 2, ];\n";
        data << "flat_negative = [-1, 2, -3];\n";
        data << "flat_junk = [1, 2abc, 3];\n";
        data << "grid = [| 1, 2, 3 | 4, 5, 6 |];\n";
        data << "grid_ragged = [| 1, 2 | 3 |];\n";
        data << "grid_junk = [| 1, 2x | 3, 4 |];\n";
        data << "groups = [ {1, 2}, {}, {3} ];\n";
        data << "groups_junk = [ {1, x} ];\n";
        data << "groups_outside = [ {1} 7 ];\n";
        data << "groups_stray_close = [ {1, 2} } 99 ];\n";
        data << "groups_unclosed = [ {1, 2 ];\n";
        if (! data)
            fail("could not write the test data file");
    }

    try {
        auto d = dzn::read(path);

        if (d.integer("scalar") != 7)
            fail("an integer scalar");
        if (! d.contains("flat") || d.contains("nothing_of_the_sort"))
            fail("contains()");

        expect("a flat array", d.integers("flat"), {1, 2, 3, 4});
        expect("an array1d wrapper, whose index set is not an entry", d.integers("flat_wrapped"), {5, 6, 7, 8});
        expect("negative entries", d.integers("flat_negative"), {-1, 2, -3});
        expect("an empty array", d.integers("flat_empty"), {});
        expect("a trailing comma, which is a separator with nothing after it", d.integers("flat_trailing_comma"), {1, 2});

        // The row bars become whitespace, so one entry can be separated from
        // the next by a bar rather than by a comma. Splitting on commas alone
        // made `2 | 3` a single entry, read the 2 out of it, and dropped the 3.
        expect("a 2-D literal read flat, which keeps every entry", d.integers("flat_2d"), {1, 2, 3, 4});

        auto grid = d.matrix("grid");
        if (grid.size() != 2)
            fail("a matrix's row count");
        else {
            expect("matrix row 0", grid[0], {1, 2, 3});
            expect("matrix row 1", grid[1], {4, 5, 6});
        }

        auto groups = d.sets("groups");
        if (groups.size() != 3)
            fail("an array of sets' count");
        else {
            expect("set 0", groups[0], {1, 2});
            expect("set 1, which is empty", groups[1], {});
            expect("set 2", groups[2], {3});
        }

        expect_rejected("a non-integer entry", [&] { return d.integers("flat_junk"); });
        expect_rejected("a non-integer matrix entry", [&] { return d.matrix("grid_junk"); });
        expect_rejected("a non-integer set member", [&] { return d.sets("groups_junk"); });
        expect_rejected("matrix rows of differing lengths", [&] { return d.matrix("grid_ragged"); });
        expect_rejected("something outside the braces", [&] { return d.sets("groups_outside"); });
        expect_rejected("a set that is never closed", [&] { return d.sets("groups_unclosed"); });

        // A `}` with nothing open took an unsigned brace counter to SIZE_MAX,
        // after which the outside-the-braces test never fired again and the
        // rest of the string was accepted --- so the check was switched off by
        // exactly the input it is there to catch.
        expect_rejected("a closing brace with nothing open", [&] { return d.sets("groups_stray_close"); });

        expect_rejected("a name the file does not define", [&] { return d.integer("absent"); });
        expect_rejected("an integer scalar with trailing text", [&] { return d.integer("flat"); });
    }
    catch (const std::exception & e) {
        fail(string{"unexpected exception: "} + e.what());
    }

    std::filesystem::remove(path);

    if (0 != failures) {
        cerr << "dzn test: " << failures << " failures\n";
        return EXIT_FAILURE;
    }

    cerr << "dzn test: every check passed\n";
    return EXIT_SUCCESS;
}
