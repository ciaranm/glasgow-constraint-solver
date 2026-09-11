# Code style

`clang-format` settles the mechanical questions — indentation, wrapping,
spacing — and `CONTRIBUTING.md` covers how to run it and the pre-commit hook
that checks it. This document covers the conventions it does *not* enforce:
things the formatter is happy either way about, but which the tree does
consistently one way.

Each of these is a convention the whole tree already follows, so the right move
when in doubt is to copy the nearest existing file rather than to reason from
first principles.

## `using` declarations

The `using` declarations block near the top of each `.cc` file is sorted
**alphabetically by name**, with the `std::ranges::` names in a group of their
own **after** all the plain `std::` ones, themselves alphabetical:

```cpp
using std::pair;
using std::string;
using std::vector;
using std::ranges::any_of;
using std::ranges::sort;
```

Every one of the 57 files that names a `std::ranges::` algorithm does it this
way. In particular, do not sort `std::ranges::sort` under 'r', between
`std::pair` and `std::string`: nothing in the tree does that.

The `#if defined(__cpp_lib_print)` block that picks `std::print` / `fmt::print`
is a separate block and stays where it is, below.

## Ranges algorithms

When replacing a classic algorithm with its `std::ranges::` equivalent:

- Remove `using std::foo;`
- Add `using std::ranges::foo;` to the `std::ranges::` group below the plain
  `std::` ones, in alphabetical order within that group (see above)
- Leave the call site **unqualified** — do not write `std::ranges::sort(v)` at
  the call site

## `using enum`

Place `using enum SomeEnum;` on the **first line inside the switch body**,
indented one level past the `switch` keyword, before the first `case` label:

```cpp
switch (x) {
    using enum SomeEnum;
case Value1:
```

Watch for an enumerator that shadows a class of the same name once it is
unqualified; `search_heuristics.cc` has a case label qualified for exactly that
reason, with a comment saying so.

## `overloaded{...}` visitor blocks

Format `overloaded{...}` visitors like a `switch`: nothing after the opening
brace, each lambda starting on its own line at one indent level, all lambdas
indented equally. Pin the layout with an empty `//` comment straight after the
opening brace:

```cpp
overloaded{//
    [&](const consistency::GAC &) {
        // ...
    },
    [&](const consistency::VC &) {
        // ...
    }}
    .visit(_level);
```

The pin is load-bearing. clang-format's penalty optimiser will otherwise pull
the first lambda up onto the `overloaded{` line whenever the content happens to
make that layout score better, and it re-mangles a previously-clean block when
the lambda bodies change — so an unpinned block that looks stable today is one
edit away from being reflowed. When you meet an already-mangled block, add the
`//` and re-run clang-format rather than re-indenting by hand.

The same trick keeps cxxopts `add_options` blocks one option per line: a
trailing `//` on each line.

## `std::format` / `fmt::format`

The compiler's own `<format>` and `<print>` are used where available, and
libfmt is fetched as a fallback where they are not (see
[building.md](building.md)). A file that uses `format()` for string building
must therefore use the conditional pattern:

```cpp
#if defined(__cpp_lib_print) && defined(__cpp_lib_format)
#include <format>
using std::format;
#else
#include <fmt/core.h>
using fmt::format;
#endif
```

**Both** macros, not just `__cpp_lib_print`: all 348 guards in the tree test
both, and a guard that tests only one will break on a standard library that has
one and not the other. Add `#include <format>` in the same `#if` block as
`#include <print>` where both are needed.

## See also

- `CONTRIBUTING.md` — clang-format version, how to run it, the pre-commit hook
- [building.md](building.md) — which standard-library features are available on
  which supported toolchain
