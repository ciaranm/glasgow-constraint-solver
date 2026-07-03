// Temporary CI probe: confirm the C++23 library features we want to start using
// are available on every supported toolchain (Ubuntu 24.04/26.04 GCC, macOS
// libc++). This file is not part of the real build and will be removed once the
// answer is recorded.

#include <optional>
#include <vector>
#include <version>

// std::optional monadic operations (P0798R8, C++23): and_then / transform / or_else.
static_assert(__cpp_lib_optional >= 202110L, "std::optional monadic operations (and_then/transform/or_else) unavailable");

// Ranges support for containers (P1206R7, C++23): std::vector::append_range et al.
static_assert(__cpp_lib_containers_ranges >= 202202L, "std::vector::append_range (containers-ranges) unavailable");

auto probe_optional_monadic(std::optional<int> a, std::optional<int> b) -> int
{
    auto r = a.transform([](int x) { return x * 10; })
                 .and_then([](int x) -> std::optional<int> { return x > 0 ? std::optional<int>{x} : std::nullopt; })
                 .or_else([&]() -> std::optional<int> { return b; });
    return r.value_or(-1);
}

auto probe_append_range(std::vector<int> a, const std::vector<int> & b) -> std::vector<int>
{
    a.append_range(b);
    return a;
}

auto main() -> int
{
    return probe_optional_monadic(std::optional<int>{3}, std::nullopt) + static_cast<int>(probe_append_range({1, 2}, {3, 4}).size());
}
