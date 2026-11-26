#include <gcs/innards/environment.hh>

#include <charconv>
#include <cstdio>
#include <cstdlib>
#include <optional>
#include <string_view>
#include <system_error>

#include <version>
#if defined(__cpp_lib_print) && defined(__cpp_lib_format)
#include <print>
using std::print;
#else
#include <fmt/core.h>
using fmt::print;
#endif

using std::nullopt;
using std::optional;
using std::string_view;

auto gcs::innards::parse_non_negative_count(string_view value) -> optional<unsigned long long>
{
    // from_chars into an unsigned type refuses a sign, and reports a value too
    // big to fit; checking where it stopped refuses trailing text.
    unsigned long long parsed = 0;
    auto [end, error] = std::from_chars(value.data(), value.data() + value.size(), parsed);
    if (value.empty() || error != std::errc{} || end != value.data() + value.size())
        return nullopt;
    return parsed;
}

auto gcs::innards::non_negative_count_from_environment(const char * name, unsigned long long default_value) -> unsigned long long
{
    const char * e = std::getenv(name);
    if (! e || ! *e)
        return default_value;

    if (auto parsed = parse_non_negative_count(e))
        return *parsed;

    print(stderr, "Ignoring unrecognised {} value '{}'\n", name, e);
    return default_value;
}
