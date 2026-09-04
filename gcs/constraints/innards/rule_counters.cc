#include <gcs/constraints/innards/rule_counters.hh>

#include <cstdlib>
#include <utility>

#include <version>
#if defined(__cpp_lib_print) && defined(__cpp_lib_format)
#include <print>
#else
#include <fmt/core.h>
#include <fmt/ostream.h>
#endif

#include <iostream>

using namespace gcs::innards;

using std::cerr;
using std::initializer_list;
using std::move;
using std::string;

#if defined(__cpp_lib_print) && defined(__cpp_lib_format)
using std::println;
#else
using fmt::println;
#endif

RuleInstrumentation::RuleInstrumentation(string prefix, initializer_list<const char *> names) :
    _prefix(move(prefix)), _names(names), _counters(names.size())
{
}

RuleInstrumentation::~RuleInstrumentation()
{
    if (! std::getenv("GCS_SCHEDULING_RULE_STATS"))
        return;

    // Every rule, including the ones that did nothing: a zero here is a
    // result. "This rule was switched on and never once moved a bound" is
    // exactly the finding that decides a default, and it would be invisible if
    // silent rules were skipped.
    for (std::size_t r = 0; r != _names.size(); ++r) {
        const auto & c = _counters[r];
        println(cerr, "{}_{}: calls={} firings={} already_true={} contradictions={}", _prefix, _names[r], c.calls, c.firings, c.already_true,
            c.contradictions);
    }
}
