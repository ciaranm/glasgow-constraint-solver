Notes on Tooling
================

This file contains notes I've made while I attempt to learn and apply modern tooling. It might be
useful for someone someday.

clang-format
------------

All source code is now formatted using ``clang-format``. It's mostly doing a decent job of things,
although there are areas where I haven't quite found the right combination of settings yet. I'm not
necessarily trying to get automatic formatting to match how I used to format code manually, just so
long as it looks consistent and readable.

I've found that Boost Program Options and its use of parentheses for lists upsets it. The best
workaround I've found is to add in comments, such as in the following. Without the trailing
comments, the parentheses will all end up on one line, which is awful.
```C++
    po::options_description display_options{"Program options"};
    display_options.add_options()            //
        ("help", "Display help information") //
        ("prove", "Create a proof")          //
        ("extra-constraints", "Use extra constraints described in the MiniCP paper");

```

In one place I've turned off formatting through a comment. I doubt an automatic formatting tool can
be clever enough to line up the following code to look like an addition:
```C++
    // clang-format off
    p.post(LinearEquality{ Linear{
                             {  1000_i, s }, {  100_i, e }, {  10_i, n }, {  1_i, d },
                             {  1000_i, m }, {  100_i, o }, {  10_i, r }, {  1_i, e },
            { -10000_i, m }, { -1000_i, o }, { -100_i, n }, { -10_i, e }, { -1_i, y }, }, 0_i });
    // clang-format on
```

The biggest problem I've had is with lambdas inside function arguments. The ``std::visit`` function
gives us a way of writing a ``switch``-like statement on a ``std::variant``, and ``overloaded`` is a
pattern which turns multiple lambdas into a single class with overloaded ``operator()`` methods. In
canonical C++ it would look something like this:
```C++
    return visit{overloaded {
            [] (const IntegerVariableConstantState &)   { return Integer{ 1 }; },
            [] (const IntegerVariableRangeState & r)    { return r.upper - r.lower + Integer{ 1 }; },
            [] (const IntegerVariableSmallSetState & s) { return Integer{ s.bits.popcount() }; },
            [] (const IntegerVariableSetState & s)      { return Integer(s.values->size()); }
            }, state_of(actual_var, space)};
```

I can't get ``clang-format`` to do anything even remotely reasonable here, particularly when some of
the lambdas span multiple lines. This is a common code pattern due to my overuse of
``std::variant``, so I've opted to put ``visit`` as a member inside ``overloaded``, allowing:
```C++
    return overloaded{
        [](const IntegerVariableConstantState &) { return Integer{1}; },
        [](const IntegerVariableRangeState & r) { return r.upper - r.lower + Integer{1}; },
        [](const IntegerVariableSmallSetState & s) { return Integer{s.bits.popcount()}; },
        [](const IntegerVariableSetState & s) { return Integer(s.values->size()); }}
        .visit(state_of(actual_var, space));
```
This isn't ideal, but it'll do for now.

Also, ``clang-format`` insists upon removing all of the spaces in
```C++
    list<vector<function<auto()->void>>> on_backtracks;
```
which I think should look more like
```C++
    list<vector<function<auto () -> void>>> on_backtracks;
```
and I've not figured out how to fix this...

Finally, the indenting of ``using enum`` inside a ``switch`` isn't great. I'd expect the following
not to be indented.
```C++
    switch (ilit.op) {
        using enum LiteralFromIntegerVariable::Operator;
    case Equal: return x.const_value == ilit.value;
    case NotEqual: return x.const_value != ilit.value;
    case GreaterEqual: return x.const_value >= ilit.value;
    case Less: return x.const_value < ilit.value;
    }
```

cmake
-----

Is terrible.

<!-- vim: set tw=100 spell spelllang=en : -->
