/*=============================================================================
 * parser for CSP instances represented in XCSP3 Format
 *
 * Copyright (c) 2015 xcsp.org (contact <at> xcsp.org)
 *
 * Permission is hereby granted, free of charge, to any person obtaining a copy
 * of this software and associated documentation files (the "Software"), to deal
 * in the Software without restriction, including without limitation the rights
 * to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
 * copies of the Software, and to permit persons to whom the Software is
 * furnished to do so, subject to the following conditions:
 *
 * The above copyright notice and this permission notice shall be included in
 * all copies or substantial portions of the Software.
 *
 * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
 * IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
 * FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
 * AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
 * LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
 * OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN
 * THE SOFTWARE.
 *=============================================================================
 */

#include "XCSP3Tree.h"

using namespace XCSP3Core;
using namespace std;

int main () {

    // Example 1 :
    Tree t("eq(z,add(x,3))");
    t.prefixe(); std::cout << std::endl;
    std::map<string, int> tuple;
    tuple["z"] = 4;
    tuple["x"] = 1;
    std::cout << "z=4 and x=1" << std::endl;
    std::cout << "result: " << t.evaluate(tuple) << std::endl;

    // Same variable appear many times
    Tree t2("eq(z,mul(x,x))");
    t2.prefixe(); std::cout << std::endl;
    std::map<string, int> tuple2;
    tuple2["z"] = 4;
    tuple2["x"] = 1;
    std::cout << "z=4 and x=1" << std::endl;
    std::cout << "result: " << t2.evaluate(tuple2) << std::endl;

    std::map<string, int> tuple3;
    tuple2["z"] = 4;
    tuple2["x"] = 2;
    std::cout << "z=4 and x=2" << std::endl;
    std::cout << "result: " << t2.evaluate(tuple3) << std::endl;

}
