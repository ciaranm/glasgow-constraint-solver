#include <gcs/problem.hh>
#include <gcs/solve.hh>

#include <iostream>
#include <soplex.h>
#include <string>

#include <boost/program_options.hpp>

using namespace gcs;

using namespace soplex;

using std::cerr;
using std::cout;
using std::endl;
using std::make_optional;
using std::nullopt;
using std::string;
using std::vector;

namespace po = boost::program_options;

auto main(int argc, char * argv[]) -> int
{
    SoPlex mysoplex;

    /* set parameters for exact solving */
    mysoplex.setIntParam(SoPlex::READMODE, SoPlex::READMODE_RATIONAL);
    mysoplex.setIntParam(SoPlex::SOLVEMODE, SoPlex::SOLVEMODE_RATIONAL);
    mysoplex.setIntParam(SoPlex::CHECKMODE, SoPlex::CHECKMODE_RATIONAL);
    mysoplex.setIntParam(SoPlex::SYNCMODE, SoPlex::SYNCMODE_AUTO);
    mysoplex.setRealParam(SoPlex::FEASTOL, 0.0);
    mysoplex.setRealParam(SoPlex::OPTTOL, 0.0);

    /* set the objective sense */
    mysoplex.setIntParam(SoPlex::OBJSENSE, SoPlex::OBJSENSE_MINIMIZE);

    /* we first add variables (the integer data is converted to type Rational) */
    DSVectorRational dummycol(0);
    mysoplex.addColRational(LPColRational(3, dummycol, infinity, 1));
    mysoplex.addColRational(LPColRational(2, dummycol, infinity, 1));

    /* then constraints one by one (here we show how Rationals can be used directly) */
    DSVectorRational row1(2);
    Rational r;
    r = 1;
    r /= 5;
    row1.add(0, r);
    r = 1;
    row1.add(1, r);
    r = 2;
    mysoplex.addRowRational(LPRowRational(r, row1, infinity));

    /* NOTE: alternatively, we could have added the matrix nonzeros in dummycol already; nonexisting rows are then
     * automatically created. */

    /* write LP in .lp format */
    mysoplex.writeFileRational("dump_rational.lp", NULL, NULL, NULL);

    /* solve LP */
    SPxSolver::Status stat;
    DVectorRational prim(2);
    DVectorRational dual(1);
    stat = mysoplex.optimize();

    /* get solution */
    if (stat == SPxSolver::OPTIMAL) {
        mysoplex.getPrimalRational(prim);
        mysoplex.getDualRational(dual);
        std::cout << "LP solved to optimality.\n";
        std::cout << "Objective value is " << mysoplex.objValueRational() << ".\n";
        std::cout << "Primal solution is [" << prim[0] << ", " << prim[1] << "].\n";
        std::cout << "Dual solution is [" << dual[0] << "].\n";
    }
    else {
        std::cout << "Error: SoPlex returned with status " << stat << ".\n";
    }
    return EXIT_SUCCESS;
}
