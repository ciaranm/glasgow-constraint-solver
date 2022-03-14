/*=============================================================================
 * parser for CSP instances represented in XCSP3 Format
 *
 * Copyright (c) 2015 xcsp.org (contact <at> xcsp.org)
 * Copyright (c) 2008 Olivier ROUSSEL (olivier.roussel <at> cril.univ-artois.fr)
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
#ifndef COSOCO_XCSP3SummaryCallbacks_H
#define COSOCO_XCSP3SummaryCallbacks_H

#include <XCSP3Tree.h>
#include "XCSP3CoreCallbacks.h"
#include "XCSP3Variable.h"
/**
 * This is an example that prints useful informations of a XCSP3 instance.
 * You need to create your own class and to override functions of the callback.
 * We suggest to make a map between XVariable and your own variables in order to
 * facilitate the constructions of constraints.
 *
 * see main.cc to show declaration of the parser
 *
 */

namespace XCSP3Core {

    class XCSP3SummaryCallbacks : public XCSP3CoreCallbacks {
    public:
        int nbv, nbc;
        string minmax,type;

        XCSP3SummaryCallbacks();

        virtual void beginInstance(InstanceType type) override;

        virtual void endInstance() override;

        virtual void beginVariables() override;

        virtual void endVariables() override;

        virtual void beginVariableArray(string id) override;

        virtual void endVariableArray() override;

        virtual void beginConstraints() override;

        virtual void endConstraints() override;

        virtual void beginGroup(string id) override;

        virtual void endGroup() override;

        virtual void beginBlock(string classes) override;

        virtual void endBlock() override;

        virtual void beginSlide(string id, bool circular) override;

        virtual void endSlide() override;

        virtual void beginObjectives() override;

        virtual void endObjectives() override;

        virtual void beginAnnotations() override;

        virtual void endAnnotations() override;

        virtual void buildVariableInteger(string id, int minValue, int maxValue) override;

        virtual void buildVariableInteger(string id, vector<int> &values) override;

        virtual void buildConstraintExtension(string id, vector<XVariable *> list, vector<vector<int>> &tuples, bool support, bool hasStar) override;

        virtual void buildConstraintExtension(string id, XVariable *variable, vector<int> &tuples, bool support, bool hasStar) override;

        virtual void buildConstraintExtensionAs(string id, vector<XVariable *> list, bool support, bool hasStar) override;

        virtual void buildConstraintIntension(string id, string expr) override;

        virtual void buildConstraintIntension(string id, Tree *tree) override;

        virtual void buildConstraintPrimitive(string id, OrderType op, XVariable *x, int k, XVariable *y) override;

        virtual void buildConstraintPrimitive(string id, OrderType op, XVariable *x, int k) override;

        virtual void buildConstraintPrimitive(string id, XVariable *x,  bool in, int min, int max) override;

        virtual void buildConstraintRegular(string id, vector<XVariable *> &list, string st, vector<string> &final, vector<XTransition> &transitions) override;

        virtual void buildConstraintMDD(string id, vector<XVariable *> &list, vector<XTransition> &transitions) override;

        virtual void buildConstraintAlldifferent(string id, vector<XVariable *> &list) override;

        virtual void buildConstraintAlldifferentExcept(string id, vector<XVariable *> &list, vector<int> &except) override;

        virtual void buildConstraintAlldifferent(string id, vector<Tree *> &list) override;

        virtual void buildConstraintAlldifferentList(string id, vector<vector<XVariable *>> &lists) override;

        virtual void buildConstraintAlldifferentMatrix(string id, vector<vector<XVariable *>> &matrix) override;

        virtual void buildConstraintAllEqual(string id, vector<XVariable *> &list) override;

        virtual void buildConstraintNotAllEqual(string id, vector<XVariable *> &list) override;

        virtual void buildConstraintOrdered(string id, vector<XVariable *> &list, OrderType order) override;

        virtual void buildConstraintOrdered(string id, vector<XVariable *> &list, vector<int> &lengths, OrderType order) override;

        virtual void buildConstraintLex(string id, vector<vector<XVariable *>> &lists, OrderType order) override;

        virtual void buildConstraintLexMatrix(string id, vector<vector<XVariable *>> &matrix, OrderType order) override;

        virtual void buildConstraintSum(string id, vector<XVariable *> &list, vector<int> &coeffs, XCondition &cond) override;

        virtual void buildConstraintSum(string id, vector<XVariable *> &list, XCondition &cond) override;

        virtual void buildConstraintSum(string id, vector<XVariable *> &list, vector<XVariable *> &coeffs, XCondition &cond) override;

        virtual void buildConstraintSum(string id, vector<Tree *> &list, vector<int> &coeffs, XCondition &cond) override;

        virtual void buildConstraintSum(string id, vector<Tree *> &list, XCondition &cond) override;

        virtual void buildConstraintAtMost(string id, vector<XVariable *> &list, int value, int k) override;

        virtual void buildConstraintAtLeast(string id, vector<XVariable *> &list, int value, int k) override;

        virtual void buildConstraintExactlyK(string id, vector<XVariable *> &list, int value, int k) override;

        virtual void buildConstraintAmong(string id, vector<XVariable *> &list, vector<int> &values, int k) override;

        virtual void buildConstraintExactlyVariable(string id, vector<XVariable *> &list, int value, XVariable *x) override;

        virtual void buildConstraintCount(string id, vector<XVariable *> &list, vector<int> &values, XCondition &xc) override;

        virtual void buildConstraintCount(string id, vector<XVariable *> &list, vector<XVariable *> &values, XCondition &xc) override;

        virtual void buildConstraintNValues(string id, vector<XVariable *> &list, vector<int> &except, XCondition &xc) override;

        virtual void buildConstraintNValues(string id, vector<XVariable *> &list, XCondition &xc) override;

        virtual void buildConstraintCardinality(string id, vector<XVariable *> &list, vector<int> values, vector<int> &occurs, bool closed) override;

        virtual void buildConstraintCardinality(string id, vector<XVariable *> &list, vector<int> values, vector<XVariable *> &occurs,
                                                bool closed) override;

        virtual void buildConstraintCardinality(string id, vector<XVariable *> &list, vector<int> values, vector<XInterval> &occurs,
                                                bool closed) override;

        virtual void buildConstraintCardinality(string id, vector<XVariable *> &list, vector<XVariable *> values, vector<int> &occurs,
                                                bool closed) override;

        virtual void buildConstraintCardinality(string id, vector<XVariable *> &list, vector<XVariable *> values, vector<XVariable *> &occurs,
                                                bool closed) override;

        virtual void buildConstraintCardinality(string id, vector<XVariable *> &list, vector<XVariable *> values, vector<XInterval> &occurs,
                                                bool closed) override;

        virtual void buildConstraintCumulative(string id, vector<XVariable *> &origins, vector<int> &lengths, vector<int> &heights, vector<XVariable *> &ends,
                                               XCondition &xc) override;

        virtual void buildConstraintMinimum(string id, vector<XVariable *> &list, XCondition &xc) override;

        virtual void buildConstraintMinimum(string id, vector<XVariable *> &list, XVariable *index, int startIndex, RankType rank,
                                            XCondition &xc) override;

        virtual void buildConstraintMaximum(string id, vector<XVariable *> &list, XCondition &xc) override;

        virtual void buildConstraintMaximum(string id, vector<XVariable *> &list, XVariable *index, int startIndex, RankType rank,
                                            XCondition &xc) override;

        virtual void buildConstraintElement(string id, vector<XVariable *> &list, int value) override;

        virtual void buildConstraintElement(string id, vector<XVariable *> &list, XVariable *value) override;

        virtual void buildConstraintElement(string id, vector<XVariable *> &list, int startIndex, XVariable *index, RankType rank, int value) override;

        virtual void buildConstraintElement(string id, vector<XVariable *> &list, int startIndex, XVariable *index, RankType rank, XVariable *value) override;

        virtual void buildConstraintElement(string id, vector<int> &list, int startIndex, XVariable *index, RankType rank, XVariable *value) override;

        virtual void buildConstraintElement(string id, vector<vector<int> > &matrix, int startRowIndex, XVariable *rowIndex, int startColIndex, XVariable* colIndex, XVariable *value) override;

        virtual void buildConstraintChannel(string id, vector<XVariable *> &list, int startIndex) override;

        virtual void buildConstraintChannel(string id, vector<XVariable *> &list1, int startIndex1, vector<XVariable *> &list2, int startIndex2) override;

        virtual void buildConstraintChannel(string id, vector<XVariable *> &list, int startIndex, XVariable *value) override;

        virtual void buildConstraintStretch(string id, vector<XVariable *> &list, vector<int> &values, vector<XInterval> &widths) override;

        virtual void
        buildConstraintStretch(string id, vector<XVariable *> &list, vector<int> &values, vector<XInterval> &widths, vector<vector<int>> &patterns) override;

        virtual void buildConstraintNoOverlap(string id, vector<XVariable *> &origins, vector<int> &lengths, bool zeroIgnored) override;

        virtual void buildConstraintNoOverlap(string id, vector<XVariable *> &origins, vector<XVariable *> &lengths, bool zeroIgnored) override;

        virtual void buildConstraintNoOverlap(string id, vector<vector<XVariable *>> &origins, vector<vector<int>> &lengths, bool zeroIgnored) override;

        virtual void buildConstraintNoOverlap(string id, vector<vector<XVariable *>> &origins, vector<vector<XVariable *>> &lengths, bool zeroIgnored) override;

        virtual void buildConstraintInstantiation(string id, vector<XVariable *> &list, vector<int> &values) override;

        virtual void buildConstraintClause(string id, vector<XVariable *> &positive, vector<XVariable *> &negative) override ;

        virtual void buildConstraintCircuit(string id, vector<XVariable *> &list, int startIndex) override;


        virtual void buildConstraintCircuit(string id, vector<XVariable *> &list, int startIndex, int size) override;


        virtual void buildConstraintCircuit(string id, vector<XVariable *> &list, int startIndex, XVariable *size) override;


        virtual void buildObjectiveMinimizeExpression(string expr) override;

        virtual void buildObjectiveMaximizeExpression(string expr) override;


        virtual void buildObjectiveMinimizeVariable(XVariable *x) override;


        virtual void buildObjectiveMaximizeVariable(XVariable *x) override;


        virtual void buildObjectiveMinimize(ExpressionObjective type, vector<XVariable *> &list, vector<int> &coefs) override;


        virtual void buildObjectiveMaximize(ExpressionObjective type, vector<XVariable *> &list, vector<int> &coefs) override;


        virtual void buildObjectiveMinimize(ExpressionObjective type, vector<XVariable *> &list) override;


        virtual void buildObjectiveMaximize(ExpressionObjective type, vector<XVariable *> &list) override;


        virtual void buildAnnotationDecision(vector<XVariable*> &list) override;
        bool canonize;

        void buildConstraintMaximum(string id, vector<Tree*> &list, XCondition &xc) {
            nbc++;
        }

        void buildConstraintMinimum(string id, vector<Tree*> &list, XCondition &xc) {
            nbc++;
        }

        virtual void buildConstraintMult(string id, XVariable *x, XVariable *y, XVariable *z) {
            nbc++;
        }




        virtual void buildObjectiveMinimize(ExpressionObjective t, vector<Tree *> &trees, vector<int> &coefs) {
            type = "sum";
            minmax = "Minimize";
        }

        virtual void buildConstraintCumulative(string id, vector<XVariable *> &origins, vector<int> &lengths, vector<int> &heights, XCondition &xc) {
            nbc++;
        }


        };


}

using namespace XCSP3Core;


XCSP3SummaryCallbacks::XCSP3SummaryCallbacks() : XCSP3CoreCallbacks(), canonize(true) {nbv=0;nbc=0;}





void XCSP3SummaryCallbacks::beginInstance(InstanceType _type) {
    if(_type == InstanceType::CSP) {
        minmax= "";
        type = "";
    }
}


void XCSP3SummaryCallbacks::endInstance() {
    std::cout << nbv << " " << nbc << " " << minmax << " " << type << std::endl;
}


void XCSP3SummaryCallbacks::beginVariables() {
}


void XCSP3SummaryCallbacks::endVariables() {
}


void XCSP3SummaryCallbacks::beginVariableArray(string id) {
}


void XCSP3SummaryCallbacks::endVariableArray() {
}


void XCSP3SummaryCallbacks::beginConstraints() {
}


void XCSP3SummaryCallbacks::endConstraints() {
}


void XCSP3SummaryCallbacks::beginGroup(string id) {
}


void XCSP3SummaryCallbacks::endGroup() {
}


void XCSP3SummaryCallbacks::beginBlock(string classes) {
}


void XCSP3SummaryCallbacks::endBlock() {
}


// string id, bool circular
void XCSP3SummaryCallbacks::beginSlide(string id, bool) {
}


void XCSP3SummaryCallbacks::endSlide() {
}


void XCSP3SummaryCallbacks::beginObjectives() {
}


void XCSP3SummaryCallbacks::endObjectives() {
}


void XCSP3SummaryCallbacks::beginAnnotations() {
}


void XCSP3SummaryCallbacks::endAnnotations() {
}


void XCSP3SummaryCallbacks::buildVariableInteger(string id, int minValue, int maxValue) {
    nbv++;
}


void XCSP3SummaryCallbacks::buildVariableInteger(string id, vector<int> &values) {
    nbv++;
}


void XCSP3SummaryCallbacks::buildConstraintExtension(string id, vector<XVariable *> list, vector<vector<int>> &tuples, bool support, bool hasStar) {
    nbc++;
}


void XCSP3SummaryCallbacks::buildConstraintExtension(string id, XVariable *variable, vector<int> &tuples, bool support, bool hasStar) {
    nbc++;
}


// string id, vector<XVariable *> list, bool support, bool hasStar
void XCSP3SummaryCallbacks::buildConstraintExtensionAs(string id, vector<XVariable *>, bool, bool) {
nbc++;
}


void XCSP3SummaryCallbacks::buildConstraintIntension(string id, string expr) {
    nbc++;
}


void XCSP3SummaryCallbacks::buildConstraintIntension(string id, Tree *tree) {
    nbc++;
}


void XCSP3SummaryCallbacks::buildConstraintPrimitive(string id, OrderType, XVariable *x, int k, XVariable *y) {
    nbc++;
}


void XCSP3SummaryCallbacks::buildConstraintPrimitive(string id, OrderType op, XVariable *x, int k) {
    nbc++;
}

void XCSP3SummaryCallbacks::buildConstraintPrimitive(string id, XVariable *x, bool in, int min, int max) {
    nbc++;
}


// string id, vector<XVariable *> &list, string start, vector<string> &final, vector<XTransition> &transitions
void XCSP3SummaryCallbacks::buildConstraintRegular(string, vector<XVariable *> &list, string start, vector<string> &final, vector<XTransition> &transitions) {
    nbc++;
}


// string id, vector<XVariable *> &list, vector<XTransition> &transitions
void XCSP3SummaryCallbacks::buildConstraintMDD(string, vector<XVariable *> &list, vector<XTransition> &transitions) {
    nbc++;
}


void XCSP3SummaryCallbacks::buildConstraintAlldifferent(string id, vector<XVariable *> &list) {
    nbc++;
}


void XCSP3SummaryCallbacks::buildConstraintAlldifferentExcept(string id, vector<XVariable *> &list, vector<int> &except) {
    nbc++;
}


void XCSP3SummaryCallbacks::buildConstraintAlldifferent(string id, vector<Tree *> &list) {
    nbc++;
}

void XCSP3SummaryCallbacks::buildConstraintAlldifferentList(string id, vector<vector<XVariable *>> &lists) {
    nbc++;
}


void XCSP3SummaryCallbacks::buildConstraintAlldifferentMatrix(string id, vector<vector<XVariable *>> &matrix) {
    nbc++;
}


void XCSP3SummaryCallbacks::buildConstraintAllEqual(string id, vector<XVariable *> &list) {
    nbc++;
}


void XCSP3SummaryCallbacks::buildConstraintNotAllEqual(string id, vector<XVariable *> &list) {
    nbc++;
}


// string id, vector<XVariable *> &list, OrderType order
void XCSP3SummaryCallbacks::buildConstraintOrdered(string, vector<XVariable *> &list, OrderType order) {
    nbc++;
}

// string id, vector<XVariable *> &list, vector<int> &lengths, OrderType order
void XCSP3SummaryCallbacks::buildConstraintOrdered(string, vector<XVariable *> &list, vector<int> &lengths, OrderType order) {
    nbc++;
}

// string id, vector<vector<XVariable *>> &lists, OrderType order
void XCSP3SummaryCallbacks::buildConstraintLex(string, vector<vector<XVariable *>> &lists, OrderType order) {
    nbc++;
}


// string id, vector<vector<XVariable *>> &matrix, OrderType order
void XCSP3SummaryCallbacks::buildConstraintLexMatrix(string, vector<vector<XVariable *>> &matrix, OrderType order) {
    nbc++;
}


// string id, vector<XVariable *> &list, vector<int> &coeffs, XCondition &cond
void XCSP3SummaryCallbacks::buildConstraintSum(string, vector<XVariable *> &list, vector<int> &coeffs, XCondition &cond) {
    nbc++;
}


// string id, vector<XVariable *> &list, XCondition &cond
void XCSP3SummaryCallbacks::buildConstraintSum(string, vector<XVariable *> &list, XCondition &cond) {
    nbc++;
}


// string id, vector<XVariable *> &list, vector<XVariable *> &coeffs, XCondition &cond
void XCSP3SummaryCallbacks::buildConstraintSum(string, vector<XVariable *> &list, vector<XVariable *> &coeffs, XCondition &cond) {
    nbc++;
}


void XCSP3SummaryCallbacks::buildConstraintSum(string id, vector<Tree *> &list, vector<int> &coeffs, XCondition &cond) {
    nbc++;
}

void XCSP3SummaryCallbacks::buildConstraintSum(string id, vector<Tree *> &list, XCondition &cond) {
    nbc++;
}



// string id, vector<XVariable *> &list, int value, int k
void XCSP3SummaryCallbacks::buildConstraintAtMost(string, vector<XVariable *> &list, int value, int k) {
    nbc++;
}


// string id, vector<XVariable *> &list, int value, int k
void XCSP3SummaryCallbacks::buildConstraintAtLeast(string, vector<XVariable *> &list, int value, int k) {
    nbc++;
}


// string id, vector<XVariable *> &list, int value, int k
void XCSP3SummaryCallbacks::buildConstraintExactlyK(string, vector<XVariable *> &list, int value, int k) {
    nbc++;
}


// string id, vector<XVariable *> &list, vector<int> &values, int k
void XCSP3SummaryCallbacks::buildConstraintAmong(string, vector<XVariable *> &list, vector<int> &values, int k) {
    nbc++;
}


// string id, vector<XVariable *> &list, int value, XVariable *x
void XCSP3SummaryCallbacks::buildConstraintExactlyVariable(string, vector<XVariable *> &list, int value, XVariable *x) {
    nbc++;
}


// string id, vector<XVariable *> &list, vector<int> &values, XCondition &xc
void XCSP3SummaryCallbacks::buildConstraintCount(string, vector<XVariable *> &list, vector<int> &values, XCondition &xc) {
    nbc++;
}


// string id, vector<XVariable *> &list, vector<XVariable *> &values, XCondition &xc
void XCSP3SummaryCallbacks::buildConstraintCount(string, vector<XVariable *> &list, vector<XVariable *> &values, XCondition &xc) {
    nbc++;
}


// string id, vector<XVariable *> &list, vector<int> &except, XCondition &xc
void XCSP3SummaryCallbacks::buildConstraintNValues(string, vector<XVariable *> &list, vector<int> &except, XCondition &xc) {
    nbc++;
}


// string id, vector<XVariable *> &list, XCondition &xc
void XCSP3SummaryCallbacks::buildConstraintNValues(string, vector<XVariable *> &list, XCondition &xc) {
    nbc++;
}


// string id, vector<XVariable *> &list, vector<int> values, vector<int> &occurs, bool closed
void XCSP3SummaryCallbacks::buildConstraintCardinality(string, vector<XVariable *> &list, vector<int> values, vector<int> &occurs, bool closed) {
    nbc++;
}


// string id, vector<XVariable *> &list, vector<int> values, vector<XVariable *> &occurs, bool closed
void XCSP3SummaryCallbacks::buildConstraintCardinality(string, vector<XVariable *> &list, vector<int> values, vector<XVariable *> &occurs, bool closed) {
    nbc++;
}


// string id, vector<XVariable *> &list, vector<int> values, vector<XInterval> &occurs, bool closed
void XCSP3SummaryCallbacks::buildConstraintCardinality(string, vector<XVariable *> &list, vector<int> values, vector<XInterval> &occurs, bool closed) {
    nbc++;
}


// string id, vector<XVariable *> &list, vector<XVariable *> values, vector<int> &occurs, bool closed
void XCSP3SummaryCallbacks::buildConstraintCardinality(string, vector<XVariable *> &list, vector<XVariable *> values, vector<int> &occurs, bool closed) {
    nbc++;
}


// string id, vector<XVariable *> &list, vector<XVariable *> values, vector<XVariable *> &occurs, bool closed
void XCSP3SummaryCallbacks::buildConstraintCardinality(string, vector<XVariable *> &list, vector<XVariable *> values, vector<XVariable *> &occurs, bool closed) {
    nbc++;
}


// string id, vector<XVariable *> &list, vector<XVariable *> values, vector<XInterval> &occurs, bool closed
void XCSP3SummaryCallbacks::buildConstraintCardinality(string, vector<XVariable *> &list, vector<XVariable *> values, vector<XInterval> &occurs, bool closed) {
    nbc++;
}


// string id, vector<XVariable *> &list, XCondition &xc
void XCSP3SummaryCallbacks::buildConstraintMinimum(string, vector<XVariable *> &list, XCondition &xc) {
    nbc++;
}


// string id, vector<XVariable *> &list, XVariable *index, int startIndex, RankType rank, XCondition &xc
void XCSP3SummaryCallbacks::buildConstraintMinimum(string, vector<XVariable *> &list, XVariable *index, int startIndex, RankType, XCondition &xc) {
    nbc++;
}


// string id, vector<XVariable *> &list, XCondition &xc
void XCSP3SummaryCallbacks::buildConstraintMaximum(string, vector<XVariable *> &list, XCondition &xc) {
    nbc++;
}


// string id, vector<XVariable *> &list, XVariable *index, int startIndex, RankType rank, XCondition &xc
void XCSP3SummaryCallbacks::buildConstraintMaximum(string, vector<XVariable *> &list, XVariable *index, int startIndex, RankType, XCondition &xc) {
    nbc++;
}


// string id, vector<XVariable *> &list, int value
void XCSP3SummaryCallbacks::buildConstraintElement(string, vector<XVariable *> &list, int value) {
    nbc++;
}


// string id, vector<XVariable *> &list, XVariable *value
void XCSP3SummaryCallbacks::buildConstraintElement(string, vector<XVariable *> &list, XVariable *value) {
    nbc++;
}


// string id, vector<XVariable *> &list, int startIndex, XVariable *index, RankType rank, int value
void XCSP3SummaryCallbacks::buildConstraintElement(string, vector<XVariable *> &list, int startIndex, XVariable *index, RankType, int value) {
    nbc++;
}

void XCSP3SummaryCallbacks::buildConstraintElement(string id, vector<vector<int> > &matrix, int startRowIndex, XVariable *rowIndex, int startColIndex, XVariable* colIndex, XVariable *value) {
    nbc++;
}

// string id, vector<XVariable *> &list, int startIndex, XVariable *index, RankType rank, XVariable *value
void XCSP3SummaryCallbacks::buildConstraintElement(string, vector<XVariable *> &list, int startIndex, XVariable *index, RankType, XVariable *value) {
    nbc++;
}


// string, vector<int> &list, int startIndex, XVariable *index, RankType rank, XVariable *value
void XCSP3SummaryCallbacks::buildConstraintElement(string, vector<int> &list, int startIndex, XVariable *index, RankType, XVariable *value) {
    nbc++;
}


// string id, vector<XVariable *> &list, int startIndex
void XCSP3SummaryCallbacks::buildConstraintChannel(string, vector<XVariable *> &list, int startIndex) {
    nbc++;
}


// string id, vector<XVariable *> &list1, int startIndex1, vector<XVariable *> &list2, int startIndex2
void XCSP3SummaryCallbacks::buildConstraintChannel(string, vector<XVariable *> &list1, int, vector<XVariable *> &list2, int) {
    nbc++;
}


// string id, vector<XVariable *> &list, int startIndex, XVariable *value
void XCSP3SummaryCallbacks::buildConstraintChannel(string, vector<XVariable *> &list, int, XVariable *value) {
    nbc++;
}


// string id, vector<XVariable *> &list, vector<int> &values, vector<XInterval> &widths
void XCSP3SummaryCallbacks::buildConstraintStretch(string, vector<XVariable *> &list, vector<int> &values, vector<XInterval> &widths) {
    nbc++;
}


// string id, vector<XVariable *> &list, vector<int> &values, vector<XInterval> &widths, vector<vector<int>> &patterns
void XCSP3SummaryCallbacks::buildConstraintStretch(string, vector<XVariable *> &list, vector<int> &values, vector<XInterval> &widths, vector<vector<int>> &patterns) {
    nbc++;
}


// string id, vector<XVariable *> &origins, vector<int> &lengths, bool zeroIgnored
void XCSP3SummaryCallbacks::buildConstraintNoOverlap(string, vector<XVariable *> &origins, vector<int> &lengths, bool) {
    nbc++;
}


// string id, vector<XVariable *> &origins, vector<XVariable *> &lengths, bool zeroIgnored
void XCSP3SummaryCallbacks::buildConstraintNoOverlap(string, vector<XVariable *> &origins, vector<XVariable *> &lengths, bool) {
    nbc++;
}


// string id, vector<vector<XVariable *>> &origins, vector<vector<int>> &lengths, bool zeroIgnored
void XCSP3SummaryCallbacks::buildConstraintNoOverlap(string, vector<vector<XVariable *>> &origins, vector<vector<int>> &lengths, bool) {
    nbc++;
}


// string id, vector<vector<XVariable *>> &origins, vector<vector<XVariable *>> &lengths, bool zeroIgnored
void XCSP3SummaryCallbacks::buildConstraintNoOverlap(string, vector<vector<XVariable *>> &origins, vector<vector<XVariable *>> &lengths, bool) {
    nbc++;
}


// string id, vector<XVariable *> &list, vector<int> &values
void XCSP3SummaryCallbacks::buildConstraintInstantiation(string, vector<XVariable *> &list, vector<int> &values) {
    nbc++;
}


// string id, vector<XVariable *> &list, vector<int> &values
void XCSP3SummaryCallbacks::buildConstraintClause(string, vector<XVariable *> &positive, vector<XVariable *> &negative) {
    nbc++;
}


// string id, vector<XVariable *> &list, int startIndex
void XCSP3SummaryCallbacks::buildConstraintCircuit(string, vector<XVariable *> &list, int startIndex) {
    nbc++;
}


// string id, vector<XVariable *> &list, int startIndex, int size
void XCSP3SummaryCallbacks::buildConstraintCircuit(string, vector<XVariable *> &list, int startIndex, int size) {
    nbc++;
}


// string id, vector<XVariable *> &list, int startIndex, XVariable *size
void XCSP3SummaryCallbacks::buildConstraintCircuit(string, vector<XVariable *> &list, int startIndex, XVariable *size) {
    nbc++;
}


void XCSP3SummaryCallbacks::buildObjectiveMinimizeExpression(string expr) {
    type = expr;
    minmax = "Minimize";
}


void XCSP3SummaryCallbacks::buildObjectiveMaximizeExpression(string expr) {
    type = expr;
    minmax = "Maximize";
}


void XCSP3SummaryCallbacks::buildObjectiveMinimizeVariable(XVariable *x) {
    type = "variable";
    minmax = "Minimize";
}


void XCSP3SummaryCallbacks::buildObjectiveMaximizeVariable(XVariable *x) {
    type = "variable";
    minmax = "Maximize";

}

void XCSP3SummaryCallbacks::buildConstraintCumulative(string id, vector<XVariable *> &origins, vector<int> &lengths, vector<int> &heights, vector<XVariable *> &ends,
                               XCondition &xc) {nbc++;}

void XCSP3SummaryCallbacks::buildObjectiveMinimize(ExpressionObjective _type, vector<XVariable *> &list, vector<int> &coefs) {
    minmax = "Minimize";
    switch(_type) {
        case SUM_O :
            type="sum";
            break;
        case PRODUCT_O :
            type="product";
            break;
        case MINIMUM_O :
            type="minimum";
            break;
        case MAXIMUM_O :
            type="maximum";
            break;
        case NVALUES_O :
            type="nvalues";
            break;
        case LEX_O :
            type="lex";
            break;
    }
}


void XCSP3SummaryCallbacks::buildObjectiveMaximize(ExpressionObjective _type, vector<XVariable *> &list, vector<int> &coefs) {
    minmax = "Maximize";
    switch(_type) {
        case SUM_O :
            type="sum";
            break;
        case PRODUCT_O :
            type="product";
            break;
        case MINIMUM_O :
            type="minimum";
            break;
        case MAXIMUM_O :
            type="maximum";
            break;
        case NVALUES_O :
            type="nvalues";
            break;
        case LEX_O :
            type="lex";
            break;
    }
}


void XCSP3SummaryCallbacks::buildObjectiveMinimize(ExpressionObjective _type, vector<XVariable *> &list) {
    minmax = "Minimize";
    switch(_type) {
        case SUM_O :
            type="sum";
            break;
        case PRODUCT_O :
            type="product";
            break;
        case MINIMUM_O :
            type="minimum";
            break;
        case MAXIMUM_O :
            type="maximum";
            break;
        case NVALUES_O :
            type="nvalues";
            break;
        case LEX_O :
            type="lex";
            break;
    }
}


void XCSP3SummaryCallbacks::buildObjectiveMaximize(ExpressionObjective _type, vector<XVariable *> &list) {
    minmax = "Maximize";
    switch(_type) {
        case SUM_O :
            type="sum";
            break;
        case PRODUCT_O :
            type="product";
            break;
        case MINIMUM_O :
            type="minimum";
            break;
        case MAXIMUM_O :
            type="maximum";
            break;
        case NVALUES_O :
            type="nvalues";
            break;
        case LEX_O :
            type="lex";
            break;
        default :
            break;
    }
}

void XCSP3SummaryCallbacks::buildAnnotationDecision(vector<XVariable*> &list) {
}

#endif //COSOCO_XCSP3SummaryCallbacks_H
