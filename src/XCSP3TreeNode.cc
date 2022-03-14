/*=============================================================================
 * parser for CSP instances represented in XCSP3 Format
 *
 * Copyright (c) 2015 xcsp.org (contact <at> xcsp.org)
 *
 * Permission is hereby granted, free of charge, to any person obtaining a copy
 * of this software and associated documentation files (the "Software"), to deal
 * in the Software without restriction, including without limitation the rights
 * to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
 * copies of the Software, and to permit pernewParams to whom the Software is
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

#include <map>

#include "XCSP3Tree.h"
#include "XCSP3TreeNode.h"
#include <sstream>
#include <vector>
#include <limits>
#include <algorithm>

using namespace XCSP3Core;


bool XCSP3Core::isSymmetricOperator(ExpressionType type) {
    return type == OADD || type == OMUL || type == OMIN || type == OMAX || type == ODIST || type == ONE
           || type == OEQ || type == OSET || type == OAND || type == OOR || type == OXOR || type == OIFF ||
           type == OUNION || type == OINTER || type == ODJOINT;
}


bool XCSP3Core::isNonSymmetricRelationalOperator(ExpressionType type) {
    return type == OLT || type == OLE || type == OGE || type == OGT;
}


bool XCSP3Core::isPredicateOperator(ExpressionType type) {
    return isRelationalOperator(type) || type == ONOT || type == OIMP || type == OAND || type == OOR || type == OAND || type == OOR || type == OXOR ||
     type == OIFF || type == OIN || type == ONOTIN;
}


bool XCSP3Core::isRelationalOperator(ExpressionType type) {
    return XCSP3Core::isNonSymmetricRelationalOperator(type) || type == ONE || type == OEQ;
}


ExpressionType XCSP3Core::arithmeticInversion(ExpressionType type) {
    return type == OLT ? OGT : type == OLE ? OGE : type == OGE ? OLE : type == OGT ? OLT : type; // no change for NE and EQ
}


std::string XCSP3Core::operatorToString(ExpressionType op) {
    if(op == ONEG) return "neg";
    if(op == OABS) return "abs";

    if(op == OADD) return "add";
    if(op == OSUB) return "sub";
    if(op == OMUL) return "mul";
    if(op == ODIV) return "div";
    if(op == OMOD) return "mod";

    if(op == OSQR) return "sqr";
    if(op == OPOW) return "pow";

    if(op == OMIN) return "min";
    if(op == OMAX) return "max";

    if(op == ODIST) return "dist";

    if(op == OLE) return "le";
    if(op == OLT) return "lt";
    if(op == OGE) return "ge";
    if(op == OGT) return "gt";

    if(op == ONE) return "ne";
    if(op == OEQ) return "eq";

    if(op == ONOT) return "not";
    if(op == OAND) return "and";
    if(op == OOR) return "or";
    if(op == OXOR) return "xor";
    if(op == OIMP) return "imp";
    if(op == OIF) return "if";
    if(op == OIFF) return "iff";

    if(op == OIN) return "in";
    if(op == ONOTIN) return "notin";
    if(op == OSET) return "set";
    //assert(false);
    return "oundef";
}


NodeOperator *createNodeOperator(std::string op) {
    NodeOperator *tmp = nullptr;
    if(op == "neg") tmp = new NodeNeg();
    if(op == "abs") tmp = new NodeAbs();

    if(op == "add") tmp = new NodeAdd();
    if(op == "sub") tmp = new NodeSub();
    if(op == "mul") tmp = new NodeMult();
    if(op == "div") tmp = new NodeDiv();
    if(op == "mod") tmp = new NodeMod();

    if(op == "sqr") tmp = new NodeSquare();
    if(op == "pow") tmp = new NodePow();

    if(op == "min") tmp = new NodeMin();
    if(op == "max") tmp = new NodeMax();
    if(op == "dist") tmp = new NodeDist();

    if(op == "le") tmp = new NodeLE();
    if(op == "lt") tmp = new NodeLT();
    if(op == "ge") tmp = new NodeGE();
    if(op == "gt") tmp = new NodeGT();

    if(op == "ne") tmp = new NodeNE();
    if(op == "eq") tmp = new NodeEQ();

    if(op == "not") tmp = new NodeNot();
    if(op == "and") tmp = new NodeAnd();
    if(op == "or") tmp = new NodeOr();
    if(op == "xor") tmp = new NodeXor();
    if(op == "imp") tmp = new NodeImp();
    if(op == "if") tmp = new NodeIf();
    if(op == "iff") tmp = new NodeIff();

    if(op == "in") tmp = new NodeIn();
    if(op == "notin") tmp = new NodeNotIn();
    if(op == "set") tmp = new NodeSet();

    if(tmp == nullptr)
        throw std::runtime_error("in expression, unexpected keyword " + op);
    return tmp;
}


ExpressionType XCSP3Core::logicalInversion(ExpressionType type) {
    return type == OLT ? OGE
                       : type == OLE ? OGT
                                     : type == OGE ? OLT
                                                   : type == OGT ? OLE
                                                                 : type == ONE ? OEQ
                                                                               : type == OEQ ? ONE
                                                                                             : type == OIN ? ONOTIN
                                                                                                           : type ==
                                                                                                             ONOTIN ? OIN
                                                                                                                    :
                                                                                                             type ==
                                                                                                             OSUBSET
                                                                                                             ? OSUPSEQ
                                                                                                             :
                                                                                                             type ==
                                                                                                             OSUBSEQ
                                                                                                             ? OSUPSET
                                                                                                             :
                                                                                                             type ==
                                                                                                             OSUPSEQ
                                                                                                             ? OSUBSET :
                                                                                                             type ==
                                                                                                             OSUPSET
                                                                                                             ? OSUBSEQ
                                                                                                             : OUNDEF;
}






int equalNodes(Node *a, Node *b) { // return -1 if a<0, 0 if a=b, +1 si a>b
    if(a->type != b->type)
        return static_cast<int>(a->type) - static_cast<int>(b->type);

    NodeConstant *c1 = dynamic_cast<NodeConstant *>(a), *c2 = dynamic_cast<NodeConstant *>(b);
    if(c1 != nullptr)
        return c1->val - c2->val;

    NodeVariable *v1 = dynamic_cast<NodeVariable *>(a), *v2 = dynamic_cast<NodeVariable *>(b);
    if(v1 != nullptr)
        return v1->var.compare(v2->var);


    NodeOperator *o1 = dynamic_cast<NodeOperator *>(a), *o2 = dynamic_cast<NodeOperator *>(b);
    if(o1->parameters.size() < o2->parameters.size())
        return -1;
    if(o1->parameters.size() > o2->parameters.size())
        return +1;

    for(unsigned int i = 0; i < o1->parameters.size() - 1; i++) {
        int cmp = equalNodes(o1->parameters[i], o2->parameters[i]);
        if(cmp != 0)
            return cmp;
    }
    return equalNodes(o1->parameters.back(), o2->parameters.back());
}


bool compareNodes(Node *a, Node *b) {
    return equalNodes(a, b) < 0;
}


bool pattern(Node *node, std::string s,
             std::vector<ExpressionType> &operators, std::vector<int> &constants, std::vector<std::string> &variables, bool fakeR=false) {
    constants.clear();
    variables.clear();
    operators.clear();
    Tree pattern(s);
    if(fakeR)
        pattern.root->type= OFAKEOP;
    return Node::areSimilar(node, pattern.root, operators, constants, variables);
}


Node *NodeOperator::canonize() {
    std::vector<int> constants;
    std::vector<std::string> variables;
    std::vector<ExpressionType> operators;


    std::vector<Node *> newParams;
    for(Node *n : parameters)
        newParams.push_back(n->canonize());

    if(isSymmetricOperator(type))
        std::sort(newParams.begin(), newParams.end(), compareNodes);


    ExpressionType newType = type;

    // newParams are potentially sorted if the type corresponds to a non-symmetric binary relational operator (in that case, we swap newParams and
    // arithmetically
    // inverse the operator)
    if(newParams.size() == 2 && isNonSymmetricRelationalOperator(type) &&
       (static_cast<int>(arithmeticInversion(type)) < static_cast<int>(type)
        || (arithmeticInversion(type) == type && equalNodes(newParams[0], newParams[1]) > 0))) {
        newType = arithmeticInversion(type);
        Node *tmp = newParams[0];
        newParams[0] = newParams[1];
        newParams[1] = tmp;
        return createNodeOperator(operatorToString(newType))->addParameters(newParams)->canonize();
    }


    // Now, some specific reformulation rules are applied
    if(newType == OLT && newParams[1]->type == ODECIMAL) { // lt(x,k) becomes le(x,k-1)
        NodeConstant *c = dynamic_cast<NodeConstant *>(newParams[1]);
        c->val = c->val - 1;
        return (new NodeLE())->addParameter(newParams[0])->addParameter(newParams[1])->canonize();
    }
    if(newType == OLT && newParams[0]->type == ODECIMAL) { // lt(k,x) becomes le(k+1,x)
        NodeConstant *c = dynamic_cast<NodeConstant *>(newParams[0]);
        c->val = c->val + 1;
        return (new NodeLE())->addParameter(newParams[0])->addParameter(newParams[1])->canonize();
    }


    NodeOperator *tmp = dynamic_cast<NodeOperator *>(newParams[0]);  // abs(sub becomes dist
    if(newType == OABS && newParams[0]->type == OSUB)
        return (new NodeDist())->addParameters(tmp->parameters)->canonize();

    if(newType == ONOT && newParams[0]->type == ONOT)   // NOT(NOT.. becomes ..
        return tmp->parameters[0]->canonize();

    if(newType == ONEG && newParams[0]->type == ONEG) // neg(neg(...)) becomes ...
        return tmp->parameters[0]->canonize();

    if(newType == ONOT && logicalInversion(newParams[0]->type) != OUNDEF) // not(lt(...)) becomes ge(...), not(eq(...)) becomes ne(...), and
        return createNodeOperator(operatorToString(logicalInversion(newParams[0]->type)))->addParameters(tmp->parameters)->canonize();


    if(newParams.size() == 1 && (newType == OADD || newType == OMUL || newType == OMIN || newType == OMAX || newType == OEQ || newType == OAND
                                 || newType == OOR || newType == OXOR || newType == OIFF)) // certainly can happen during the canonization process
        return newParams[0];

    if(newType == OADD || newType == OMUL) {// we merge constant (similar operations possible for MUL, MIN, ...)
        // They are at the end of the add
        NodeConstant *c1, *c2;
        if(newParams.size() >= 2 && (c1 = dynamic_cast<NodeConstant *>(newParams[newParams.size() - 1])) != nullptr &&
           (c2 = dynamic_cast<NodeConstant *>(newParams[newParams.size() - 2])) != nullptr) {
            std::vector<Node *> l;
            l.insert(l.end(), newParams.begin(), newParams.end() - 2);
            l.push_back(newType == OADD ? new NodeConstant(c1->val + c2->val) : new NodeConstant(c1->val * c2->val));

            if(newType == OADD)
                return ((new NodeAdd())->addParameters(l))->canonize();
            else
                return ((new NodeMult())->addParameters(l))->canonize();
        }
    }




    //le(add(y[4],5),7) -> le(y[4],2)
    if(pattern(this, "le(add(y[4],5),7)", operators, constants, variables, true)) {
        if(newType == OEQ || newType == ONE || newType == OLE || newType == OLT)
            return createNodeOperator(operatorToString(newType))
                    ->addParameter(new NodeVariable(variables[0]))->addParameter(new NodeConstant(constants[1] - constants[0]))->canonize();
    }

    //le(8,add(5,y[4])) -> le(3, y[4])
    if(pattern(this, "le(8,add(y[4],5))", operators, constants, variables, true)) {
        if(newType == OEQ || newType == ONE || newType == OLE || newType == OLT)
            return createNodeOperator(operatorToString(newType))
                    ->addParameter(new NodeConstant(constants[0] - constants[1]))->addParameter(new NodeVariable(variables[0]))->canonize();
    }

    //le(8,add(5,y[4]))->le(3, y[4])
    if(pattern(this, "le(8,add(5,y[4]))", operators, constants, variables, true)) {
        if(newType == OEQ || newType == ONE || newType == OLE || newType == OLT)
            return createNodeOperator(operatorToString(newType))
                    ->addParameter(new NodeConstant(constants[0] - constants[1]))->addParameter(new NodeVariable(variables[0]))->canonize();
    }

    // eq(mul(y[0],3),9) -> eq(y[0],3)
    if(pattern(this, "eq(mul(y[0],3),9)", operators, constants, variables) ||
            pattern(this, "eq(mul(3,x),6)", operators, constants, variables)) {
        if(constants[1] % constants[0] != 0)
            return new NodeConstant(0);
        return (new NodeEQ())->addParameter(new NodeVariable(variables[0]))->addParameter(new NodeConstant(constants[1] / constants[0]))->canonize();
    }

    //eq(9,mul(3,y[0]))
    if(pattern(this, "eq(9,mul(3,y[0]))", operators, constants, variables) ||
            pattern(this, "eq(9,mul(y[0],3))", operators, constants, variables)) {
        if(constants[0] % constants[1] != 0)
            return new NodeConstant(0);
        return (new NodeEQ())->addParameter(new NodeVariable(variables[0]))->addParameter(new NodeConstant(constants[0] / constants[1]))->canonize();
    }

    // Then, we merge operators when possible; for example add(add(x,y),z) becomes add(x,y,z)
    if(isSymmetricOperator(newType) && newType != OEQ && newType != ODIST && newType != ODJOINT) {
        for(unsigned int i = 0; i < newParams.size(); i++) {
            NodeOperator *n;
            if((n = dynamic_cast<NodeOperator *>(newParams[i])) != nullptr && n->type == newType) {
                std::vector<Node *> list;
                for(unsigned int j = 0; j < i; j++)
                    list.push_back(newParams[j]);

                list.insert(list.end(), n->parameters.begin(), n->parameters.end());

                for(unsigned int j = i + 1; j < newParams.size(); j++)
                    list.push_back(newParams[j]);
                return ((createNodeOperator(operatorToString(newType)))->addParameters(list))->canonize();
            }
        }
    }
    if(newParams.size() == 2 && isRelationalOperator(type)) {
        NodeOperator *n0 = dynamic_cast<NodeOperator *>(newParams[0]);
        NodeOperator *n1 = dynamic_cast<NodeOperator *>(newParams[1]);
        // First, we replace sub by add when possible
        if(newParams[0]->type == OSUB && newParams[1]->type == OSUB) {
            Node *a = (new NodeAdd())->addParameter(n0->parameters[0])->addParameter(n1->parameters[1]);
            Node *b = (new NodeAdd())->addParameter(n1->parameters[0])->addParameter(n0->parameters[1]);
            return (createNodeOperator(operatorToString(newType)))->addParameter(a)->addParameter(b)->canonize();
        } else if(newParams[1]->type == OSUB) {
            Node *a = (new NodeAdd())->addParameter(newParams[0])->addParameter(n1->parameters[1]);
            Node *b = n1->parameters[0];
            return (createNodeOperator(operatorToString(newType)))->addParameter(a)->addParameter(b)->canonize();
        } else if(n0 != nullptr && n0->op == "sub") {
            Node *a = n0->parameters[0];
            Node *b = (new NodeAdd())->addParameter(newParams[1])->addParameter(n0->parameters[1]);
            return (createNodeOperator(operatorToString(newType)))->addParameter(a)->addParameter(b)->canonize();
        }

        // next, we remove some add when possible
        if(newParams[0]->type == OADD && newParams[1]->type == ODECIMAL) {
            if(n0->parameters.size() == 2 && n0->parameters[0]->type == OVAR && n0->parameters[1]->type == ODECIMAL) {
                NodeConstant *c1 = dynamic_cast<NodeConstant *>(newParams[1]);
                NodeConstant *c2 = dynamic_cast<NodeConstant *>(n0->parameters[1]);
                return (createNodeOperator(operatorToString(newType)))->addParameter(n0->parameters[0])->addParameter(
                        new NodeConstant(c1->val - c2->val))->canonize();
            }
        }

        if(n0 != nullptr && n1 != nullptr && n0->type == OADD && n1->type == OADD) {
            NodeConstant *c1, *c2;
            if(n0->parameters.size() == 2 && n1->parameters.size() == 2 &&
               (c1 = dynamic_cast<NodeConstant *>(n0->parameters[1])) != nullptr &&
               (c2 = dynamic_cast<NodeConstant *>(n1->parameters[1])) != nullptr) {
                c1->val = c1->val - c2->val;
                newParams[1] = n1->parameters[0];
                return (createNodeOperator(operatorToString(newType)))->addParameters(newParams)->canonize();
            }
        }

    }

    return (createNodeOperator(operatorToString(newType)))->addParameters(newParams);
}


// -----------------------------------------
// Compare Two trees in order to find primitives
// -----------------------------------------

bool
Node::areSimilar(Node *canonized, Node *pattern, std::vector<ExpressionType> &operators, std::vector<int> &constants, std::vector<std::string> &variables) {
    if(pattern->type == OFAKEOP) {
        operators.push_back(canonized->type);
    } else {
        if(pattern->type != canonized->type)
            return false;

        if(pattern->type == ODECIMAL) {
            NodeConstant *c = dynamic_cast<NodeConstant *>(canonized);
            constants.push_back(c->val);
            return true;
        }

        if(pattern->type == OVAR) {
            NodeVariable *v = dynamic_cast<NodeVariable *>(canonized);
            variables.push_back(v->var);
            return true;
        }

    }
    if(pattern->type == OSET) {
        for(Node *n : canonized->parameters)
            if(n->type != ODECIMAL)
                return false;
        return true;
    }

    NodeOperator *nc = dynamic_cast<NodeOperator *>(canonized);
    NodeOperator *np = dynamic_cast<NodeOperator *>(pattern);
    if(nc->parameters.size() != np->parameters.size())
        return false;

    for(unsigned int i = 0; i < nc->parameters.size(); i++) {
        if(Node::areSimilar(nc->parameters[i], np->parameters[i], operators, constants, variables) == false)
            return false;
    }
    return true;
}
