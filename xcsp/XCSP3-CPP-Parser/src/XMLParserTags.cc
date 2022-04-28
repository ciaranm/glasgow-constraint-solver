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
#include "XMLParser.h"
#include<string>

using namespace XCSP3Core;


/***************************************************************************
 * Actions performed on INSTANCE tag
 ***************************************************************************/

void XMLParser::InstanceTagAction::beginTag(const AttributeList &attributes) {
    string stringtype;
    InstanceType type;
    if(!attributes["type"].to(stringtype))
        throw runtime_error("expected attribute type for tag <instance>");


    if(stringtype == "COP") type = COP;
    else if(stringtype == "CSP") type = CSP;
    else throw runtime_error("Unknon type for tag <instance>");


    this->parser->manager->beginInstance(type);
}


void XMLParser::InstanceTagAction::endTag() {
    this->parser->manager->endInstance();
    /*for(XEntity *xe : this->parser->toFree)
        delete xe;
    for(XIntegerEntity *xe : this->parser->toFreeEntity)
        delete xe;
    this->parser->toFree.clear();
    for(XDomainInteger *xdomain :this->parser->allDomains) {
        delete xdomain;
    }
    for(std::map<string, XEntity *>::iterator it = this->parser->variablesList.begin(); it != this->parser->variablesList.end(); ++it) {
        delete it->second;
    }*/
}


/***************************************************************************
 * Actions performed on VARIABLES tag
 ***************************************************************************/

// AttributeList &attributes
void XMLParser::VariablesTagAction::beginTag(const AttributeList &) {
    this->checkParentTag("instance");
    this->parser->manager->beginVariables();
}


void XMLParser::VariablesTagAction::endTag() {
    this->parser->manager->endVariables();
}


/***************************************************************************
 * Actions performed on VAR tag
 ***************************************************************************/

void XMLParser::VarTagAction::beginTag(const AttributeList &attributes) {
    string type, as, lid;

    this->checkParentTag("variables");
    this->parser->stateStack.front().subtagAllowed = false;

    variable = nullptr;
    variableArray = nullptr;


    if(!attributes["id"].to(lid))
        throw runtime_error("expected attribute id for tag <var>");
    id = lid;

    if(!attributes["class"].isNull())
        attributes["class"].to(classes);
    else
        classes = "";


    if(!attributes["type"].isNull()) {
        attributes["type"].to(type);
        if(type != "integer")
            throw runtime_error("XCSP3Core expected type=\"integer\" for tag <var>");
    }
    if(!attributes["as"].isNull()) {
        // Create a similar Variable
        attributes["as"].to(as);
        XVariableArray *similarArray;
        if(this->parser->variablesList[as] == NULL)
            throw runtime_error("Variable as \"" + as + "\" does not exist");
        if((similarArray = dynamic_cast<XVariableArray *>(this->parser->variablesList[as])) != NULL) {
            variableArray = new XVariableArray(id, similarArray);

        } else {
            XVariable *similar = (XVariable *)this->parser->variablesList[as];
            variable = new XVariable(id, similar->domain);
        }
    } else {
        domain = new XDomainInteger();
        this->parser->allDomains.push_back(domain);
    }
}


// UTF8String txt, bool last
void XMLParser::VarTagAction::text(const UTF8String txt, bool) {
    if((variable != NULL || variableArray != NULL) && !txt.isWhiteSpace())
        throw runtime_error("<var> with attribute 'as' must not have domain declaration");
    this->parser->parseDomain(txt, *domain);
}


void XMLParser::VarTagAction::endTag() {
    if(variableArray != NULL) {  // SImulate an array
        this->parser->manager->beginVariableArray(variableArray->id);
        this->parser->variablesList[variableArray->id] = variableArray;
        for(XVariable *x : variableArray->variables)
            this->parser->variablesList[x->id] = x;
        this->parser->manager->buildVariableArray(variableArray);
        this->parser->manager->endVariableArray();
        return;
    }
    if(variable == NULL)
        variable = new XVariable(id, domain);
    variable->classes = classes;
    this->parser->variablesList[variable->id] = variable;
    this->parser->manager->buildVariable(variable);

}


/***************************************************************************
 * Actions performed on ARRAY tag
 ***************************************************************************/


void XMLParser::ArrayTagAction::beginTag(const AttributeList &attributes) {
    string type, as, lid, size;

    this->checkParentTag("variables");
    varArray = NULL;
    domain = NULL;
    sizes.clear();

    if(!attributes["id"].to(lid))
        throw runtime_error("expected attribute id for tag <array>");
    id = lid;

    if(!attributes["class"].isNull())
        attributes["class"].to(classes);
    else
        classes = "";

    if(!attributes["type"].isNull()) {
        attributes["type"].to(type);
        if(type != "integer")
            throw runtime_error("XCSP3Core expected type=\"integer\" for tag <var>");
    }


    if(!attributes["as"].isNull()) {
        // Create a similar Variable
        attributes["as"].to(as);
        if(this->parser->variablesList[as] == nullptr)
            throw runtime_error("Matrix variable as \"" + as + "\" does not exist");
        XVariableArray *similar = (XVariableArray *)
                this->parser->variablesList[as];
        varArray = new XVariableArray(id, similar);
    } else {
        if(!attributes["size"].to(size))
            throw runtime_error("expected attribute id for tag <array>");
        vector<std::string> stringSizes = split(size, '[');
        for(unsigned int i = 0 ; i < stringSizes.size() ; i++) {
            if(stringSizes[i].size() == 0)
                continue;
            sizes.push_back(std::stoi(stringSizes[i].substr(0, stringSizes[i].size() - 1)));
        }
        varArray = new XVariableArray(id, sizes);

        domain = new XDomainInteger();
        this->parser->allDomains.push_back(domain);
        this->parser->manager->beginVariableArray(id);
    }

    varArray->classes = classes;
}


void XMLParser::ArrayTagAction::endTag() {
    if(domain != nullptr && domain->nbValues() != 0) // If dommain is null -> as variable // Possible empty variables
        varArray->buildVarsWith(domain);
    this->parser->variablesList[varArray->id] = varArray;
    for(XVariable *x : varArray->variables) {
        if(x == nullptr) // Undefined variable
            continue;
        this->parser->variablesList[x->id] = x;
    }
    this->parser->manager->buildVariableArray(varArray);
    this->parser->manager->endVariableArray();
}


void XMLParser::DomainTagAction::beginTag(const AttributeList &attributes) {
    this->checkParentTag("array");
    attributes["for"].to(forAttr);
    if(forAttr == "others")
        d = ((XMLParser::ArrayTagAction *) this->parser->getParentTagAction())->domain;
    else {
        d = new XDomainInteger();
        this->parser->allDomains.push_back(d);
    }
}


// UTF8String txt, bool last
void XMLParser::DomainTagAction::text(const UTF8String txt, bool) {
    this->parser->parseDomain(txt, *d);
}


void XMLParser::DomainTagAction::endTag() {
    if(forAttr == "others")
        return;

    string name;
    vector<string> allCompactForms;
    vector<XVariable *> vars;
    XVariableArray *varArray = ((XMLParser::ArrayTagAction *) this->parser->getParentTagAction())->varArray;

    split(forAttr, ' ', allCompactForms);
    for(unsigned int i = 0 ; i < allCompactForms.size() ; i++) {
        int pos = allCompactForms[i].find('[');
        name = allCompactForms[i].substr(0, pos);
        string compactForm = allCompactForms[i].substr(pos);
        vector<int> flatIndexes;
        vector<int> indexes;
        varArray->getVarsFor(vars, compactForm, &flatIndexes, true);
        for(unsigned int j = 0 ; j < flatIndexes.size() ; j++) {
            varArray->indexesFor(flatIndexes[j], indexes);
            varArray->variables[flatIndexes[j]] = new XVariable(varArray->id, d, indexes);
            this->parser->toFree.push_back(varArray->variables[flatIndexes[j]]);
        }
    }
}


void XMLParser::BasicConstraintTagAction::beginTag(const AttributeList &attributes) {
    group = NULL;
    this->parser->star = false;

    // Classic group
    if(strcmp(this->parser->getParentTagAction()->getTagName(), "group") == 0)
        group = ((XMLParser::GroupTagAction *) this->parser->getParentTagAction())->group;

    // Group with meta constraint not or block
    if(strcmp(this->parser->getParentTagAction(2)->getTagName(), "group") == 0) {
        group = ((XMLParser::GroupTagAction *) this->parser->getParentTagAction(2))->group;
        exit(1);
    }

    // Group with not and block
    if(this->parser->getParentTagAction(3) != NULL &&
       strcmp(this->parser->getParentTagAction(3)->getTagName(), "group") == 0)
        group = ((XMLParser::GroupTagAction *) this->parser->getParentTagAction(3))->group;


    // Slide constraint (special cases of group without args)
    if(strcmp(this->parser->getParentTagAction()->getTagName(), "slide") == 0)
        group = ((XMLParser::SlideTagAction *) this->parser->getParentTagAction())->group;

    // Group with meta constraint not or block
    if(strcmp(this->parser->getParentTagAction(2)->getTagName(), "slide") == 0) {
        group = ((XMLParser::SlideTagAction *) this->parser->getParentTagAction(2))->group;
        exit(1);
    }

    // Group with not and block
    if(this->parser->getParentTagAction(3) != NULL &&
       strcmp(this->parser->getParentTagAction(3)->getTagName(), "slide") == 0)
        group = ((XMLParser::SlideTagAction *)
                this->parser->getParentTagAction(3))->group;


    attributes["id"].to(id);

    if(!attributes["class"].isNull())
        attributes["class"].to(this->parser->classes);
    else
        this->parser->classes = "";

    this->parser->listTag->nbCallsToList = 0;
    this->parser->lists.clear();
    this->parser->lists.push_back(vector<XVariable *>());
    this->parser->matrix.clear();
    this->parser->patterns.clear();
    this->parser->weights.clear();


    this->parser->integers.clear();
    this->parser->values.clear();
    this->parser->widths.clear();
    this->parser->lengths.clear();
    this->parser->origins.clear();
    this->parser->transitions.clear();
    this->parser->nbParameters = 0;
    this->parser->occurs.clear();

    this->parser->star = false;
    this->parser->zeroIgnored = false;
    this->parser->condition = "";
    this->parser->rank = ANY;
    this->parser->index = NULL;
    this->parser->index2 = NULL;
    this->parser->closed = true;
    this->parser->listTag->nbCallsToList = 0;

}


/***************************************************************************
 * Actions performed on EXTENSION tag
 ****************************************************************************/

void XMLParser::ExtensionTagAction::beginTag(const AttributeList &attributes) {

    // Must be called inside a constraint
    BasicConstraintTagAction::beginTag(attributes);

    constraint = new XConstraintExtension(this->id, this->parser->classes);

    // Link constraint to group
    if(this->group != NULL) {
        this->group->constraint = constraint;
        this->group->type = EXTENSION;
    }

}


void XMLParser::ExtensionTagAction::endTag() {
    constraint->list.assign(this->parser->lists[0].begin(), this->parser->lists[0].end());
    constraint->containsStar = this->parser->star;

    /*for(unsigned int i = 0; i < constraint->tuples.size(); i++) {
        if ( constraint->tuples[i].size() != this->parser->lists[0].size()) {
            throw runtime_error("Problem between size of tuples and size of scope");
            exit(1);

        }
    }
*/
    if(this->group == NULL) {
        this->parser->manager->newConstraintExtension(constraint);
        delete constraint;
    }
}


void XMLParser::IntensionTagAction::beginTag(const AttributeList &attributes) {

    // Must be called inside a constraint
    BasicConstraintTagAction::beginTag(attributes);

    constraint = new XConstraintIntension(this->id, this->parser->classes);

    // Link constraint to group
    if(this->group != NULL) {
        this->group->constraint = constraint;
        this->group->type = INTENSION;
    }
    fnc.clear();

}


// UTF8String txt, bool last
void XMLParser::IntensionTagAction::text(const UTF8String txt, bool) {
    fnc.append(txt);
}


void XMLParser::IntensionTagAction::endTag() {
    fnc.to(constraint->function);
    constraint->function = trim(constraint->function);
    constraint->list.assign(this->parser->lists[0].begin(), this->parser->lists[0].end());
    if(this->group == NULL) {
        this->parser->manager->newConstraintIntension(constraint);
        delete constraint;
    }

}

/***************************************************************************
****************************************************************************
 *                  CONSTRAINTS DEFINED ON LANGAGES
 ***************************************************************************
***************************************************************************/

/***************************************************************************
* Actions performed on REGULAR tag
****************************************************************************/


void XMLParser::RegularTagAction::beginTag(const AttributeList &attributes) {

    // Must be called inside a constraint
    BasicConstraintTagAction::beginTag(attributes);

    constraint = new XConstraintRegular(this->id, this->parser->classes);

    // Link constraint to group
    if(this->group != NULL) {
        this->group->constraint = constraint;
        this->group->type = REGULAR;
    }
}


void XMLParser::RegularTagAction::endTag() {
    constraint->list.assign(this->parser->lists[0].begin(), this->parser->lists[0].end());
    constraint->start = this->parser->start;
    constraint->final.clear();
    split(this->parser->final, ' ', constraint->final);
    constraint->transitions.assign(this->parser->transitions.begin(), this->parser->transitions.end());

    if(this->group == NULL) {
        this->parser->manager->newConstraintRegular(constraint);
        delete constraint;
    }
}


/***************************************************************************
 * Actions performed on MDD tag
 ****************************************************************************/


void XMLParser::MDDTagAction::beginTag(const AttributeList &attributes) {

    // Must be called inside a constraint
    BasicConstraintTagAction::beginTag(attributes);

    constraint = new XConstraintMDD(this->id, this->parser->classes);

    // Link constraint to group
    if(this->group != NULL) {
        this->group->constraint = constraint;
        this->group->type = MDD;
    }
}


void XMLParser::MDDTagAction::endTag() {
    constraint->list.assign(this->parser->lists[0].begin(), this->parser->lists[0].end());
    constraint->transitions.clear();
    for(unsigned int i = 0 ; i < this->parser->transitions.size() ; i++) {
        XTransition &xt = this->parser->transitions[i];
        constraint->transitions.push_back(XTransition(xt.from, xt.val, xt.to));
    }

    if(this->group == NULL) {
        this->parser->manager->newConstraintMDD(constraint);
        delete constraint;
    }
}


/***************************************************************************
****************************************************************************
 *                  CONSTRAINTS DEFINED ON COMPARISON
****************************************************************************
***************************************************************************/


/***************************************************************************
 * Actions performed on ALLDIFF tag / ALLEQUAL
 ****************************************************************************/



void XMLParser::AllDiffEqualTagAction::beginTag(const AttributeList &attributes) {

    // Must be called inside a constraint
    BasicConstraintTagAction::beginTag(attributes);

    if(this->tagName == "allDifferent") {
        alldiff = new XConstraintAllDiff(this->id, this->parser->classes);
        ct = alldiff;
    } else {
        allequal = new XConstraintAllEqual(this->id, this->parser->classes);
        ct = allequal;
    }

    // Link constraint to group
    if(this->group != NULL) {
        if(this->tagName == "allDifferent")
            this->group->type = ALLDIFF;
        else
            this->group->type = ALLEQUAL;
        this->group->constraint = ct;
    }

}


// UTF8String txt, bool last
void XMLParser::AllDiffEqualTagAction::text(const UTF8String txt, bool) {
    this->parser->parseSequence(txt, this->parser->lists[0]);
}


void XMLParser::AllDiffEqualTagAction::endTag() {
    if((this->parser->lists.size() > 1 || this->parser->matrix.size() > 0) && this->group != NULL)
        throw runtime_error("AllDiff matrix and AllDiff lists are not implemented with groups");

    if(this->group == NULL) {
        if(this->tagName == "allDifferent") {
            if(this->parser->lists.size() > 1) {
                if(this->parser->integers.size() > 0)  // Except not implemented
                    throw runtime_error("except tag not allowed with alldiff on lists");

                XConstraintAllDiffList *ctl = new XConstraintAllDiffList(this->id, this->parser->classes);
                for(unsigned int i = 0 ; i < this->parser->lists.size() ; i++)
                    ctl->matrix.push_back(vector<XVariable *>(this->parser->lists[i].begin(), this->parser->lists[i].end()));
                this->parser->manager->newConstraintAllDiffList(ctl);
                delete ct;
                ct = ctl;
            } else {
                if(this->parser->matrix.size() > 0) { // Matrix
                    XConstraintAllDiffMatrix *ctm = new XConstraintAllDiffMatrix(this->id, this->parser->classes, this->parser->matrix);
                    this->parser->manager->newConstraintAllDiffMatrix(ctm);
                    delete ct;
                    ct = ctm;
                } else {
                    // Alldiff classic
                    ct->list.assign(this->parser->lists[0].begin(), this->parser->lists[0].end());
                    if(this->parser->values.empty() == false)
                        alldiff->values.assign(this->parser->values.begin(), this->parser->values.end());
                    this->parser->manager->newConstraintAllDiff(alldiff);
                }
            }
        } else {
            ct->list.assign(this->parser->lists[0].begin(), this->parser->lists[0].end());
            this->parser->manager->newConstraintAllEqual(allequal);
        }
        delete ct;
    } else {
        if(this->parser->values.empty() == false)
            alldiff->values.assign(this->parser->values.begin(), this->parser->values.end());

        ct->list.assign(this->parser->lists[0].begin(), this->parser->lists[0].end());
    }
}


/***************************************************************************
* Actions performed on ORDERED tag
****************************************************************************/



void XMLParser::OrderedTagAction::beginTag(const AttributeList &attributes) {


    // Must be called inside a constraint
    BasicConstraintTagAction::beginTag(attributes);

    constraint = new XConstraintOrdered(this->id, this->parser->classes);
    string cs;
    attributes["case"].to(cs);
    if(cs == "strictlyDecreasing") this->parser->op = GT;
    if(cs == "decreasing") this->parser->op = GE;
    if(cs == "strictlyIncreasing") this->parser->op = LT;
    if(cs == "increasing") this->parser->op = LE;


    // Link constraint to group
    if(this->group != NULL) {
        this->group->constraint = constraint;
        this->group->type = ORDERED;
    }
}


// const UTF8String txt, bool last
void XMLParser::OrderedTagAction::text(const UTF8String txt, bool) {
    this->parser->parseSequence(txt, this->parser->lists[0]);
}


void XMLParser::OrderedTagAction::endTag() {
    constraint->list.assign(this->parser->lists[0].begin(), this->parser->lists[0].end());
    constraint->op = this->parser->op;
    if(this->parser->lengths.size() > 0)
        constraint->lengths.assign(this->parser->lengths.begin(), this->parser->lengths.end());

    if(this->group == NULL) {
        this->parser->manager->newConstraintOrdered(constraint);
        delete constraint;
    }
}


/***************************************************************************
 * Actions performed on LEX tag
 ****************************************************************************/


void XMLParser::LexTagAction::beginTag(const AttributeList &attributes) {
    // Must be called inside a constraint
    BasicConstraintTagAction::beginTag(attributes);

    constraint = new XConstraintLex(this->id, this->parser->classes);

    // Link constraint to group
    if(this->group != NULL) {
        this->group->constraint = constraint;
        this->group->type = LEX;
    }
}


void XMLParser::LexTagAction::endTag() {
    if(this->parser->matrix.size() > 0) {
        XConstraintLexMatrix *lexM = new XConstraintLexMatrix(this->id, this->parser->classes);
        lexM->op = this->parser->op;
        for(unsigned int i = 0 ; i < this->parser->matrix.size() ; i++)
            lexM->matrix.push_back(
                    vector<XVariable *>(this->parser->matrix[i].begin(), this->parser->matrix[i].end()));

        this->parser->manager->newConstraintLexMatrix(lexM);
        delete lexM;
        delete constraint;
    } else {
        if(this->parser->lists.size() == 0)
            throw runtime_error("<lex> tag should  have many lists");

        for(unsigned int i = 0 ; i < this->parser->lists.size() ; i++)
            constraint->lists.push_back(
                    vector<XVariable *>(this->parser->lists[i].begin(), this->parser->lists[i].end()));
        constraint->op = this->parser->op;
        if(this->group == NULL) {
            this->parser->manager->newConstraintLex(constraint);
            delete constraint;
        }
    }
}


/***************************************************************************
****************************************************************************
 *                  COUNTIG AND SUMMING CONSTRAINTS
****************************************************************************
 ****************************************************************************/

/***************************************************************************
 * Actions performed on SUM tag
 ****************************************************************************/

void XMLParser::SumTagAction::beginTag(const AttributeList &attributes) {


    // Must be called inside a constraint
    BasicConstraintTagAction::beginTag(attributes);

    constraint = new XConstraintSum(this->id, this->parser->classes);

    // Link constraint to group
    if(this->group != NULL) {
        this->group->constraint = constraint;
        this->group->type = SUM;
    }
}


void XMLParser::SumTagAction::endTag() {
    constraint->list.assign(this->parser->lists[0].begin(), this->parser->lists[0].end());
    if(this->parser->values.size() == 0)
        constraint->values.clear();
    else
        constraint->values.assign(this->parser->values.begin(), this->parser->values.end());

    constraint->condition = this->parser->condition;

    if(this->group == NULL) {
        this->parser->manager->newConstraintSum(constraint);
        delete constraint;
    }
}


/***************************************************************************
 * Actions performed on NVALUES tag
 ****************************************************************************/

void XMLParser::NValuesTagAction::beginTag(const AttributeList &attributes) {

    // Must be called inside a constraint
    BasicConstraintTagAction::beginTag(attributes);

    constraint = new XConstraintNValues(this->id, this->parser->classes);

    // Link constraint to group
    if(this->group != NULL) {
        this->group->constraint = constraint;
        this->group->type = NVALUES;
    }
}


void XMLParser::NValuesTagAction::endTag() {
    constraint->list.assign(this->parser->lists[0].begin(), this->parser->lists[0].end());
    constraint->condition = this->parser->condition;
    constraint->except.assign(this->parser->integers.begin(), this->parser->integers.end());
    if(this->group == NULL) {
        this->parser->manager->newConstraintNValues(constraint);
        delete constraint;
    }
}


/***************************************************************************
 * Actions performed on COUNT tag
 ****************************************************************************/

void XMLParser::CountTagAction::beginTag(const AttributeList &attributes) {


    // Must be called inside a constraint
    BasicConstraintTagAction::beginTag(attributes);

    constraint = new XConstraintCount(this->id, this->parser->classes);

    // Link constraint to group
    if(this->group != NULL) {
        this->group->constraint = constraint;
        this->group->type = COUNT;
    }
}


void XMLParser::CountTagAction::endTag() {
    constraint->list.assign(this->parser->lists[0].begin(), this->parser->lists[0].end());
    constraint->values.assign(this->parser->values.begin(), this->parser->values.end());
    constraint->condition = this->parser->condition;
    if(this->group == NULL) {
        this->parser->manager->newConstraintCount(constraint);
        delete constraint;
    }
}


/***************************************************************************
* Actions performed on CARDINALITY tag
****************************************************************************/



void XMLParser::CardinalityTagAction::beginTag(const AttributeList &attributes) {


    // Must be called inside a constraint
    BasicConstraintTagAction::beginTag(attributes);
    this->parser->closed = false;
    constraint = new XConstraintCardinality(this->id, this->parser->classes);

    // Link constraint to group
    if(this->group != NULL) {
        this->group->constraint = constraint;
        this->group->type = CARDINALITY;
    }
}


void XMLParser::CardinalityTagAction::endTag() {
    constraint->list.assign(this->parser->lists[0].begin(), this->parser->lists[0].end());
    constraint->values.assign(this->parser->values.begin(), this->parser->values.end());
    constraint->occurs.assign(this->parser->occurs.begin(), this->parser->occurs.end());
    constraint->closed = this->parser->closed;
    if(this->group == NULL) {
        this->parser->manager->newConstraintCardinality(constraint);
        delete constraint;
    }
}


/***************************************************************************
****************************************************************************
 *                  CONNECTION CONSTRAINTS
****************************************************************************
 ****************************************************************************/

/***************************************************************************
 * Actions performed on CHANNEL tag
 ****************************************************************************/
void XMLParser::ChannelTagAction::beginTag(const AttributeList &attributes) {

    // Must be called inside a constraint
    BasicConstraintTagAction::beginTag(attributes);

    constraint = new XConstraintChannel(this->id, this->parser->classes);

    // Link constraint to group
    if(this->group != NULL) {
        this->group->constraint = constraint;
        this->group->type = CHANNEL;
    }
}


// const UTF8String txt, bool last
void XMLParser::ChannelTagAction::text(const UTF8String txt, bool) {
//                if (this->parser->list.size() == 0)
    this->parser->parseSequence(txt, this->parser->lists[0]);
}


void XMLParser::ChannelTagAction::endTag() {
    constraint->list.assign(this->parser->lists[0].begin(), this->parser->lists[0].end());
    constraint->startIndex1 = this->parser->startIndex;


    if(this->parser->values.size() == 1)
        constraint->value = this->parser->values[0];
    else if(this->parser->values.size() > 1)
        throw runtime_error("<value> tag accepts only one value");

    if(this->parser->lists.size() == 2) {
        constraint->secondList.assign(this->parser->lists[1].begin(), this->parser->lists[1].end());
        constraint->startIndex2 = this->parser->startIndex2;
    }

    if(this->group == NULL) {
        this->parser->manager->newConstraintChannel(constraint);
        delete constraint;
    }
}


/***************************************************************************
 * Actions performed on ELEMENT tag
 ****************************************************************************/


void XMLParser::ElementTagAction::beginTag(const AttributeList &attributes) {

    // Must be called inside a constraint
    BasicConstraintTagAction::beginTag(attributes);

    constraint = new XConstraintElement(this->id, this->parser->classes);

    // Link constraint to group
    if(this->group != NULL) {
        this->group->constraint = constraint;
        this->group->type = ELEMENT;
    }
}


void XMLParser::ElementTagAction::endTag() {
    constraint->list.assign(this->parser->lists[0].begin(), this->parser->lists[0].end());
    constraint->startIndex = this->parser->startIndex;
    constraint->index = this->parser->index;
    constraint->rank = this->parser->rank;

    if(this->parser->values.size() == 0)
        constraint->condition = this->parser->condition;
    else
        constraint->value = this->parser->values[0];

    XConstraintElementMatrix *c  = nullptr;
    if(this->parser->matrix.size() > 0) {
        c = new XConstraintElementMatrix(this->id, this->parser->classes, this->parser->matrix);
        c->value = this->parser->values[0];
        c->index = this->parser->index;
        c->rank = this->parser->rank;
        if(this->parser->index2 == NULL)
            throw runtime_error("<index> tag should have two values in element matrix");
        c->index2 = this->parser->index2;
        c->startRowIndex = this->parser->startRowIndex;
        c->startColIndex = this->parser->startColIndex;
        if(this->group != nullptr) {
            this->group->type = ELEMENTMATRIX;
            this->group->constraint = c;
        }
        delete constraint;
    }


    if(this->group == NULL) {
        if(this->parser->matrix.size() > 0) { // Matrix
            this->parser->manager->newConstraintElementMatrix(c);
            delete c;
        } else {
            this->parser->manager->newConstraintElement(constraint);
            delete constraint;
        }
    }
}


/***************************************************************************
 * Actions performed on MAXIMUM or MINIMUM tag
 ****************************************************************************/



void XMLParser::MinMaxTagAction::beginTag(const AttributeList &attributes) {

    if(!attributes["rank"].isNull()) {
        string rank;
        attributes["rank"].to(rank);
        if(rank == "any") this->parser->rank = ANY;
        if(rank == "first") this->parser->rank = FIRST;
        if(rank == "last") this->parser->rank = LAST;
    }


    // Must be called inside a constraint
    BasicConstraintTagAction::beginTag(attributes);

    constraint = new XConstraintMaximum(this->id, this->parser->classes);

    // Link constraint to group
    if(this->group != NULL) {
        this->group->constraint = constraint;
        if(this->tagName == "maximum") this->group->type = MAXIMUM;
        if(this->tagName == "minimum") this->group->type = MINIMUM;
        if(this->tagName == "minimumArg") this->group->type = MINARG;
        if(this->tagName == "maximumArg") this->group->type = MAXARG;
    }
}


void XMLParser::MinMaxTagAction::endTag() {
    constraint->list.assign(this->parser->lists[0].begin(), this->parser->lists[0].end());
    constraint->startIndex = this->parser->startIndex;
    constraint->condition = this->parser->condition;
    constraint->index = this->parser->index;
    constraint->rank = this->parser->rank;

    if(this->group == NULL) {
        if(this->tagName == "maximum") this->parser->manager->newConstraintMaximum(constraint);
        if(this->tagName == "minimum") this->parser->manager->newConstraintMinimum(constraint);
        if(this->tagName == "maximumArg") this->parser->manager->newConstraintMinMaxArg(constraint, true);
        if(this->tagName == "minimumArg")  this->parser->manager->newConstraintMinMaxArg(constraint, false);
        delete constraint;
    }
}

/***************************************************************************
 ****************************************************************************
  *                  PACKING and SCHEDULING CONSTRAINTS
 ****************************************************************************
  ****************************************************************************/

/***************************************************************************
 * Actions performed on STRETCH tag
 ****************************************************************************/

void XMLParser::StretchTagAction::beginTag(const AttributeList &attributes) {
    // Must be called inside a constraint
    BasicConstraintTagAction::beginTag(attributes);
    constraint = new XConstraintStretch(this->id, this->parser->classes);
    // Link constraint to group
    if(this->group != NULL) {
        this->group->constraint = constraint;
        this->group->type = STRETCH;
    }
}


void XMLParser::StretchTagAction::endTag() {
    constraint->list.assign(this->parser->lists[0].begin(), this->parser->lists[0].end());
    for(XEntity *xi : this->parser->values) {
        int v;
        isInteger(xi, v);
        constraint->values.push_back(v);
    }


    for(unsigned int i = 0 ; i < this->parser->widths.size() ; i++) {
        XIntegerInterval *xrange = dynamic_cast<XIntegerInterval *>(this->parser->widths[i]);
        constraint->widths.push_back(XInterval(xrange->min, xrange->max));
    }


    if(this->parser->patterns.size() > 0) {
        constraint->patterns.resize(this->parser->patterns.size());
        for(unsigned int i = 0 ; i < this->parser->patterns.size() ; i++)
            constraint->patterns[i].assign(this->parser->patterns[i].begin(), this->parser->patterns[i].end());
    }

    if(this->group == NULL) {
        this->parser->manager->newConstraintStretch(constraint);
        delete constraint;
    }
}


/***************************************************************************
 * Actions performed on NOOVERLAP tag
 ****************************************************************************/


void XMLParser::NoOverlapTagAction::beginTag(const AttributeList &attributes) {

    // Must be called inside a constraint
    BasicConstraintTagAction::beginTag(attributes);
    diffn = false;
    constraint = new XConstraintNoOverlap(this->id, this->parser->classes);
    if(!attributes["zeroIgnored"].isNull()) {
        string tmp;
        attributes["zeroIgnored"].to(tmp);
        this->parser->zeroIgnored = (tmp == "true");
    } else
        this->parser->zeroIgnored = true;

    // Link constraint to group
    if(this->group != NULL) {
        this->group->constraint = constraint;
        this->group->type = NOOVERLAP;
    }
}


void XMLParser::NoOverlapTagAction::endTag() {
    constraint->list.assign(this->parser->origins.begin(), this->parser->origins.end());
    constraint->lengths.assign(this->parser->lengths.begin(), this->parser->lengths.end());
    constraint->zeroIgnored = this->parser->zeroIgnored;
    if(this->group == NULL) {
        this->parser->manager->newConstraintNoOverlap(constraint);
        delete constraint;
    }
}


/***************************************************************************
   * Actions performed on CUMULATIVE tag
   ****************************************************************************/


void XMLParser::CumulativeTagAction::beginTag(const AttributeList &attributes) {

    // Must be called inside a constraint
    BasicConstraintTagAction::beginTag(attributes);

    constraint = new XConstraintCumulative(this->id, this->parser->classes);

    // Link constraint to group
    if(this->group != NULL) {
        this->group->constraint = constraint;
        this->group->type = CUMULATIVE;
    }
}


void XMLParser::CumulativeTagAction::endTag() {
    constraint->list.assign(this->parser->origins.begin(), this->parser->origins.end());
    constraint->lengths.assign(this->parser->lengths.begin(), this->parser->lengths.end());
    constraint->ends.assign(this->parser->ends.begin(), this->parser->ends.end());
    constraint->heights.assign(this->parser->heights.begin(), this->parser->heights.end());
    constraint->condition = this->parser->condition;


    if(this->group == NULL) {
        this->parser->manager->newConstraintCumulative(constraint);
        delete constraint;
    }
}


/***************************************************************************
   * Actions performed on BinPAcking tag
   ****************************************************************************/


void XMLParser::BinPackingTagAction::beginTag(const AttributeList &attributes) {

    // Must be called inside a constraint
    BasicConstraintTagAction::beginTag(attributes);

    constraint = new XConstraintBinPacking(this->id, this->parser->classes);

    // Link constraint to group
    if(this->group != NULL) {
        this->group->constraint = constraint;
        this->group->type = BINPACKING;
    }
}


void XMLParser::BinPackingTagAction::endTag() {
    constraint->list.assign(this->parser->lists[0].begin(), this->parser->lists[0].end());
    constraint->values.assign(this->parser->values.begin(), this->parser->values.end());
    constraint->condition = this->parser->condition;


    if(this->group == NULL) {
        this->parser->manager->newConstraintBinPacking(constraint);
        delete constraint;
    }
}


/***************************************************************************
****************************************************************************
 *                  CONSTRAINTS DEFINED ON GRAPHS
****************************************************************************
***************************************************************************/

void XMLParser::CircuitTagAction::beginTag(const AttributeList &attributes) {
    BasicConstraintTagAction::beginTag(attributes);

    constraint = new XConstraintCircuit(this->id, this->parser->classes);

    // Link constraint to group
    if(this->group != NULL) {
        this->group->constraint = constraint;
        this->group->type = CIRCUIT;
    }
    this->parser->values.clear();
}


// UTF8String txt, bool last
void XMLParser::CircuitTagAction::text(const UTF8String txt, bool) {
    this->parser->parseSequence(txt, this->parser->lists[0]);
}


void XMLParser::CircuitTagAction::endTag() {
    constraint->list.assign(this->parser->lists[0].begin(), this->parser->lists[0].end());
    constraint->startIndex = this->parser->startIndex;
    if(this->parser->values.size() == 1)
        constraint->value = this->parser->values[0];
    else {
        if(this->parser->values.size() == 0)
            constraint->value = nullptr;
        else
            throw runtime_error("<size> tag accepts only one value");
    }

    if(this->group == NULL) {
        this->parser->manager->newConstraintCircuit(constraint);
        delete constraint;
    }
}

/***************************************************************************
****************************************************************************
 *                  CPRECEDENCE CONSTRAINT
****************************************************************************
***************************************************************************/

void XMLParser::PrecedenceTagAction::beginTag(const AttributeList &attributes) {
    BasicConstraintTagAction::beginTag(attributes);

    constraint = new XConstraintPrecedence(this->id, this->parser->classes);

    // Link constraint to group
    if(this->group != NULL) {
        this->group->constraint = constraint;
        this->group->type = PRECEDENCE;
    }
    this->parser->values.clear();
}


// UTF8String txt, bool last
void XMLParser::PrecedenceTagAction::text(const UTF8String txt, bool) {
    this->parser->parseSequence(txt, this->parser->lists[0]);
}


void XMLParser::PrecedenceTagAction::endTag() {
    constraint->list.assign(this->parser->lists[0].begin(), this->parser->lists[0].end());
    constraint->values.assign(this->parser->values.begin(), this->parser->values.end());

    if(this->group == NULL) {
        this->parser->manager->newConstraintPrecedence(constraint);
        delete constraint;
    }
}



void XMLParser::FlowTagAction::beginTag(const AttributeList &attributes) {
    BasicConstraintTagAction::beginTag(attributes);

    constraint = new XConstraintFlow(this->id, this->parser->classes);

    // Link constraint to group
    if(this->group != NULL) {
        this->group->constraint = constraint;
        this->group->type = FLOW;
    }
}






void XMLParser::FlowTagAction::endTag() {
    constraint->list.assign(this->parser->lists[0].begin(), this->parser->lists[0].end());
    constraint->balance.assign(this->parser->values.begin(), this->parser->values.end());
    constraint->weights.assign(this->parser->weights.begin(), this->parser->weights.end());
    constraint->condition = this->parser->condition;

    int v=0;
    int i = 0;
    for (XEntity *xe: this->parser->lengths) {

        if(isInteger(xe, v)) { // Horrible, but too lazy....
            if(i%2 == 0)
                constraint->arcs.push_back(vector<int>());
            i++;
            constraint->arcs.back().push_back(v);
        }
    }

    if(this->group == NULL) {
        this->parser->manager->newConstraintFlow(constraint);
        delete constraint;
    }
}




void XMLParser::KnapsackTagAction::beginTag(const AttributeList &attributes) {
    BasicConstraintTagAction::beginTag(attributes);
    constraint = new XConstraintKnapsack(this->id, this->parser->classes);
    // Link constraint to group
    if(this->group != NULL) {
        this->group->constraint = constraint;
        this->group->type = FLOW;
    }
}






void XMLParser::KnapsackTagAction::endTag() {
    constraint->list.assign(this->parser->lists[0].begin(), this->parser->lists[0].end());
    constraint->profits.assign(this->parser->heights.begin(), this->parser->heights.end());
    constraint->weights.assign(this->parser->weights.begin(), this->parser->weights.end());
    constraint->condition = this->parser->condition;
    constraint->value = this->parser->values[0];


    if(this->group == NULL) {
        this->parser->manager->newConstraintKnapsack(constraint);
        delete constraint;
    }
}


/***************************************************************************
 ****************************************************************************
  *                            OBJECTIVES
 ****************************************************************************
  ****************************************************************************/


// AttributeList &attributes
void XMLParser::ObjectivesTagAction::beginTag(const AttributeList &) {
    objective = new XObjective();
    this->parser->expr = "";
    this->checkParentTag("instance");
    this->parser->lists.clear();
    this->parser->listTag->nbCallsToList = 0;
    this->parser->integers.clear();
    this->parser->values.clear();
    this->parser->lists.push_back(vector<XVariable *>());
    this->parser->manager->beginObjectives();
}


void XMLParser::ObjectivesTagAction::endTag() {
    if(this->parser->expr != "")
        objective->expression = this->parser->expr;

    if(this->parser->lists[0].size() > 0)
        objective->list.assign(this->parser->lists[0].begin(), this->parser->lists[0].end());
    if(this->parser->values.size() > 0) {
        int value;
        for(XEntity *xe : this->parser->values) {
            isInteger(xe, value);
            objective->coeffs.push_back(value);
        }
    } else if(objective->type != EXPRESSION_O) {
        objective->coeffs.assign(objective->list.size(), 1);
    }

    this->parser->manager->addObjective(objective);
    delete objective;
    this->parser->manager->endObjectives();

}


void XMLParser::MinimizeOrMaximizeTagAction::beginTag(const AttributeList &attributes) {
    obj = ((XMLParser::ObjectivesTagAction *) this->parser->getParentTagAction())->objective;
    obj->goal = (this->tagName == "minimize") ? MINIMIZE : MAXIMIZE;
    string tmp;
    this->checkParentTag("objectives");

    attributes["type"].to(tmp);
    obj->type = EXPRESSION_O;
    if(tmp == "sum") obj->type = SUM_O;
    if(tmp == "product") obj->type = PRODUCT_O;
    if(tmp == "minimum") obj->type = MINIMUM_O;
    if(tmp == "maximum") obj->type = MAXIMUM_O;
    if(tmp == "nValues") obj->type = NVALUES_O;
    if(tmp == "lex") obj->type = LEX_O;

}


// UTF8String txt, bool last
void XMLParser::MinimizeOrMaximizeTagAction::text(const UTF8String txt, bool) {
    string op;
    txt.to(op);
    if(trim(op) == "") return; // skip white space.

    if(obj->type == EXPRESSION_O)
        this->parser->expr = op;
    else
        this->parser->parseSequence(txt, this->parser->lists[0]);
}


/***************************************************************************
 * Actions performed on list of variables integers... tag
 ****************************************************************************/

// UTF8String txt, bool last
void XMLParser::ListOfIntegerTagAction::text(const UTF8String txt, bool) {
    UTF8String::Tokenizer tokenizer(txt);
    while(tokenizer.hasMoreTokens()) {
        UTF8String token = tokenizer.nextToken();
        int c = -1;
        token.to(c);
        this->parser->integers.push_back(c);
    }
}


void XMLParser::ListOfVariablesOrIntegerTagAction::beginTag(const AttributeList &attributes) {

    listToFill.clear();
    if(!attributes["closed"].isNull()) {
        string tmp;
        attributes["closed"].to(tmp);
        this->parser->closed = (tmp == "true");
    }
}


// UTF8String txt, bool last
void XMLParser::ListOfVariablesOrIntegerTagAction::text(const UTF8String txt, bool) {
    this->parser->parseSequence(txt, listToFill);
}


// AttributeList &attributes
void XMLParser::ListOfVariablesOrIntegerOrIntervalTagAction::beginTag(const AttributeList &) {
    listToFill.clear();
}


// UTF8String txt, bool last
void XMLParser::ListOfVariablesOrIntegerOrIntervalTagAction::text(const UTF8String txt, bool) {
    this->parser->keepIntervals = true;
    this->parser->parseSequence(txt, listToFill);
    this->parser->keepIntervals = false;
}


// AttributeList &attributes) {
void XMLParser::ListOfIntegerOrIntervalTagAction::beginTag(const AttributeList &) {
    listToFill.clear();
}


// UTF8String txt, bool last
void XMLParser::ListOfIntegerOrIntervalTagAction::text(const UTF8String txt, bool) {
    this->parser->parseListOfIntegerOrInterval(txt, listToFill);
}


/***************************************************************************
 * Actions performed on ORIGINS tag
 ****************************************************************************/


// AttributeList &attributes
void XMLParser::OriginsTagAction::beginTag(const AttributeList &) {
    listToFill.clear();
}


// UTF8String txt, bool last
void XMLParser::OriginsTagAction::text(const UTF8String txt, bool) {
    vector<char> delims;
    delims.push_back('(');
    delims.push_back(')');
    delims.push_back(',');
    this->parser->parseSequence(txt, listToFill, delims);
}


/***************************************************************************
 * Actions performed on ARGS tag
 ****************************************************************************/


// AttributeList &attributes
void XMLParser::ArgsTagAction::beginTag(const AttributeList &) {
    this->parser->args.clear();
}


// UTF8String txt, bool last
void XMLParser::ArgsTagAction::text(const UTF8String txt, bool) {
    this->parser->parseSequence(txt, this->parser->args);
}


void XMLParser::ArgsTagAction::endTag() {
    XConstraintGroup *group = ((GroupTagAction * )
    this->parser->getParentTagAction())->group;
    group->arguments.push_back(vector<XVariable *>(this->parser->args.begin(), this->parser->args.end()));
}


/***************************************************************************
 * Actions performed on Operator tag
 ****************************************************************************/


// UTF8String txt, bool last
void XMLParser::OperatorTagAction::text(const UTF8String txt, bool) {
    string op;
    txt.to(op);
    if(trim(op) == "") return; // skip white space.
    if(op == "lt") this->parser->op = LT;
    if(op == "le") this->parser->op = LE;
    if(op == "gt") this->parser->op = GT;
    if(op == "ge") this->parser->op = GE;
}


// UTF8String txt, bool last
void XMLParser::StringTagAction::text(const UTF8String txt, bool) {
    string tmp;
    txt.to(tmp);
    tmp = trim(tmp);
    if(tmp == "")
        return;
    if(this->tagName == "final") {
        this->parser->final = tmp;
    }
    if(this->tagName == "start")
        this->parser->start = tmp;
}


/***************************************************************************
 * Actions performed on instantiation tag
 ****************************************************************************/


void XMLParser::InstantiationTagAction::beginTag(const AttributeList &attributes) {
    // Must be called inside a constraint
    BasicConstraintTagAction::beginTag(attributes);
    constraint = new XConstraintInstantiation(this->id, this->parser->classes);
    // Link constraint to group
    if(this->group != NULL) {
        this->group->constraint = constraint;
        this->group->type = INSTANTIATION;
    }
}


void XMLParser::InstantiationTagAction::endTag() {
    constraint->list.assign(this->parser->lists[0].begin(), this->parser->lists[0].end());
    constraint->values.clear();
    for(XEntity *xi : this->parser->values) {
        int v;
        isInteger(xi, v);
        constraint->values.push_back(v);
    }
    if(this->group == NULL) {
        this->parser->manager->newConstraintInstantiation(constraint);
        delete constraint;
    }
}

/***************************************************************************
 * Actions performed on clause tag
 ****************************************************************************/


void XMLParser::ClauseTagAction::beginTag(const AttributeList &attributes) {
    // Must be called inside a constraint
    BasicConstraintTagAction::beginTag(attributes);
    constraint = new XConstraintClause(this->id, this->parser->classes);
    literals.clear();
    // Link constraint to group
    if(this->group != NULL) {
        this->group->constraint = constraint;
        this->group->type = CLAUSE;
    }
}

void XMLParser::ClauseTagAction::text(const UTF8String txt, bool) {
    literals.append(txt);
}



void XMLParser::ClauseTagAction::endTag() {
    if(this->group == nullptr) {
        UTF8String::Tokenizer tokenizer(literals);

        while(tokenizer.hasMoreTokens()) {

            UTF8String token = tokenizer.nextToken();

            string current;
            token.to(current);
            if(current == " ")
                continue;
            current = trim(current);
            size_t p = current.find('(');

            if(p == string::npos) {
                if(this->parser->variablesList[current] != NULL)
                    constraint->positive.push_back((XVariable *) this->parser->variablesList[current]);
                else
                    throw runtime_error("unknown variable: " + current);
            } else {
                assert(p == 3);
                string v = current.substr(p + 1, current.size() - p - 2);

                if(this->parser->variablesList[v] != NULL)
                    constraint->negative.push_back((XVariable *) this->parser->variablesList[v]);
                else
                    throw runtime_error("unknown variable: " + v);
            }

        }
        if(constraint->positive.size() == 0 && constraint->negative.size() == 0)
            throw runtime_error("clause is empty (currently the tag list inside a clause is not supported...)");
        this->parser->manager->newConstraintClause(constraint);
        delete constraint;
    }
}


void XMLParser::ListTagAction::beginTag(const AttributeList &attributes) {
    nbCallsToList++;
    if(nbCallsToList > 1) {
        this->parser->lists.push_back(vector<XVariable *>());
        this->parser->startIndex2 = 0;
        if(!attributes["startIndex"].isNull())
            attributes["startIndex"].to(this->parser->startIndex2);
    } else {
        this->parser->startIndex = 0;
        if(!attributes["startIndex"].isNull())
            attributes["startIndex"].to(this->parser->startIndex);
    }
    if(!attributes["offset"].isNull()) {
        SlideTagAction *slide = ((XMLParser::SlideTagAction *) this->parser->getParentTagAction());
        attributes["offset"].to(slide->offset);
    }
}


// UTF8String txt, bool last
void XMLParser::ListTagAction::text(const UTF8String txt, bool) {
    this->parser->parseSequence(txt, this->parser->lists.back());
}


void XMLParser::ListTagAction::endTag() {
    if(this->parser->getParentTagAction() != NULL &&
       strcmp(this->parser->getParentTagAction()->getTagName(), "slide") == 0) {
        if(nbCallsToList > 1)
            throw runtime_error("Multiple lists in slide constraint is not yet supported");

        SlideTagAction *sl = ((XMLParser::SlideTagAction *) this->parser->getParentTagAction());
        sl->list.insert(sl->list.begin(), this->parser->lists[0].begin(), this->parser->lists[0].end());
        this->parser->lists[0].clear(); // for sure.
    }

}


// AttributeList &attributes
void XMLParser::ConflictOrSupportTagAction::beginTag(const AttributeList &) {
    bool support = true;
    this->checkParentTag("extension");

    this->parser->star = false;
    if(this->tagName == "conflicts")
        support = false;

    ((XMLParser::ExtensionTagAction *) this->parser->getParentTagAction())->constraint->isSupport = support;
}


// UTF8String txt, bool last
void XMLParser::ConflictOrSupportTagAction::text(const UTF8String txt, bool) {
    XConstraintExtension *ctr = ((XMLParser::ExtensionTagAction *) this->parser->getParentTagAction())->constraint;
    if(this->parser->lists[0].size() == 1 && this->parser->lists[0][0]->id != "%...") {
        vector<XIntegerEntity *> tmplist;
        this->parser->parseListOfIntegerOrInterval(txt, tmplist);
        for(unsigned int i = 0 ; i < tmplist.size() ; i++) {
            for(int val = tmplist[i]->minimum() ; val <= tmplist[i]->maximum() ; val++) {
                ctr->tuples.push_back(vector<int>());
                ctr->tuples.back().push_back(val);
            }
        }
    } else
        this->parser->star |= this->parser->parseTuples(txt, ctr->tuples);
}


/***************************************************************************
 * Actions performed on GROUP tag
 ****************************************************************************/

void XMLParser::GroupTagAction::beginTag(const AttributeList &attributes) {
    string lid, tmp;
    //this->checkParentTag("constraints");
    attributes["id"].to(lid);

    if(!attributes["class"].isNull())
        attributes["class"].to(tmp);


    group = new XConstraintGroup(lid, tmp);
    this->parser->manager->beginGroup(lid);
    XParameterVariable::max = -1;
}


void XMLParser::GroupTagAction::endTag() {
    if(group->constraint == NULL)
        throw runtime_error("<group> constraint is not linked to a classical constraint");
    this->parser->manager->newConstraintGroup(group);
    this->parser->manager->endGroup();
    delete group;

}


/***************************************************************************
 * Actions performed on SLIDE tag
 ****************************************************************************/


void XMLParser::SlideTagAction::beginTag(const AttributeList &attributes) {
    string lid, tmp;
    //this->checkParentTag("constraints");
    attributes["id"].to(lid);
    if(!attributes["circular"].isNull()) {
        string tmp;
        attributes["circular"].to(tmp);
        circular = (tmp == "true");
    }
    if(!attributes["class"].isNull())
        attributes["class"].to(tmp);


    group = new XConstraintGroup(lid, tmp);
    this->parser->lists.clear();
    this->parser->listTag->nbCallsToList = 0;
    this->parser->lists.push_back(vector<XVariable *>()); // Be careful, why not ?? see after revision e32b7f8
    list.clear();
    this->parser->manager->beginSlide(lid, circular);
}


void XMLParser::SlideTagAction::endTag() {
    if(group->constraint == NULL)
        throw runtime_error("<slide> constraint is not linked to a classical constraint");

    // Create list of arguments
    if(this->parser->lists.size() != 1)
        throw runtime_error("Multiple lists in slide constraint is not yet supported");


    unsigned long arity;
    if(this->parser->nbParameters == 0) {
        XConstraintIntension *c = (XConstraintIntension *) group->constraint;
        int ar = 0;
        for(;; ar++) {
            if(c->function.find("%" + std::to_string(ar)) == string::npos)
                break;
        }
        arity = ar;
    } else
        arity = this->parser->nbParameters;

    unsigned long end = circular ? list.size() - arity + 2 : list.size() - arity + 1;
    for(unsigned int i = 0 ; i < end ; i += offset) {
        group->arguments.push_back(vector<XVariable *>());
        for(unsigned int j = 0 ; j < arity ; j++) {
            group->arguments.back().push_back(list[(i + j) % list.size()]);
        }
    }

    this->parser->manager->newConstraintGroup(group);

    this->parser->manager->endSlide();
    delete group;

}


/***************************************************************************
 * Actions performed on GROUP tag
 ****************************************************************************/



void XMLParser::BlockTagAction::beginTag(const AttributeList &attributes) {
    string currentClasses, lid;

    attributes["id"].to(lid);
    if(!attributes["class"].isNull())
        attributes["class"].to(currentClasses);
    else
        currentClasses = "";
    if(classes.empty())
        classes.push_back(currentClasses);
    else
        classes.push_back(classes.back() + " " + currentClasses);
    this->parser->manager->beginBlock(classes.back());
}


void XMLParser::BlockTagAction::endTag() {
    this->parser->manager->endBlock();
    classes.pop_back();
}


void XMLParser::IndexTagAction::beginTag(const AttributeList &attributes) {
    if(!attributes["rank"].isNull()) {
        string rank;
        attributes["rank"].to(rank);
        if(rank == "any") this->parser->rank = ANY;
        if(rank == "first") this->parser->rank = FIRST;
        if(rank == "last") this->parser->rank = LAST;
    }

}


// UTF8String txt, bool last
void XMLParser::IndexTagAction::text(const UTF8String txt, bool) {
    string tmp;
    txt.to(tmp);
    tmp = trim(tmp);
    if(tmp == "")
        return;
    if(this->parser->index != NULL && strcmp(this->parser->getParentTagAction(1)->getTagName(), "element") == 0 && this->parser->matrix.size() == 0)
        throw runtime_error("<index> tag must contain only one variable1");
    vector<XVariable *> tmpList;
    this->parser->parseSequence(txt, tmpList);
    if(tmpList.size() > 2 && strcmp(this->parser->getParentTagAction(1)->getTagName(), "element") == 0)
        throw runtime_error("<index> tag must contain only one variable2");

    if(this->parser->index2 != NULL)
        throw runtime_error("<index> tag must contain only two variables");
    if(tmpList.size() > 2)
        throw runtime_error("<index> tag must contain only two variables");

    if(this->parser->index == NULL) {
        this->parser->index = tmpList[0];
        if(tmpList.size() == 2)
            this->parser->index2 = tmpList[1];
    }else {
        if(tmpList.size() > 1)
            throw runtime_error("<index> tag must contain only two variables");
        this->parser->index2 = tmpList[0];
    }
}


/***************************************************************************
 * Actions performed on MATRIX TAG
 ****************************************************************************/

// AttributeList &attributes
void XMLParser::MatrixTagAction::beginTag(const AttributeList &attributes) {
    if(strcmp(this->parser->getParentTagAction(2)->getTagName(), "slide") == 0)
        throw runtime_error("<matrix> can not be used in a <slide>");

    this->parser->startRowIndex = 0;
    this->parser->startColIndex = 0;


    if(!attributes["startRowIndex"].isNull())
        attributes["startRowIndex"].to(this->parser->startRowIndex);
    if(!attributes["startColIndex"].isNull())
        attributes["startColIndex"].to(this->parser->startColIndex);
}


// UTF8String txt, bool last
void XMLParser::MatrixTagAction::text(const UTF8String txt, bool) {
    if(txt.isWhiteSpace())
        return;
    string txt2;
    txt.to(txt2);
    txt2 = trim(txt2);
    size_t p = txt2.find(("("));
    if(p == string::npos) {
        size_t pos = txt2.find("[");
        if(pos == string::npos)
            throw runtime_error("matrix needs a 2-dim matrix");
        string name;
        string compactForm;
        name = txt2.substr(0, pos);
        compactForm = txt2.substr(pos);
        if(this->parser->variablesList[name] == NULL)
            throw runtime_error("Matrix variable " + name + "does not exist");
        XVariableArray *varArray = ((XVariableArray *)
                this->parser->variablesList[name]);
        int nbV = 0;
        string tmp;
        // Find the first interval
        for(unsigned int i = 0 ; i < varArray->sizes.size() ; i++) {
            int pos = compactForm.find(']');
            tmp = compactForm.substr(1, pos - 1);
            compactForm = compactForm.substr(pos + 1);
            if(tmp.size() == 0) {
                nbV = varArray->sizes[i];
                break;
            }
            size_t dot = tmp.find("..");
            if(dot == string::npos)
                continue;
            int first = std::stoi(tmp.substr(0, dot));
            int last = std::stoi(tmp.substr(dot + 2));
            nbV = last - first + 1;
            break;
        }


        this->parser->parseSequence(txt, this->parser->lists[0]);
        int nbCol = this->parser->lists[0].size() / nbV;
        for(int i = 0 ; i < nbV ; i++) {
            this->parser->matrix.push_back(vector<XVariable *>());
            for(int j = 0 ; j < nbCol ; j++)
                this->parser->matrix.back().push_back(this->parser->lists[0][i * nbCol + j]);
        }

    } else {

        vector<char> delims;
        delims.push_back('(');
        delims.push_back(')');
        delims.push_back(',');
        this->parser->parseSequence(txt, this->parser->lists[0], delims);

        for(XVariable *x : this->parser->lists[0]) {
            if(x == NULL)
                this->parser->matrix.push_back(vector<XVariable *>());
            else
                this->parser->matrix.back().push_back(x);
        }
    }
}


void XMLParser::MatrixTagAction::endTag() {
    for(unsigned int i = 0 ; i < this->parser->matrix.size() - 1 ; i++)
        if(this->parser->matrix[i].size() != this->parser->matrix[i + 1].size())
            throw runtime_error("Matrix is not a matrix...");
}


// AttributeList &attributes
void XMLParser::TransitionsTagAction::beginTag(const AttributeList &) {
    nb = 0;
    transitions.clear();
}

void XMLParser::TransitionsTagAction::text(const UTF8String txt, bool last) {
    if(txt.isWhiteSpace())
        return;
    transitions.append(txt);
}

// UTF8String txt, bool last
void XMLParser::TransitionsTagAction::endTag() {
    UTF8String::Tokenizer tokenizer(transitions);
    tokenizer.addSeparator(')');
    tokenizer.addSeparator(',');
    tokenizer.addSeparator('(');
    // nb = 0 : from nb=1 : val nb=2 to
    while(tokenizer.hasMoreTokens()) {
        UTF8String token = tokenizer.nextToken();
        if(token == UTF8String(",")) continue;
        if(token == UTF8String("(")) {
            nb = 0; //Start
            continue;
        }
        if(token == UTF8String(")")) {
            assert(from != "");
            this->parser->transitions.push_back(XTransition(from, val, to));
            continue;
        }
        if(nb == 0) token.to(from);
        if(nb == 1) token.to(val);
        if(nb == 2) token.to(to);
        if(nb > 2) throw runtime_error("<transitions> tag is malformed");
        nb++;
    }
}


/***************************************************************************
 * Actions performed on  PATTERNS tag
****************************************************************************/


// const AttributeList &attributes
void XMLParser::PatternsTagAction::beginTag(const AttributeList &) {
    listToFill.clear();
}


// const UTF8String txt, bool last
void XMLParser::PatternsTagAction::text(const UTF8String txt, bool) {
    vector<char> delims;
    delims.push_back('(');
    delims.push_back(')');
    delims.push_back(',');
    this->parser->parseSequence(txt, listToFill, delims);

    for(XVariable *x : listToFill) {
        if(x == NULL) {
            if(this->parser->patterns.size() > 0 && this->parser->patterns.back().size() != 2)
                throw runtime_error("patterns needs couples of integers");
            this->parser->patterns.push_back(vector<int>());
        } else {
            int nb;
            if(!isInteger(x, nb))
                throw runtime_error("patterns accepts only integers:" + x->id);
            this->parser->patterns.back().push_back(nb);
        }
    }

}


/***************************************************************************
  *                            ANNOTATIONS
  ****************************************************************************/

void XMLParser::AnnotationsTagAction::beginTag(const AttributeList &) {
    this->parser->manager->beginAnnotations();

}


void XMLParser::AnnotationsTagAction::endTag() {
    this->parser->manager->endAnnotations();
}


void XMLParser::DecisionTagAction::beginTag(const AttributeList &) {

}



void XMLParser::DecisionTagAction::text(const UTF8String txt, bool) {
    this->parser->parseSequence(txt, list);
}

void XMLParser::DecisionTagAction::endTag() {
    this->parser->manager->buildAnnotationDecision(list);
}

