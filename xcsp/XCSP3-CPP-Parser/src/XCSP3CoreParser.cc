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
 */#include "XCSP3CoreParser.h"

using namespace XCSP3Core;

namespace XCSP3Core {
// From UTF8String
ostream & operator<<(ostream &f, const UTF8String s) {
    // directly output UTF8
    f.write(reinterpret_cast<const char *> (s._beg), s.byteLength());
    return f;
}
}


int XCSP3CoreParser::parse(const char *filename) {
    ifstream in(filename);
    if(!in.good())
        throw runtime_error("Path filename does not exist");
    return parse(in);
}


int XCSP3CoreParser::parse(istream &in) {
    /**
     * We don't use the DOM interface because it reads the document as
     * a whole and it is too memory consuming. The TextReader
     * interface is better because it reads only one node at a
     * time,but the text of a node is read as a whole and this can
     * still be large for the definition of some
     * relations. Therefore, we use the SAX interface.
     *
     * We also use the push mode to be able to read from any C++
     * stream.
     */
    const char *filename = NULL; // name of the input file
    xmlSAXHandler handler;
    xmlParserCtxtPtr parserCtxt = nullptr;

    const int bufSize = 4096;
    std::unique_ptr<char[]> buffer { new char[bufSize] };

    int size;

    xmlSAXVersion(&handler, 1); // use SAX1 for now ???

    handler.startDocument = startDocument;
    handler.endDocument = endDocument;
    handler.characters = characters;
    handler.startElement = startElement;
    handler.endElement = endElement;
    handler.comment = comment;


        xmlSubstituteEntitiesDefault(1);

        in.read(buffer.get(), bufSize);
        size = in.gcount();

        if(size > 0) {
            parserCtxt = xmlCreatePushParserCtxt(&handler, &cspParser, buffer.get(), size, filename);

            while(in.good()) {
                in.read(buffer.get(), bufSize);
                size = in.gcount();

                if(size > 0)
                    xmlParseChunk(parserCtxt, buffer.get(), size, 0);
            }

            xmlParseChunk(parserCtxt, buffer.get(), 0, 1);

            xmlFreeParserCtxt(parserCtxt);

            xmlCleanupParser();
        }

    return 0;
}


// void *parser, const xmlChar *value
void XCSP3CoreParser::comment(void *, const xmlChar *) { }


void XCSP3CoreParser::startDocument(void *parser) {
#ifdef debug
    cout << "Parsing begins" << endl;
#endif
    static_cast<XMLParser *> (parser)->startDocument();
}


void XCSP3CoreParser::endDocument(void *parser) {
#ifdef debug
    cout << "Parsing ends" << endl;
#endif
    static_cast<XMLParser *> (parser)->endDocument();
}


void XCSP3CoreParser::characters(void *parser, const xmlChar *ch, int len) {
#ifdef debug
    cout << "    chars '" << UTF8String(ch, ch + len) << "'" << endl;
#endif
    static_cast<XMLParser *> (parser)->characters(UTF8String(ch, ch + len));
}


void XCSP3CoreParser::startElement(void *parser, const xmlChar *name, const xmlChar **attr) {
    AttributeList attributes(attr);
#ifdef debug
    cout << "  begin element " << UTF8String(name) << endl;
            for (int i = 0; i < attributes.size(); ++i) {
                cout << "    attribute " << attributes.getName(i)
                        << " = " << attributes.getValue(i) << endl;
            }
#endif
    static_cast<XMLParser *> (parser)->startElement(UTF8String(name), attributes);
}


void XCSP3CoreParser::endElement(void *parser, const xmlChar *name) {
#ifdef debug
    cout << "  end element " << UTF8String(name) << endl;
#endif
    static_cast<XMLParser *> (parser)->endElement(UTF8String(name));
}



