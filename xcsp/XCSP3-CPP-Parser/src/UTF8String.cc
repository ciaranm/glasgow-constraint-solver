/*=============================================================================
 * parser for CSP instances represented in XML format
 *
 * Copyright (c) 2008 Olivier ROUSSEL (olivier.roussel <at> cril.univ-artois.fr)
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

#include "UTF8String.h"

using namespace XCSP3Core;

typedef unsigned char Byte;

//------------------------ CONSTRUCTORS ------------------------

UTF8String::UTF8String() {
    _beg = _end = NULL;
    allocated = 0;
}


UTF8String::UTF8String(const UTF8String &s) {
    _beg = s._beg;
    _end = s._end;
    allocated = 0;
}


UTF8String::UTF8String(const Byte *b, const Byte *e) {
    _beg = b;
    _end = e;
    allocated = 0;
}


UTF8String::UTF8String(const Byte *s) {
    _beg = s;
    _end = NULL;
    allocated = 0;
}

// nul terminated string

UTF8String::UTF8String(const char *s) {
    _beg = reinterpret_cast<const Byte *> (s);
    _end = NULL;
    allocated = 0;
}

UTF8String::~UTF8String() {
    if(allocated)
        delete[] _beg;
}

//------------------------ FUNCTIONS ------------------------

bool UTF8String::isNull() const {
    return _beg == NULL;
}


bool UTF8String::empty() const {
    return _beg == _end || (_beg && *_beg == 0);
}


int UTF8String::byteLength() const {
    if(!_end && _beg) {
        // identify the end of the string
        _end = _beg;
        while(*_end)
            ++_end;
    }

    return _end - _beg;
}


void UTF8String::clear() {
    _end = _beg;
}

UTF8String::iterator UTF8String::begin() const {
    return iterator(_beg);
}


UTF8String::iterator UTF8String::end() const {
    if(!_end && _beg) {
        // identify the end of the string
        _end = _beg;
        while(*_end)
            ++_end;
    }
    return iterator(_end);
}


void UTF8String::append(int ch) {
    if(_end + 4 > _beg + allocated)
        resize();

    // when it's allocated, it's writeable
    Byte *p = const_cast<Byte *> (_end);
    write(p, ch);
    _end = p;
}


void UTF8String::append(UTF8String s) {
    for(iterator it = s.begin(); it != s.end() && *it; ++it)
        append(*it);
}


bool UTF8String::isWhiteSpace() const {
    iterator it(_beg), end(_end);

    while(it != end && it.isWhiteSpace())
        ++it;

    return it == end || it.firstByte() == 0;
}


int UTF8String::firstChar() const {
    return *iterator(_beg);
}


int UTF8String::find(UTF8String sub) const {
    int pos = 0;
    int firstChar = sub.firstChar();

    for(iterator it(_beg), end(_end); it != end && it.firstByte(); ++it) {
        if(*it != firstChar)
            ++pos;
        else {
            // try to find a match
            iterator itSub(sub._beg), endSub(sub._end), it2(it);

            ++itSub;
            ++it2;

            while(it2 != end && it2.firstByte() &&
                  itSub != endSub && itSub.firstByte() &&
                  *it2 == *itSub) {
                ++it;
                ++itSub;
            }

            if(itSub == endSub || itSub.firstByte() == 0)
                return pos; // found it

            if(it2 == end || it2.firstByte() == 0)
                return npos; // can't find it any more
        }
    }

    return npos; // not found
}


UTF8String UTF8String::substr(int pos, int count) {
    const Byte *beg;
    iterator it(_beg), end(_end);

    for(int i = 0; i < pos && it != end && it.firstByte(); ++i)
        ++it;

    beg = it.getPointer();

    for(int i = 0; i < count && it != end && it.firstByte(); ++i)
        ++it;

    return UTF8String(beg, it.getPointer());
}


UTF8String UTF8String::substr(UTF8String::iterator beg, UTF8String::iterator end) {
    return UTF8String(beg.getPointer(), end.getPointer());
}


bool UTF8String::operator==(const UTF8String s) const {
    const Byte *p = _beg, *q = s._beg;

    while(p != _end && q != s._end && *p && *q && *p == *q) {
        ++p;
        ++q;
    }

    return (*p == 0 || p == _end) && (*q == 0 || q == s._end);
}


bool UTF8String::operator!=(const UTF8String s) const {
    return !operator==(s);
}


bool UTF8String::operator<(const UTF8String s) const {
    const Byte *p = _beg, *q = s._beg;

    while(p != _end && q != s._end && *p && *q && *p == *q) {
        ++p;
        ++q;
    }

    return (q != s._end && *q != 0) && ((p == _end || *p == 0) || *p < *q);
}


bool UTF8String::to(string &v) const {
    // fill v with the UTF8 encoding
    v.clear();

    for(const Byte *p = _beg; p != _end && *p; ++p)
        v += *p;

    return true;
}


bool UTF8String::to(int &v) const {
    iterator it(_beg), end(_end);
    bool neg = false;

    while(it != end && it.isWhiteSpace())
        ++it;

    if(it == end || it.firstByte() == 0) // end of string?
        return false;

    if(*it == '+')
        ++it;
    else if(*it == '-') {
        ++it;
        neg = true;
    }

    v = 0;
    while(it != end && *it >= '0' && *it <= '9') {
        //??? #warning "must check for overflows"
        v = v * 10 + (*it - '0');
        ++it;
    }

    if(neg)
        v = -v;

    while(it != end && it.isWhiteSpace())
        ++it;

    return it == end || it.firstByte() == 0;
}

void UTF8String::appendTo(string &v) const {
    // fill v with the UTF8 encoding

    for(const Byte *p = _beg; p != _end && *p; ++p)
        v += *p;
}

void UTF8String::resize() {
    if(allocated) {
        const Byte *q;
        Byte *tmp, *p;

        tmp = new Byte[2 * allocated];

        for(p = tmp, q = _beg; q != _end; ++p, ++q)
            *p = *q;

        delete[] _beg;
        _beg = tmp;
        _end = p;
        allocated *= 2;
    } else {
        allocated = 64;
        _beg = _end = new Byte[allocated];
    }
}

void UTF8String::write(Byte *&p, int ch) {
    if(ch < 0x80)
        *p++ = ch;
    else if(ch < 0x800) {
        *p++ = 0xC0 | (ch >> 6);
        *p++ = 0x80 | (ch & 0x3F);
    } else if(ch < 0x10000) {
        if(ch >= 0xD800 && ch <= 0xDFFF)
            throw runtime_error("invalid UTF8 character");

        *p++ = 0xE0 | (ch >> 12);
        *p++ = 0x80 | ((ch >> 6) & 0x3F);
        *p++ = 0x80 | (ch & 0x3F);
    } else if(ch < 0x110000) {
        *p++ = 0xF0 | (ch >> 18);
        *p++ = 0x80 | ((ch >> 12) & 0x3F);
        *p++ = 0x80 | ((ch >> 6) & 0x3F);
        *p++ = 0x80 | (ch & 0x3F);
    } else
        throw runtime_error("invalid UTF8 character");
}

//------------------------ ITERATOR INTERN CLASS ------------------------

UTF8String::iterator::iterator() {
    p = NULL;
}


UTF8String::iterator::iterator(const Byte *s) {
    p = s;
}


int UTF8String::iterator::operator*() {
    int ch = *p;

    switch(codeLength(ch)) {
        case 1:
            return ch;
        case 2:
            ch &= 0x1F;
            addNextByte(ch);
            return ch;
        case 3:
            if((ch == 0xE0 && p[1] < 0xA0)
               || (ch == 0xED && p[1] > 0x9F))
                throw runtime_error("invalid UTF8 character");

            ch &= 0x0F;
            addNextByte(ch);
            addNextByte(ch);
            return ch;
        case 4:
            if((ch == 0xF0 && p[1] < 0x90)
               || (ch == 0xF4 && p[1] > 0x8F))
                throw runtime_error("invalid UTF8 character");

            ch &= 0x07;
            addNextByte(ch);
            addNextByte(ch);
            addNextByte(ch);
            return ch;
        default:
            throw runtime_error("internal bug");
    }
}


UTF8String::iterator &UTF8String::iterator::operator++() // prefix
{
    p += codeLength(*p);
    return *this;
}


UTF8String::iterator UTF8String::iterator::operator++(int) // postfix
{
    iterator tmp = *this;
    p += codeLength(*p);
    return tmp;
}


UTF8String::iterator &UTF8String::iterator::operator--() // prefix
{
    const Byte *q = p;

    do {
        --p;
    } while((*p & 0xC0) == 0x80);

    if(p + codeLength(*p) != q)
        throw runtime_error("invalid UTF8 sequence");

    return *this;
}


UTF8String::iterator UTF8String::iterator::operator--(int) // postfix
{
    iterator tmp = *this;
    --(*this);
    return tmp;
}

UTF8String::iterator &UTF8String::iterator::operator=(UTF8String::iterator it) {
    p = it.p;
    return *this;
}


bool UTF8String::iterator::operator!=(UTF8String::iterator it) {
    return p != it.p;
}


bool UTF8String::iterator::operator==(UTF8String::iterator it) {
    return p == it.p;
}



const Byte *UTF8String::iterator::getPointer() const {
    return p;
}


Byte UTF8String::iterator::firstByte() const {
    return *p;
}

//------------------------ ITERATOR INTERN CLASS ------------------------
UTF8String::Tokenizer::Tokenizer(const UTF8String s) : it(s._beg), end(s._end) {
    skipWhiteSpace();
}


/**
 * Character ch will be returned as one token
 */
void UTF8String::Tokenizer::addSeparator(int ch) {
    separators.push_back(ch);
}


bool UTF8String::Tokenizer::hasMoreTokens() {
    return it != end && *it;
}


UTF8String UTF8String::Tokenizer::nextToken() {
    const Byte *b = it.getPointer(), *e;

    if(it == end || it.firstByte() == 0)
        return UTF8String();

    if(isSeparator(*it))
        ++it;
    else
        while(it != end && *it && !it.isWhiteSpace() && !isSeparator(*it))
            ++it;

    e = it.getPointer();

    skipWhiteSpace();

    return UTF8String(b, e);
}
