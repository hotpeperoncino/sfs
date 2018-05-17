/*  [printbuf.h] Print buffer class for anders2 debug output
 *  v. 005, 2008-08-15
 *------------------------------------------------------------------------------
 *  This buffer is used to form a string of debug info before output.
 *  The fixed-size char array must be allocated before use with reset()
 *    and can be deleted at any time using free().
 *  The << operator is supported for int, unsigned, char, char*, and
 *    std::string; there is also printf() with the usual syntax, nprintf()
 *    to limit the length, and nputs() to append the first N chars of a string.
 *    None of the append methods ever overflow the buffer.
 *  The result can be cast either to a char* (which is automatically null-
 *    terminated) or to an std::string. Use reset() to start a new string.
 *------------------------------------------------------------------------------
 *  Copyright 2008 Andrey Petrov
 *  - apetrov87@gmail.com, apetrov@cs.utexas.edu
 *
 *  Permission is hereby granted, free of charge, to any person
 *  obtaining a copy of this software and associated documentation
 *  files (the "Software"), to deal in the Software without
 *  restriction, including without limitation the rights to use, copy,
 *  modify, merge, publish, distribute, sublicense, and/or sell copies
 *  of the Software, and to permit persons to whom the Software is
 *  furnished to do so, subject to the following conditions:
 *
 *  The above copyright notice and this permission notice shall be
 *  included in all copies or substantial portions of the Software.
 *
 *  THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND,
 *  EXPRESS OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF
 *  MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND
 *  NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT
 *  HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY,
 *  WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
 *  OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER
 *  DEALINGS IN THE SOFTWARE.
 *------------------------------------------------------------------------------
 */

#ifndef __PRINTBUF_H
#define __PRINTBUF_H

#include "common.h"

//The max. length of the buffered string
const size_t pb_size= 1<<18;

//------------------------------------------------------------------------------
class PrintBuf{
private:

  char *buf;
  //Current write position in the buffer; p==0 whenever buf==0
  char *p;

  void alloc(){
    assert(!buf);
    buf= (char*)malloc(pb_size+1);
    p= buf;
  }

public:
//------------------------------------------------------------------------------
  PrintBuf(){
    p= buf= 0;
  }
  ~PrintBuf(){
    free();
  }

  void free(){
    if(!buf)
      return;
    ::free(buf);
    p= buf= 0;
  }
  void reset(){
    if(!buf)
      alloc();
    p= buf;
  }

//------------------------------------------------------------------------------
  //Get a pointer to the start/end of the buffer and the current position.
  const char* begin() const{
    return buf;
  }
  const char* end() const{
    return buf ? buf+pb_size : 0;
  }
  const char* pos() const{
    return p;
  }

  //Get the current length of the string and the remaining space.
  size_t size() const{
    return buf ? p-buf : 0;
  }
  size_t avail() const{
    return pb_size - size();
  }

  operator const char*() const{
    assert(buf);
    *p= 0;
    return buf;
  }
  operator string() const{
    assert(buf);
    return string(buf, p);
  }

//------------------------------------------------------------------------------
  PrintBuf& operator << (const char *s){
    assert(buf);
    for(char *pe= buf + pb_size; p < pe && *s; *(p++)= *(s++));
    return *this;
  }
  PrintBuf& operator << (const string &s){
    return (operator<<(s.c_str()));
  }

  PrintBuf& operator << (char c){
    assert(buf);
    if((size_t)(p-buf) < pb_size)
      *(p++)= c;
    return *this;
  }

  PrintBuf& operator << (int x){
    assert(buf);
    size_t n= pb_size - (p-buf);
    size_t res= snprintf(p, n, "%d", x);
    //snprintf returns how much space the complete printout needed,
    //  which may be more than it actually printed.
    if(res > n)
      res= n;
    p += res;                           //point (p) to the new end pos.
    return *this;
  }
  PrintBuf& operator << (u32 x){
    assert(buf);
    size_t n= pb_size - (p-buf);
    size_t res= snprintf(p, n, "%u", x);
    if(res > n)
      res= n;
    p += res;
    return *this;
  }

//------------------------------------------------------------------------------
  size_t printf(const char *fmt, ...){
    assert(buf);
    size_t n= pb_size - (p-buf);
    if(!n)
      return 0;
    va_list va;
    va_start(va, fmt);
    size_t res= vsnprintf(p, n, fmt, va);
    if(res > n)
      res= n;
    p += res;
    va_end(va);
    return res;
  }

  size_t nprintf(size_t n, const char *fmt, ...){
    assert(buf);
    size_t n2= pb_size - (p-buf);       //remaining space
    if(!n2)
      return 0;
    if(n > n2)                //make sure the given limit is not too big
      n= n2;
    //Pass the varargs part to the real snprintf.
    va_list va;
    va_start(va, fmt);
    size_t res= vsnprintf(p, n, fmt, va);
    if(res > n)
      res= n;
    p += res;
    va_end(va);
    return res;
  }

  size_t nputs(size_t n, const char *s){
    assert(buf);
    char *pe= buf + pb_size, *pn= p + n, *p0= p;
    if(pn > pe)
      pn= pe;
    for(; p < pn && *s; *(p++)= *(s++));
    return p-p0;
  }
  size_t nputs(size_t n, const string &s){
    return nputs(n, s.c_str());
  }

  //Pad the string with (c) on the right, up to (len).
  void pad(char c, u32 len){
    assert(buf);
    if(len > pb_size)
      len= pb_size;
    for(char *pe= buf+len; p < pe; *(p++)= c);
  }

  //Cut off the result to at most (len) chars.
  void clip(u32 len){
    if(p > buf+len)
      p= buf+len;
  }
};

#endif
