/*
 * This file is part of the source code of the software program
 * Vampire. It is protected by applicable
 * copyright laws.
 *
 * This source code is distributed under the licence found here
 * https://vprover.github.io/license.html
 * and in the source directory
 */
/**
 * @file Tracer.hpp
 * Implements call tracing.
 * @since 01/05/2002 Manchester
 * @since 24/10/2002 Manchester, changed after talking with Shura
 * @since 08/12/2005 Redmond, moved to the Debug namespace with the purpose
 *                   of making global to Vampire
 */


#ifndef __Tracer__
#define __Tracer__

#include <iostream>
#include <iomanip>
#include "Debug/Output.hpp"

namespace Debug {

namespace Tracer {
  // print the current stack
  void printStack(std::ostream &out);
};

template<class... As>
struct _printDbg {
  void operator()(const As&... msg);
};

template<> struct _printDbg<>{
  void operator()() { }
};

template<class A, class... As> struct _printDbg<A, As...>{
  void operator()(const A& a, const As&... as) {
    std::cout << a;
    _printDbg<As...>{}(as...);
  }
};

template<class... A> void printDbg(const char* file, int line, const A&... msg)
{
  int width = 60;
  std::cout << "[ debug ] ";
  for (const char* c = file; *c != 0 && width > 0; c++, width--) {
    std::cout << *c;
  }
  for (int i = 0; i < width; i++) {
    std::cout << ' ';
  }
  std::cout <<  "@" << std::setw(5) << line << ":";
  _printDbg<A...>{}(msg...);
  std::cout << std::endl; 
}

struct Indent {
  static unsigned int value;
};

template<class... A> void printDbg2(int diffIndent, const char* file, const char* func, unsigned line, const A&... msg)
{
  if (diffIndent < 0) Indent::value += diffIndent;

  const char* slashIdx = nullptr;
  while (*file != 0) {
    if (*file == '/') slashIdx = file + 1;
    ++file;
  }

  for (unsigned i = 0; i < Indent::value; i++)
    std::cout << " ";

  std::cout << slashIdx << ":" << line << " @ " << func << ":";
  ((std::cout << " " << msg), ...);
  std::cout << std::endl;

  if (diffIndent > 0) Indent::value += diffIndent;
}

} // namespace Debug

#if VDEBUG
#  define DBG(...) { Debug::printDbg(__FILE__, __LINE__, __VA_ARGS__); }
#  define LOG(...) { Debug::printDbg2(0, __FILE__, __func__, __LINE__, __VA_ARGS__); }
#  define LOG_ENTER(...) { Debug::printDbg2(4, __FILE__, __func__, __LINE__, __VA_ARGS__); }
#  define LOG_RETURN(...) { Debug::printDbg2(-4, __FILE__, __func__, __LINE__, __VA_ARGS__); }
#  define DBGE(x) DBG(#x, " = ", x)
#else // ! VDEBUG
#  define DBG(...) {}
#  define LOG(...) {}
#  define DBGE(x) {}
#endif

#endif // Tracer
