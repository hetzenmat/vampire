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
 * @file Forwards.hpp
 * Forward declarations of some classes
 */
#ifndef __Debug_Output__
#define __Debug_Output__

#include <iostream>
#include <utility>

namespace Kernel {

template<class A, class B>
std::ostream& operator<<(std::ostream& out, std::pair<A,B> const& self)
{ return out << "(" << self.first << ", " << self.second << ")"; }

/** Newtype in order to nicely output a pointer.
 * Usage: `out << outputPtr(ptr) << std::endl;` 
 */
template<class T>
struct OutputPtr {
  T* self;
  friend std::ostream& operator<<(std::ostream& out, OutputPtr const& self)
  { return self.self ? out << *self.self : out << "NULL"; }
};

template<class T>
OutputPtr<T> outputPtr(T* self) { return { .self = self, }; }

template<class T>
void repeat(std::ostream& out, T const& c, int times) 
{ for (int i = 0; i < times; i++) out << c; };


/** Newtype for outputting a datatype that implements it in multiline format.
 * Usage: `out << multiline(substitutioTree) << std::endl;` 
 *
 * You can implement this for a `MyType` by implementing 
 * std::ostream& operator<<(std::ostream&, OutputMultiline<MyType>)
 */
template<class T>
struct OutputMultiline { 
  T const& self; 
  unsigned indent; 

  static void outputIndent(std::ostream& out, unsigned indent)
  { repeat(out, "    ", indent); };
};


template<class T>
OutputMultiline<T> multiline(T const& self, unsigned indent)
{ return { self, indent, }; }

template<class Sep, class Iter>
struct OutputInterleaved { 
  Sep const& sep; 
  Iter iter; 
};

template<class Sep, class Iter>
struct OutputInterleaved<Sep,Iter> outputInterleaved(Sep const& s, Iter i)
{ return OutputInterleaved<Sep, Iter>{s, std::move(i)}; }

template<class Sep, class Iter>
std::ostream& operator<<(std::ostream& out, OutputInterleaved<Sep, Iter> self)
{
  if (self.iter.hasNext()) {
    out << self.iter.next();
    while (self.iter.hasNext()) {
      out << self.sep << self.iter.next();
    }
  }
  return out;
}

template<class Iter>
auto commaSep(Iter i) { return outputInterleaved(", ", std::move(i)); }

} // namespace Kernel
#endif // __Debug_Output__
