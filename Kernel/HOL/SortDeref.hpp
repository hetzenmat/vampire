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
 * @file SortDeref.hpp
 */

#ifndef __SortDeref__
#define __SortDeref__

#include "Kernel/RobSubstitution.hpp"
#include "Kernel/TermTransformer.hpp"

using namespace Kernel;

class SortDeref : public TermTransformer
{
public:
  SortDeref(RobSubstitution* sub, int index) : _sub(sub), _index(index) {}
  explicit SortDeref(RobSubstitution* sub) : _sub(sub), _index(-1) {}

  TermSpec deref(TermSpec term);
  TermList transformSubterm(TermList t) override;
  void onTermEntry(Term* t) override;
  void onTermExit(Term* t) override;
  bool exploreSubterms(TermList orig, TermList newTerm) override;

private:
  RobSubstitution* _sub;
  int _index;
  Stack<unsigned> _typeArities;
  Stack<unsigned> _positions;
};

#endif // __SortDeref__
