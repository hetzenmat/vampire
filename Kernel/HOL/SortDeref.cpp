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
 * @file SortDeref.cpp
 */

#include "Kernel/HOL/SortDeref.hpp"

TermSpec SortDeref::deref(TermList term)
{
  // assume term var here
  if (term.isVar() || !term.term()->hasTermVar())
    return {term, _index};

  return {transform(term), _index};
}

TermList SortDeref::transformSubterm(TermList t)
{
  THROW_MH("");
  /*
  if(t.isVar() && _positions.top() < _typeArities.top()) {
    t = _sub->derefBound(t);
  }
  unsigned pos = _positions.pop();
  _positions.push(pos + 1);
  return t;
   */
}

void SortDeref::onTermEntry(Term* t) {
  _typeArities.push(t->isSort() ? t->arity() : t->numTypeArguments());
  _positions.push(0);
}

void SortDeref::onTermExit(Term* t){
  _typeArities.pop();
  _positions.pop();
}

bool SortDeref::exploreSubterms(TermList orig, TermList newTerm) {
  ASS(newTerm.isTerm());

  return newTerm.term()->hasTermVar();
}