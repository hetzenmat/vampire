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
 * @file WHNFDeref.hpp
 */

#include "Kernel/HOL/WHNFDeref.hpp"

#include "HOL.hpp"
#include "RedexReducer.hpp"
#include "SortDeref.hpp"

TermList WHNFDeref::normalise(TermSpec t) {
  _index = t.index;
  TermList term = t.term;
  term = transformSubterm(term);
  return term.isLambdaTerm() ? transform(term) : term;
}

TermList WHNFDeref::transformSubterm(TermList t) {
  if(t.isLambdaTerm())
    return t;

  TermList head;
  TermList sort;
  TermStack args;
  HOL::getHeadSortAndArgs(t, head, sort, args);

  TermSpec _newHead = _sub->derefBound({head, _index});
  ASS(_newHead.index == _index)
  _newHead = SortDeref(_sub).deref(_newHead);
  ASS(_newHead.index == _index)

  TermList newHead = _newHead.term;

  // if the head is a bound variable, then
  // either it is bound to a lambda term creating a redex on dereferencing,
  // or it is not. In the case, it isn't we need to track
  // that the head has changed
  bool headDereffed = newHead != head;

  while (HOL::canHeadReduce(newHead, args)) {
    headDereffed = false;
    t = RedexReducer().reduce(newHead, args);
    if (t.isLambdaTerm())
      break;
    HOL::getHeadSortAndArgs(t, head, sort, args);

    _newHead = _sub->derefBound({head, _index});
    ASS(_newHead.index == _index)
    _newHead = SortDeref(_sub).deref(_newHead);
    ASS(_newHead.index == _index)
    newHead = _newHead.term;

    headDereffed = newHead != head;
  }

  if (!headDereffed)
    return t;

  if(!args.size())
    return newHead;

  return HOL::app(sort, newHead, args);
}

bool WHNFDeref::exploreSubterms(TermList orig, TermList newTerm) {
  return newTerm.isLambdaTerm();
}