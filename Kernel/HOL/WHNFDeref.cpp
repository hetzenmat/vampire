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

TermSpec WHNFDeref::normalise(TermSpec t) {
  THROW_MH("");
  _index = t.index;
  // term transformer does not work at the top level...
  auto transformed = transformSubterm(t.term);

  // return transformed.isLambdaTerm() ? transform(transformed) : transformed;
}

TermList WHNFDeref::transformSubterm(TermList t) {
  THROW_MH("");

  /*if(t.isLambdaTerm()) return t;

  TermList head;
  TermList sort;
  TermStack args;
  ApplicativeHelper::getHeadSortAndArgs(t, head, sort, args);
  TermList newHead = _sub->derefBound(head);
  newHead = SortDeref(_sub).deref(newHead);

  // if the head is a bound variable, then
  // either it is bound to a lambda term creating a redex on dereferencing,
  // or it is not. In the case, it isn't we need to track
  // that the head has changed
  bool headDereffed = newHead != head;

  while(ApplicativeHelper::canHeadReduce(newHead, args)){
    headDereffed = false;
    t = RedexReducer().reduce(newHead, args);
    if(t.isLambdaTerm()) break;
    ApplicativeHelper::getHeadSortAndArgs(t, head, sort, args);
    newHead = _sub->derefBound(head);
    newHead = SortDeref(_sub).deref(newHead);
    headDereffed = newHead != head;
  }

  return !headDereffed ? t :
         !args.size()  ? newHead : // TOOD MH maybe use args.empty() instead of !args.size()
                         ApplicativeHelper::app(sort, newHead, args);
*/

  /*if(!headDereffed){
    return t;
  } else if(!args.size()){
    return newHead;
  } else {
    return ApplicativeHelper::app(sort, newHead, args);
  }*/

}

bool WHNFDeref::exploreSubterms(TermList orig, TermList newTerm) {
  return newTerm.isLambdaTerm();
}