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
 * @file EtaNormaliser.cpp
 */

#include "Kernel/HOL/EtaNormaliser.hpp"
#include "Kernel/HOL/TermShifter.hpp"
#include "Kernel/HOL/ApplicativeHelper.hpp"
#include "Kernel/TermTransformer.hpp"

TermList EtaNormaliser::normalise(TermList t)
{
  if (t.isVar() || !t.term()->hasLambda())
    return t;

  if (t.isLambdaTerm()) {
    TermStack lambdaSorts;
    TermList matrix;
    ApplicativeHelper::getMatrixAndPrefSorts(t, matrix, lambdaSorts);

    if (matrix.isVar())
      return t; // ^^^^^^X can't eta reduce this

    TermList matrixSort = SortHelper::getResultSort(matrix.term());
    TermList reduced = normalise(matrix);
    if (reduced != matrix)
      t = ApplicativeHelper::surroundWithLambdas(reduced, lambdaSorts, matrixSort, true);


    return transformSubterm(t);
  }

  // t is not a lambda term

  TermList head;
  TermList headSort;
  TermStack args;
  TermStack argsModified;
  ApplicativeHelper::getHeadSortAndArgs(t, head, headSort, args);

  bool changed = false;
  for (unsigned j = 0; j < args.size(); j++) {
    argsModified.push(normalise(args[j]));
    changed = changed || (argsModified[j] != args[j]);
  }

  if (!changed)
    return t;

  return ApplicativeHelper::app(headSort,head,argsModified);
}

// uses algorithm for eta-reduction that can be found here:
// https://matryoshka-project.github.io/pubs/lambdae.pdf

TermList EtaNormaliser::transformSubterm(TermList t) {
  TermList body = t;
  unsigned l = 0; // number of lambda binders
  while(body.isLambdaTerm()){
    l++;
    body = body.lambdaBody();
  }
  if(!l) return t; //not a lambda term, cannot eta reduce

  unsigned n = 0; // number of De bruijn indices at end of term
  TermList newBody = body;
  while(body.isApplication()){
    auto dbIndex = body.rhs().deBruijnIndex();
    if(!dbIndex.isSome() || dbIndex.unwrap() != n){
      break;
    }
    body = body.lhs();
    n++;
  }

  TermShifter ts;
  ts.shift(body, 0);
  auto mfi = ts.minFreeIndex();
  unsigned j = mfi.isSome() ? mfi.unwrap() : UINT_MAX; // j is minimum free index
  unsigned k = std::min(l, std::min(n, j));

  if(!k){
    return t;
  }

  for(unsigned i = 0; i < k; i++){
    newBody = newBody.lhs();
  }
  newBody = TermShifter().shift(newBody, 0 - k);

  body = t;
  for(unsigned i = 0; i < l - k; i++){
    body = body.lambdaBody();
  }

  // TermTransform doesn't work at top level...
  if (body == t) {
    return newBody;
  }

  return SubtermReplacer(body, newBody).transform(t);
}