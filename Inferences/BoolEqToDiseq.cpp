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
 * @file BoolEqToDiseq.cpp
 * Implements class BoolEqToDiseq.
 */

#include "Debug/RuntimeStatistics.hpp"

#include "Kernel/OperatorType.hpp"
#include "Kernel/Clause.hpp"
#include "Kernel/SortHelper.hpp"
#include "Kernel/Signature.hpp"
#include "Kernel/Inference.hpp"
#include "Kernel/HOL/HOL.hpp"
#include "Kernel/TermIterators.hpp"

#include "Lib/Environment.hpp"
#include "Shell/Statistics.hpp"
#include "Lib/Metaiterators.hpp"

#include "BoolEqToDiseq.hpp"

#if VDEBUG
#include <iostream>
using namespace std;
#endif

namespace Inferences
{
  
using namespace Lib;
using namespace Kernel;
using namespace Indexing;
using namespace Saturation;


  
ClauseIterator BoolEqToDiseq::generateClauses(Clause* cl)
{
  unsigned pos = 0;
  Literal* newLit = 0;

  for(unsigned i = 0; i < cl->length(); i++){
    Literal* lit = (*cl)[i];
    if(!lit->polarity()){
      pos++;
      continue;
    }
    TermList eqSort = SortHelper::getEqualityArgumentSort(lit);
    if(eqSort == AtomicSort::boolSort()){
      TermList lhs = *lit->nthArgument(0);
      TermList rhs = *lit->nthArgument(1);
      if(HOL::isBool(lhs) || HOL::isBool(rhs)){
        pos++;
        continue;
      }
      TermList head = lhs.head();
      if(!head.isVar() && !head.isNot()){
        newLit = Literal::createEquality(false, HOL::app(HOL::neg(), lhs), rhs, AtomicSort::boolSort());
        goto afterLoop;
      }
      head = rhs.head();
      if(!head.isVar() && !head.isNot()){
        newLit = Literal::createEquality(false, lhs, HOL::app(HOL::neg(), rhs), AtomicSort::boolSort());
        goto afterLoop;
      }
    }
    pos++;
  }

  return ClauseIterator::getEmpty(); 

afterLoop:

  Clause* res = new(cl->length()) Clause(cl->length(), GeneratingInference1(InferenceRule::EQ_TO_DISEQ, cl));

  for (unsigned i = 0; i < res->length(); i++) {
    (*res)[i] = i == pos ? newLit : (*cl)[i];
  }

  env.statistics->boolEqToDiseq++;

  return pvi(getSingletonIterator(res));
}

}
