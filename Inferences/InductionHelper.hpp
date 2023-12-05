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
 * @file InductionHelper.hpp
 * Defines class InductionHelper
 *
 */

#ifndef __InductionHelper__
#define __InductionHelper__

#include "Forwards.hpp"

#include "Indexing/Index.hpp"
#include "Indexing/LiteralIndex.hpp"
#include "Indexing/TermIndex.hpp"

#include "Saturation/Splitter.hpp"

namespace Inferences {

using namespace Indexing;
using namespace Kernel;

class InductionHelper {
  using TermIndex               = Indexing::TermIndex<TermLiteralClause>;
public:
  USE_ALLOCATOR(InductionHelper);

  InductionHelper(LiteralIndex<LiteralClause>* comparisonIndex, TermIndex* inductionTermIndex)
      : _comparisonIndex(comparisonIndex), _inductionTermIndex(inductionTermIndex) {}

  VirtualIterator<TermLiteralClause> getLess(Term* t);
  VirtualIterator<TermLiteralClause> getGreater(Term* t);

  VirtualIterator<QueryRes<ResultSubstitutionSP, TermLiteralClause>> getTQRsForInductionTerm(Term* inductionTerm);

  static bool isIntegerComparison(Clause* c);
  static bool isIntInductionOn();
  static bool isIntInductionOneOn();
  static bool isIntInductionTwoOn();
  static bool isInductionForFiniteIntervalsOn();
  static bool isInductionForInfiniteIntervalsOn(); static bool isStructInductionOn();
  static bool isNonUnitStructInductionOn();
  static bool isInductionClause(Clause* c);
  static bool isInductionLiteral(Literal* l);
  static bool isInductionTermFunctor(unsigned f);
  static bool isIntInductionTermListInLiteral(Term* tl, Literal* l);
  static bool isStructInductionTerm(Term* t);

private:
  VirtualIterator<TermLiteralClause> getComparisonMatch(bool polarity, bool termIsLeft, Term* t);

  // The following pointers can be null if splitting or integer induction is off.
  LiteralIndex<LiteralClause>* _comparisonIndex;  // not owned
  TermIndex* _inductionTermIndex;  // not owned
};

};  // namespace Inferences

#endif /*__InductionHelper__*/
