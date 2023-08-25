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
 * @file Superposition.hpp
 * Defines class Superposition.
 */


#ifndef __Superposition__
#define __Superposition__

#include "Forwards.hpp"
#include "Indexing/TermIndex.hpp"
#include "Kernel/KBO.hpp"
#include "Lib/MultiCounter.hpp"

#include "InferenceEngine.hpp"

namespace Inferences {

using namespace Kernel;
using namespace Indexing;
using namespace Saturation;

class LeftmostInnermostReducibilityChecker {
private:
  DHSet<Term*> _reducible;
  DHSet<Term*> _nonReducible;

  DemodulationLHSIndex* _index;
  const Ordering& _ord;
  const Options& _opt;

  bool checkTerm(Term* t, Term* tS, Term* rwTermS, ResultSubstitution* subst, bool result, bool& variant);
  bool checkTermReducible(Term* tS, TermList* tgtTermS);
  bool checkLeftmostInnermost(Clause* cl, Term* rwTermS, ResultSubstitution* subst, bool result);
  bool checkSmaller(Clause* cl, TermList rwTerm, Term* rwTermS, TermList* tgtTermS, ResultSubstitution* subst, bool result);

public:
  CLASS_NAME(LeftmostInnermostReducibilityChecker);
  USE_ALLOCATOR(LeftmostInnermostReducibilityChecker);

  LeftmostInnermostReducibilityChecker(DemodulationLHSIndex* index, const Ordering& ord, const Options& opt);

  bool check(Clause* cl, TermList rwTerm, Term* rwTermS, TermList* tgtTermS, ResultSubstitution* subst, bool result);
  void reset() { _nonReducible.reset(); }
  bool isNonReducible(Term* t) { return _nonReducible.contains(t); }  
};

class Superposition
: public GeneratingInferenceEngine
{
public:
  CLASS_NAME(Superposition);
  USE_ALLOCATOR(Superposition);

  void attach(SaturationAlgorithm* salg);
  void detach();

  ClauseIterator generateClauses(Clause* premise);

private:
  Clause* performSuperposition(
    Clause* rwClause, Literal* rwLiteral, TermList rwTerm,
    Clause* eqClause, Literal* eqLiteral, TermList eqLHS,
    ResultSubstitutionSP subst, bool eqIsResult, PassiveClauseContainer* passiveClauseContainer,
          UnificationConstraintStackSP constraints);

  bool checkClauseColorCompatibility(Clause* eqClause, Clause* rwClause);
  static bool earlyWeightLimitCheck(Clause* eqClause, Literal* eqLit,
      Clause* rwClause, Literal* rwLit, TermList rwTerm, TermList eqLHS, TermList eqRHS,
      ResultSubstitutionSP subst, bool eqIsResult, PassiveClauseContainer* passiveClauseContainer, unsigned numPositiveLiteralsLowerBound, const Inference& inf);

  static bool checkSuperpositionFromVariable(Clause* eqClause, Literal* eqLit, TermList eqLHS);

  struct ForwardResultFn;

  struct LHSsFn;
  struct RewritableResultsFn;
  struct BackwardResultFn;

  SuperpositionSubtermIndex* _subtermIndex;
  SuperpositionLHSIndex* _lhsIndex;
};


};

#endif /* __Superposition__ */
