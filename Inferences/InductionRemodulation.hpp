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
 * @file InductionRemodulation.hpp
 * Defines class InductionRemodulation
 *
 */

#ifndef __InductionRemodulation__
#define __InductionRemodulation__

#include "Forwards.hpp"
#include "Indexing/TermIndex.hpp"

#include "InferenceEngine.hpp"
#include "InductionHelper.hpp"
#include "InductionForwardRewriting.hpp"
#include "InductionRemodulationSubsumption.hpp"
#include "Indexing/LiteralSubstitutionTree.hpp"

#include "Kernel/EqHelper.hpp"
#include "Kernel/Matcher.hpp"
#include "Kernel/TermTransformer.hpp"

#include "Lib/SharedSet.hpp"

#include "Shell/InductionSignatureTree.hpp"

namespace Inferences
{

using namespace Kernel;
using namespace Indexing;
using namespace Saturation;

inline bool litHasAllVarsOfClause(Literal* lit, Clause* cl) {
  auto vit = cl->getVariableIterator();
  while (vit.hasNext()) {
    auto v = vit.next();
    if (!lit->containsSubterm(TermList(v, false))) {
      return false;
    }
  }
  return true;
}

inline bool termHasAllVarsOfClause(TermList t, Clause* cl) {
  auto vit = cl->getVariableIterator();
  while (vit.hasNext()) {
    auto v = vit.next();
    if (!t.containsSubterm(TermList(v, false))) {
      return false;
    }
  }
  return true;
}

inline bool canUseForRewrite(Clause* cl) {
  return cl->length() == 1 ||
    (env.options->inductionConsequenceGeneration() == Options::InductionConsequenceGeneration::ON &&
     isFormulaTransformation(cl->inference().rule()));
}

inline bool hasTermToInductOn(Term* t, Literal* l) {
  static const bool intInd = InductionHelper::isIntInductionOn();
  static const bool structInd = InductionHelper::isStructInductionOn();
  NonVariableIterator stit(t);
  while (stit.hasNext()) {
    auto st = stit.next();
    if (InductionHelper::isInductionTermFunctor(st.term()->functor()) &&
      ((structInd && InductionHelper::isStructInductionFunctor(st.term()->functor())) ||
       (intInd && InductionHelper::isIntInductionTermListInLiteral(st, l))))
    {
      return true;
    }
  }
  return false;
}

class SingleOccurrenceReplacement : TermTransformer {
public:
  SingleOccurrenceReplacement(Literal* lit, Term* o, TermList r)
      : _lit(lit), _o(o), _r(r) {
    _occurrences = _lit->countSubtermOccurrences(TermList(_o));
  }

  Literal* transformSubset();

protected:
  virtual TermList transformSubterm(TermList trm);

private:
  // _iteration serves as a map of occurrences to replace
  unsigned _iteration = 0;
  // Counts how many occurrences were already encountered in one transformation
  unsigned _matchCount = 0;
  unsigned _occurrences;
  Literal* _lit;
  Term* _o;
  TermList _r;
};

class InductionRemodulation
: public GeneratingInferenceEngine
{
public:
  CLASS_NAME(InductionRemodulation);
  USE_ALLOCATOR(InductionRemodulation);

  InductionRemodulation()
    : _lhsIndex(), _termIndex() {}

  void attach(SaturationAlgorithm* salg) override;
  void detach() override;
  ClauseIterator generateClauses(Clause* premise) override;
  ClauseIterator perform(
    Clause* rwClause, Literal* rwLit, TermList rwTerm,
    Clause* eqClause, Literal* eqLit, TermList eqLHS,
    ResultSubstitutionSP subst, bool eqIsResult,
    UnificationConstraintStackSP constraints);
private:
  RemodulationLHSIndex* _lhsIndex;
  RemodulationSubtermIndex* _termIndex;
};

class InductionSGIWrapper
: public SimplifyingGeneratingInference
{
public:
  CLASS_NAME(InductionSGIWrapper);
  USE_ALLOCATOR(InductionSGIWrapper);

  InductionSGIWrapper(GeneratingInferenceEngine* induction, GeneratingInferenceEngine* inductionRemodulation,
      SimplifyingGeneratingInference* generator, GeneratingInferenceEngine* rewriting)
    : _induction(induction), _inductionRemodulation(inductionRemodulation), _generator(generator),
      _rewriting(rewriting) {}

  ClauseGenerationResult generateSimplify(Clause* premise) override {
    if (!premise->isInductionLemma()) {
      return _generator->generateSimplify(premise);
    }
    ASS(InductionHelper::isInductionClause(premise));
    ASS_EQ(premise->length(), 1);
    ASS(InductionHelper::isInductionLiteral((*premise)[0]));
    ClauseIterator clIt = _induction->generateClauses(premise);
    clIt = pvi(getConcatenatedIterator(clIt, _inductionRemodulation->generateClauses(premise)));
    clIt = pvi(getConcatenatedIterator(clIt, _rewriting->generateClauses(premise)));
    return ClauseGenerationResult {
      .clauses          = clIt,
      .premiseRedundant = false,
    };
  }
  void attach(SaturationAlgorithm* salg) override
  {
    _generator->attach(salg);
  }
  void detach() override
  {
    _generator->detach();
  }
private:
  GeneratingInferenceEngine* _induction;
  GeneratingInferenceEngine* _inductionRemodulation;
  ScopedPtr<SimplifyingGeneratingInference> _generator;
  GeneratingInferenceEngine* _rewriting;
};

}

#endif /*__InductionRemodulation__*/
