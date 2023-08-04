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
 * @file UnitEqualityCC.hpp
 * Defines class UnitEqualityCC.
 */

#ifndef __UnitEqualityCC__
#define __UnitEqualityCC__

#include "Forwards.hpp"
#include "Shell/Options.hpp"

#include "DP/SimpleCongruenceClosure.hpp"
#include "Indexing/TermSubstitutionTree.hpp"
#include "Indexing/TermIndex.hpp"

#include "InferenceEngine.hpp"

namespace Inferences
{

using namespace Kernel;
using namespace Saturation;
using namespace DP;
using namespace Indexing;

class UnitEqualityCC
: public GeneratingInferenceEngine
{
public:
  CLASS_NAME(UnitEqualityCC);
  USE_ALLOCATOR(UnitEqualityCC);

  UnitEqualityCC(Ordering* ord) : _cc(ord), _tis(), _groundTerms() {}

  void attach(SaturationAlgorithm* salg) override;
  void detach() override;
  
  ClauseIterator generateClauses(Clause* premise) override;

private:
  void handleEquality(Literal* lit, Clause* cl);
  void handleGroundTerm(Term* t);

  SimpleCongruenceClosure _cc;
  TermSubstitutionTree _tis;
  DHSet<Term*> _groundTerms;
  DHMap<Literal*,Clause*> _groundLitToClauseMap;
  Stack<Term*> _unprocessedGroundTerms;
  TermIndex* _lhsIndex;
};

};

#endif // __UnitEqualityCC__
