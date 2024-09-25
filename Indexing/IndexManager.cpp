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
 * @file IndexManager.cpp
 * Implements class IndexManager.
 */

#include "Indexing/Index.hpp"
#include "Lib/Exception.hpp"

#include "Kernel/Grounder.hpp"

#include "Saturation/SaturationAlgorithm.hpp"

#include "AcyclicityIndex.hpp"
#include "CodeTreeInterfaces.hpp"
#include "GroundingIndex.hpp"
#include "LiteralIndex.hpp"
#include "LiteralSubstitutionTree.hpp"
#include "TermIndex.hpp"
#include "TermSubstitutionTree.hpp"

#include "Shell/Statistics.hpp"

#include "IndexManager.hpp"

using namespace Lib;
using namespace Indexing;

IndexManager::IndexManager(SaturationAlgorithm* alg) 
  : _alg(alg) 
  , _uwa(AbstractionOracle::create())
  , _uwaFixedPointIteration(env.options->unificationWithAbstractionFixedPointIteration())
{ }

Index* IndexManager::request(IndexType t)
{
  Entry e;
  if(_store.find(t,e)) {
    e.refCnt++;
  } else {
    e.index=create(t);
    e.refCnt=1;
  }
  _store.set(t,e);
  return e.index;
}

void IndexManager::release(IndexType t)
{
  Entry e=_store.get(t);

  e.refCnt--;
  if(e.refCnt==0) {
    delete e.index;
    _store.remove(t);
  } else {
    _store.set(t,e);
  }
}

bool IndexManager::contains(IndexType t)
{
  return _store.find(t);
}

/**
 * If IndexManager contains index @b t, return pointer to it
 *
 * The pointer can become invalid after return from the code that
 * has requested it through this function.
 */
Index* IndexManager::get(IndexType t)
{
  return _store.get(t).index;
}

/**
 * Provide index form the outside
 *
 * There must not be index of the same type from before.
 * The provided index is never deleted by the IndexManager.
 */
void IndexManager::provideIndex(IndexType t, Index* index)
{
  ASS(!_store.find(t));

  Entry e;
  e.index = index;
  e.refCnt = 1; //reference to 1, so that we never delete the provided index
  _store.set(t,e);
}

Index* IndexManager::create(IndexType t)
{
  Index* res;
  using TermSubstitutionTree    = Indexing::TermSubstitutionTree<TermLiteralClause>;
  using LiteralSubstitutionTree = Indexing::LiteralSubstitutionTree<LiteralClause>;

  bool isGenerating;
                   
  switch(t) {
  case BINARY_RESOLUTION_SUBST_TREE:
    res = new BinaryResolutionIndex(new LiteralSubstitutionTree());
    isGenerating = true;
    break;
  case BACKWARD_SUBSUMPTION_SUBST_TREE:
    res = new BackwardSubsumptionIndex(new LiteralSubstitutionTree(IF_HOL(SplittingAlgo::HOL_MATCH, SplittingAlgo::NONE)));
    isGenerating = false;
    break;
  case FW_SUBSUMPTION_UNIT_CLAUSE_SUBST_TREE:
    res = new UnitClauseLiteralIndex(new LiteralSubstitutionTree(IF_HOL(SplittingAlgo::HOL_MATCH, SplittingAlgo::NONE)));
    isGenerating = false;
    break;
  case URR_UNIT_CLAUSE_SUBST_TREE:
    res = new UnitClauseLiteralIndex(new LiteralSubstitutionTree());
    isGenerating = true;
    break;
  case URR_UNIT_CLAUSE_WITH_AL_SUBST_TREE:
    res = new UnitClauseWithALLiteralIndex(new LiteralSubstitutionTree());
    isGenerating = true;
    break;
  case URR_NON_UNIT_CLAUSE_SUBST_TREE:
    res = new NonUnitClauseLiteralIndex(new LiteralSubstitutionTree());
    isGenerating = true;
    break;
  case URR_NON_UNIT_CLAUSE_WITH_AL_SUBST_TREE:
    res = new NonUnitClauseWithALLiteralIndex(new LiteralSubstitutionTree());
    isGenerating = true;
    break;

  case SUPERPOSITION_SUBTERM_SUBST_TREE:
    res = new SuperpositionSubtermIndex(new TermSubstitutionTree(IF_HOL(SplittingAlgo::HOL_UNIF, SplittingAlgo::NONE)), _alg->getOrdering());
    isGenerating = true;
    break;

  case SUPERPOSITION_LHS_SUBST_TREE:
    res = new SuperpositionLHSIndex(new TermSubstitutionTree(IF_HOL(SplittingAlgo::HOL_UNIF, SplittingAlgo::NONE)), _alg->getOrdering(), _alg->getOptions());
    isGenerating = true;
    break;

  
  case SKOLEMISING_FORMULA_INDEX:
    res = new SkolemisingFormulaIndex(new Indexing::TermSubstitutionTree<TermWithValue<Kernel::TermList>>(IF_HOL(SplittingAlgo::HOL_MATCH, SplittingAlgo::NONE), IF_HOL(true, false)));
    isGenerating = false;
    break;

   case ACYCLICITY_INDEX:
    res = new AcyclicityIndex(new TermSubstitutionTree());
    isGenerating = true;
    break; 

  case DEMODULATION_SUBTERM_SUBST_TREE:
    if (env.getMainProblem()->isHigherOrder()) {
      res = new DemodulationSubtermIndex<DemodulationSubtermIt>(new TermSubstitutionTree(SplittingAlgo::HOL_MATCH));
    } else {
      res = new DemodulationSubtermIndex<NonVariableNonTypeIterator>(new TermSubstitutionTree());
    }
    isGenerating = false;
    break;

  case DEMODULATION_LHS_CODE_TREE:
    res = new DemodulationLHSIndex(new CodeTreeTIS<DemodulatorData>(), _alg->getOrdering(), _alg->getOptions());
    isGenerating = false;
    break;

    case DEMODULATION_LHS_SUBST_TREE:
      res = new DemodulationLHSIndex(new Indexing::TermSubstitutionTree<DemodulatorData>(IF_HOL(SplittingAlgo::HOL_MATCH, SplittingAlgo::NONE)),
      _alg->getOrdering(),
      _alg->getOptions());

      isGenerating = false;
      break;

  case FW_SUBSUMPTION_CODE_TREE:
    res = new CodeTreeSubsumptionIndex();
    isGenerating = false;
    break;

  case FW_SUBSUMPTION_SUBST_TREE:
    res = new FwSubsSimplifyingLiteralIndex(new LiteralSubstitutionTree(IF_HOL(SplittingAlgo::HOL_MATCH, SplittingAlgo::NONE)));
    isGenerating = false;
    break;

  case FSD_SUBST_TREE:
    res = new FSDLiteralIndex(new LiteralSubstitutionTree(IF_HOL(SplittingAlgo::HOL_MATCH, SplittingAlgo::NONE)));
    isGenerating = false;
    break;

  case REWRITE_RULE_SUBST_TREE:
    res = new RewriteRuleIndex(new LiteralSubstitutionTree(IF_HOL(SplittingAlgo::HOL_MATCH, SplittingAlgo::NONE)), _alg->getOrdering());
    isGenerating = false;
    break;

  case GLOBAL_SUBSUMPTION_INDEX:
    res = new GroundingIndex(_alg->getOptions());
    isGenerating = false;
    break;

  case UNIT_INT_COMPARISON_INDEX:
    res = new UnitIntegerComparisonLiteralIndex(new LiteralSubstitutionTree());
    isGenerating = true;
    break;

  case INDUCTION_TERM_INDEX:
    res = new InductionTermIndex(new TermSubstitutionTree());
    isGenerating = true;
    break;

  case STRUCT_INDUCTION_TERM_INDEX:
    res = new StructInductionTermIndex(new TermSubstitutionTree());
    isGenerating = true;
    break;

  default:
    INVALID_OPERATION("Unsupported IndexType.");
  }
  if(isGenerating) {
    res->attachContainer(_alg->getGeneratingClauseContainer());
  }
  else {
    res->attachContainer(_alg->getSimplifyingClauseContainer());
  }
  return res;
}
