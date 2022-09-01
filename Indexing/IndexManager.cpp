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

Index* IndexManager::request(IndexType t)
{
  CALL("IndexManager::request");

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
  CALL("IndexManager::release");

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
  CALL("IndexManager::provideIndex");
  ASS(!_store.find(t));

  Entry e;
  e.index = index;
  e.refCnt = 1; //reference to 1, so that we never delete the provided index
  _store.set(t,e);
}

Index* IndexManager::create(IndexType t)
{
  CALL("IndexManager::create");

  Index* res;
  LiteralIndexingStructure* is;
  TermIndexingStructure* tis;

  bool isGenerating;
  static bool const useConstraints = env.options->unificationWithAbstraction()!=Options::UnificationWithAbstraction::OFF;
  static bool const extByAbs = (env.options->functionExtensionality() == Options::FunctionExtensionality::ABSTRACTION) &&
                    env.property->higherOrder();
                    
  switch(t) {
  case BINARY_RESOLUTION_SUBST_TREE:
    is=new LiteralSubstitutionTree(useConstraints);
    res=new BinaryResolutionIndex(is);
    isGenerating = true;
    break;
  case BACKWARD_SUBSUMPTION_SUBST_TREE:
    is=new LiteralSubstitutionTree();
    res=new BackwardSubsumptionIndex(is);
    isGenerating = false;
    break;
  case FW_SUBSUMPTION_UNIT_CLAUSE_SUBST_TREE:
    is=new LiteralSubstitutionTree();
    res=new UnitClauseLiteralIndex(is);
    isGenerating = false;
    break;
  case URR_UNIT_CLAUSE_SUBST_TREE:
    is=new LiteralSubstitutionTree();
    res=new UnitClauseLiteralIndex(is);
    isGenerating = true;
    break;
  case URR_NON_UNIT_CLAUSE_SUBST_TREE:
    is=new LiteralSubstitutionTree();
    res=new NonUnitClauseLiteralIndex(is);
    isGenerating = true;
    break;

  case SUPERPOSITION_SUBTERM_SUBST_TREE:
    tis=new TermSubstitutionTree(useConstraints, extByAbs);
    res=new SuperpositionSubtermIndex(tis, _alg->getOrdering());
    isGenerating = true;
    break;
  case SUPERPOSITION_LHS_SUBST_TREE:
    tis=new TermSubstitutionTree(useConstraints, extByAbs);
    res=new SuperpositionLHSIndex(tis, _alg->getOrdering(), _alg->getOptions());
    isGenerating = true;
    break;
    
  case SUB_VAR_SUP_SUBTERM_SUBST_TREE:
    //using a substitution tree to store variable.
    //TODO update
    tis=new TermSubstitutionTree();
    res=new SubVarSupSubtermIndex(tis, _alg->getOrdering());
    isGenerating = true;
    break;
  case SUB_VAR_SUP_LHS_SUBST_TREE:
    tis=new TermSubstitutionTree();
    res=new SubVarSupLHSIndex(tis, _alg->getOrdering(), _alg->getOptions());
    isGenerating = true;
    break;
  
  case SKOLEMISING_FORMULA_INDEX:
    tis=new TermSubstitutionTree(false, false, true);
    res=new SkolemisingFormulaIndex(tis);
    isGenerating = false;
    break;

  /*case RENAMING_FORMULA_INDEX:
    tis=new TermSubstitutionTree(false, false, true);
    res=new RenamingFormulaIndex(tis);
    attachPassive = true;
    break;*/

  case NARROWING_INDEX:
    tis=new TermSubstitutionTree();
    res=new NarrowingIndex(tis); 
    isGenerating = true;
    break; 

  case PRIMITIVE_INSTANTIATION_INDEX:
    tis=new TermSubstitutionTree();
    res=new PrimitiveInstantiationIndex(tis); 
    isGenerating = true;
    break;  
   case ACYCLICITY_INDEX:
    tis = new TermSubstitutionTree();
    res = new AcyclicityIndex(tis);
    isGenerating = true;
    break; 

  case DEMODULATION_SUBTERM_SUBST_TREE:
    tis=new TermSubstitutionTree();
    if (env.options->combinatorySup()) {
      res=new DemodulationSubtermIndexImpl<true>(tis);
    } else {
      res=new DemodulationSubtermIndexImpl<false>(tis);
    }
    isGenerating = false;
    break;
  case DEMODULATION_LHS_CODE_TREE:
    tis=new CodeTreeTIS();
    res=new DemodulationLHSIndex(tis, _alg->getOrdering(), _alg->getOptions());
    isGenerating = false;
    break;
  case REMODULATION_SUBTERM_INDEX:
    tis=new TermSubstitutionTree();
    res=new RemodulationSubtermIndex(tis);
    isGenerating = true;
    break;
  case REMODULATION_LHS_SUBST_TREE:
    tis=new TermSubstitutionTree();
    res=new RemodulationLHSIndex(tis, _alg->getOrdering());
    isGenerating = true;
    break;
  case REWRITING_LHS_INDEX:
    tis=new TermSubstitutionTree();
    res=new RewritingLHSIndex(tis, _alg->getOrdering());
    isGenerating = true;
    break;
  case REWRITING_SUBTERM_INDEX:
    tis=new TermSubstitutionTree();
    res=new RewritingSubtermIndex(tis);
    isGenerating = true;
    break;

  case DEMODULATION_LHS_SUBST_TREE:
    tis=new TermSubstitutionTree();
    res=new DemodulationLHSIndex(tis, _alg->getOrdering(), _alg->getOptions());
    isGenerating = false;
    break;

  case FW_SUBSUMPTION_CODE_TREE:
    res=new CodeTreeSubsumptionIndex();
    isGenerating = false;
    break;

  case FW_SUBSUMPTION_SUBST_TREE:
    is=new LiteralSubstitutionTree();
//    is=new CodeTreeLIS();
    res=new FwSubsSimplifyingLiteralIndex(is);
    isGenerating = false;
    break;

  case FSD_SUBST_TREE:
    is = new LiteralSubstitutionTree();
    res = new FSDLiteralIndex(is);
    isGenerating = false;
    break;

  case REWRITE_RULE_SUBST_TREE:
    is=new LiteralSubstitutionTree();
    res=new RewriteRuleIndex(is, _alg->getOrdering());
    isGenerating = false;
    break;

  case GLOBAL_SUBSUMPTION_INDEX:
    res = new GroundingIndex(_alg->getOptions());
    isGenerating = false;
    break;

  case UNIT_INT_COMPARISON_INDEX:
    is = new LiteralSubstitutionTree();
    res = new UnitIntegerComparisonLiteralIndex(is);
    isGenerating = true;
    break;

  case INDUCTION_UNIT_LITERAL_INDEX:
    is = new LiteralSubstitutionTree();
    res = new InductionUnitLiteralIndex(is);
    isGenerating = true;
    break;

  case INDUCTION_NON_GROUND_LITERAL_INDEX:
    is = new LiteralSubstitutionTree();
    res = new InductionNonGroundLiteralIndex(is);
    isGenerating = true;
    break;

  case INDUCTION_TERM_INDEX:
    tis = new TermSubstitutionTree();
    res = new InductionTermIndex(tis);
    isGenerating = true;
    break;

  case STRUCT_INDUCTION_TERM_INDEX:
    tis = new TermSubstitutionTree();
    res = new StructInductionTermIndex(tis);
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
