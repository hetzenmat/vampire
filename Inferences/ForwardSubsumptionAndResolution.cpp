/*
 * This file is part of the source code of the software program
 * Vampire. It is protected by applicable
 * copyright laws.
 *
 * This source code is distributed under the licence found here
 * https://vprover.github.io/license.htmlmatch2.
 * and in the source directory
 */
/**
 * @file ForwardSubsumptionAndResolution.cpp
 * Implements class ForwardSubsumptionAndResolution. The oracle is used to ensure consistent
 * branching in the forward subsumption and resolution inference.
 */

#include "Inferences/InferenceEngine.hpp"
#include "Saturation/SaturationAlgorithm.hpp"
#include "Indexing/LiteralIndex.hpp"
#include "Kernel/ColorHelper.hpp"

#include "Inferences/ForwardSubsumptionAndResolution.hpp"

namespace Inferences {
using namespace std;
using namespace Lib;
using namespace Kernel;
using namespace Indexing;
using namespace Saturation;

ForwardSubsumptionAndResolution::ForwardSubsumptionAndResolution(bool subsumptionResolution, bool log)
    : _subsumptionResolution(subsumptionResolution)
    , satSubs(log || CORRELATE_LENGTH_TIME)
{
}

void ForwardSubsumptionAndResolution::attach(SaturationAlgorithm *salg)
{
  ForwardSimplificationEngine::attach(salg);
  _unitIndex = static_cast<UnitClauseLiteralIndex *>(
      _salg->getIndexManager()->request(FW_SUBSUMPTION_UNIT_CLAUSE_SUBST_TREE));
  _fwIndex = static_cast<FwSubsSimplifyingLiteralIndex *>(
      _salg->getIndexManager()->request(FW_SUBSUMPTION_SUBST_TREE));
}

void ForwardSubsumptionAndResolution::detach()
{
  _unitIndex = 0;
  _fwIndex = 0;
  _salg->getIndexManager()->release(FW_SUBSUMPTION_UNIT_CLAUSE_SUBST_TREE);
  _salg->getIndexManager()->release(FW_SUBSUMPTION_SUBST_TREE);
  ForwardSimplificationEngine::detach();
}

/// @brief Set of clauses that were already checked
static DHSet<Clause *> checkedClauses;

bool ForwardSubsumptionAndResolution::perform(Clause *cl,
                                              Clause *&replacement,
                                              ClauseIterator &premises)
{
  TIME_TRACE("forward subsumption");

  satSubs.beginLoop(cl);

  ASS(replacement == nullptr)

  unsigned clen = cl->length();
  if (clen == 0) {
    return false;
  }

  /// @brief Conclusion of the subsumption resolution if successful
  Clause *conclusion = nullptr;
  /// @brief Premise of either subsumption or subsumption resolution
  Clause *premise = nullptr;

  checkedClauses.reset();

  Clause *mcl;

  /*******************************************************/
  /*              SUBSUMPTION UNIT CLAUSE                */
  /*******************************************************/
  // In case of unit clauses, no need to check subsumption since
  // L = a where a is a single literal
  // M = b v C where sigma(a) = b is a given from the index
  // Therefore L subsumes M
  for (unsigned li = 0; li < clen; li++) {
    Literal *lit = (*cl)[li];
    auto it = _unitIndex->getGeneralizations(lit, false, false);
    if (it.hasNext()) {
      mcl = it.next().clause;
      premise = mcl;
      ASS(ColorHelper::compatible(cl->color(), premise->color()))
      premises = pvi(getSingletonIterator(premise));
      return true;
    }
  }

  /*******************************************************/
  /*       SUBSUMPTION & RESOLUTION MULTI-LITERAL        */
  /*******************************************************/
  // For each clauses mcl, first check for subsumption, then for subsumption resolution
  // During subsumption, setup the subsumption resolution solver. This is an overhead
  // largely compensated because the success rate of subsumption is fairly low, and
  // in case of failure, having the solver ready is a great saving on subsumption resolution
  //
  // Since subsumption is stronger than subsumption, if a subsumption resolution check is found,
  // keep it until the end of the loop to make sure no subsumption is possible.
  // Only when it has been checked that subsumption is not possible does the conclusion of
  // subsumption resolution become relevant
  for (unsigned li = 0; li < clen; li++) {
    Literal *lit = (*cl)[li];
    auto it = _fwIndex->getGeneralizations(lit, false, false);
    while (it.hasNext()) {
      mcl = it.next().clause;
      if (!checkedClauses.insert(mcl)) {
        continue;
      }

      bool checkSR = _optimizedLoop && _subsumptionResolution && !conclusion &&
          (_checkLongerClauses || mcl->length() <= clen);

      // if mcl is longer than cl, then it cannot subsume cl but still could be resolved
      bool checkS = mcl->length() <= clen;
      if (checkS) {
        if (satSubs.checkSubsumption(mcl, cl, checkSR)) {
          ASS(replacement == nullptr)
          premises = pvi(getSingletonIterator(mcl));
          return true;
        }
      }
      if (checkSR) {
        // In this case, the literals come from the non complementary list, and there is therefore
        // a low chance of it being resolved. However, in the case where there is no negative match,
        // checkSubsumption resolution is very fast after subsumption, since filling the match set
        // for subsumption will have already detected that subsumption resolution is impossible
        conclusion = satSubs.checkSubsumptionResolution(mcl, cl, checkS);
        if (conclusion) {
          ASS(premise == nullptr)
          // cannot override the premise since the loop would have ended otherwise
          // the premise will be overriden if a subsumption is found
          premise = mcl;
        }
      }
    }
  }

  if (conclusion) {
    premises = pvi(getSingletonIterator(premise));
    replacement = conclusion;
    return true;
  }
  else if (!_subsumptionResolution) {
    return false;
  }

  /*******************************************************/
  /*         SUBSUMPTION RESOLUTION UNIT CLAUSE          */
  /*******************************************************/
  // In case of unit clauses, no need to check subsumption resolution since
  // L = a where a is a single literal
  // M = ~b v C where sigma(a) = ~b is a given from the index
  // Therefore M can be replaced by C
  //
  // This behavior can be chained and several resolution can happen at the same time
  // The negatively matching literals are stacked and removed at the same time
  for (unsigned li = 0; li < clen; li++) {
    Literal *lit = (*cl)[li];
    auto it = _unitIndex->getGeneralizations(lit, true, false);
    if (it.hasNext()) {
      mcl = it.next().clause;
      ASS(mcl->length() == 1)
      replacement = SATSubsumption::SATSubsumptionAndResolution::getSubsumptionResolutionConclusion(cl, lit, mcl);
      premises = pvi(getSingletonIterator(mcl));
      return true;
    }
  }

  if (!_optimizedLoop) {
    /*******************************************************/
    /*        SUBSUMPTION RESOLUTION MULTI-LITERAL         */
    /*******************************************************/
    // Check for the clauses positively matched in the index.
    // If the loop is optimized, this would already have been done during subsumption
    checkedClauses.reset();
    for (unsigned li = 0; li < clen; li++) {
      Literal *lit = (*cl)[li];
      auto it = _fwIndex->getGeneralizations(lit, false, false);
      while (it.hasNext()) {
        mcl = it.next().clause;
        if (!checkedClauses.insert(mcl)) {
          continue;
        }
        if (!_checkLongerClauses && mcl->length() > clen) {
          continue;
        }
        conclusion = satSubs.checkSubsumptionResolution(mcl, cl, false);
        if (conclusion) {
          ASS(premise == nullptr)
          premise = mcl;
          replacement = conclusion;
          premises = pvi(getSingletonIterator(premise));
          return true;
        }
      }
    }
  }

  /*******************************************************/
  /*        SUBSUMPTION RESOLUTION MULTI-LITERAL         */
  /*******************************************************/
  // Check for the last clauses that are negatively matched in the index.
  for (unsigned li = 0; li < clen; li++) {
    Literal *lit = (*cl)[li];
    auto it = _fwIndex->getGeneralizations(lit, true, false);
    while (it.hasNext()) {
      mcl = it.next().clause;
      if (!checkedClauses.insert(mcl)) {
        continue;
      }
      if (!_checkLongerClauses && mcl->length() > clen) {
        continue;
      }
      conclusion = satSubs.checkSubsumptionResolution(mcl, cl);
      if (conclusion) {
        ASS(premise == nullptr)
        premise = mcl;
        replacement = conclusion;
        premises = pvi(getSingletonIterator(premise));
        return true;
      }
    }
  }

  return false;
}  // perform


} // namespace Inferences
