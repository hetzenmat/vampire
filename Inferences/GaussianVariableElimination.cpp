
  /*
   * File GaussianVariableElimination.cpp.
   *
   * This file is part of the source code of the software program
   * Vampire. It is protected by applicable
   * copyright laws.
   *
   * This source code is distributed under the licence found here
   * https://vprover.github.io/license.html
   * and in the source directory
   */

#include "GaussianVariableElimination.hpp"
#include "Kernel/Rebalancing.hpp"
#include "Kernel/Rebalancing/Inverters.hpp"
#include "Kernel/Clause.hpp"
#include "Kernel/EqHelper.hpp"
#include "Kernel/InterpretedLiteralEvaluator.hpp"
#include "Inferences/InterpretedEvaluation.hpp"
#include "Kernel/PolynomialNormalizer.hpp"
#include "Shell/Statistics.hpp"
#include "Lib/Option.hpp"

#define DEBUG(...)  DBG(__VA_ARGS__)

namespace Inferences {

using Inverter = Kernel::Rebalancing::Inverters::NumberTheoryInverter;
using Balancer = Kernel::Rebalancing::Balancer<Inverter>;
using InversionResult = Kernel::Rebalancing::InversionResult;

SimplifyingGeneratingInference1::Result GaussianVariableElimination::simplify(Clause* in, bool doCheckOrdering) 
{
  CALL("GaussianVariableElimination::simplify")
  ASS(in)

  auto& cl = *in;
  
  Option<std::tuple<TermList, InversionResult, unsigned>> leastGuards;
  for(unsigned i = 0; i < cl.size(); i++) {
    auto& lit = *cl[i];
    if (lit.isEquality() && lit.isNegative()) { 
      for (auto& b : Balancer(lit, Inverter(_generateGuards))) {

        /* found a rebalancing: lhs = rhs[lhs, ...] */
        auto lhs = b.lhs();
        auto rhs = b.buildRhs();
        ASS_REP(lhs.isVar(), lhs);

        if (!rhs.term.containsSubterm(lhs)) {
          /* lhs = rhs[...] */
          DEBUG(lhs, " -> ", rhs.term, " (with guards ", rhs.guards, ")");
          if (rhs.guards.size() == 0) {
            return rewrite(cl, lhs, std::move(rhs), i, doCheckOrdering);

          } else if (leastGuards.isNone() 
              || rhs.guards.size() < get<1>(leastGuards.unwrap()).guards.size() ) {
            leastGuards = decltype(leastGuards)(std::make_tuple(lhs, std::move(rhs), i));
          }
        }
      }
    }
  }
  if (leastGuards.isSome()) {
    auto& b = leastGuards.unwrap();
    return rewrite(cl, get<0>(b), std::move(get<1>(b)), get<2>(b), doCheckOrdering);
  } else {
    return SimplifyingGeneratingInference1::Result{in, false};
  }
}

SimplifyingGeneratingInference1::Result GaussianVariableElimination::rewrite(Clause& cl, TermList find, InversionResult rebalance, unsigned skipLiteral, bool doCheckOrdering) const 
{
  CALL("GaussianVariableElimination::rewrite");
  env.statistics->gveCnt++;

  Inference inf(SimplifyingInference1(Kernel::InferenceRule::GAUSSIAN_VARIABLE_ELIMINIATION, &cl));

  bool premiseRedundant = true;

  auto checkLeq = [&](Literal* orig, Literal* rewritten) 
  { 
    if (doCheckOrdering) {
      if (rewritten != orig && rewritten->isEquality()) {
        // as soon as we rewrite some clause x /= t \/ C[x] into C[t], the result will be incomparable
        // since the weight of t will be at least as big as the weight of x, hence we C[t] won't be smaller 
        // than C[x]. 
        // For non-equality literals this argument is not true, since in vampire equality literals are bigger than the ones with other predicates (due to our transfinite-ish KBO)
        // Hence, as we always get rid of one equality in gve we can make other predicates bigger if we want.

        // as soon as we rewrite some clause x /= t \/ C[x] into C[t], the result will be incomparable
        // since the weight of t will be at least as big as the weight of x, hence we C[t] won't be smaller 
        // than C[x]
        premiseRedundant = false;
      }
    }
    return rewritten;
  };

  auto sz = cl.size() - 1 + rebalance.guards.size(); 
  Clause& out = *new(sz) Clause(sz, inf); 
  for (unsigned i = 0; i < skipLiteral; i++) {
    out[i] = checkLeq(cl[i], EqHelper::replace(cl[i], find, rebalance.term));
  }

  for (unsigned i = skipLiteral; i < cl.size() - 1; i++)  {
    out[i] = checkLeq(cl[i+1], EqHelper::replace(cl[i+1], find, rebalance.term));
  }

  for (unsigned i = 0; i < rebalance.guards.size(); i++) {
    out[cl.size() - 1 + i] = rebalance.guards[i];
  }

  if (doCheckOrdering && !Inverter::guardsRedundant(cl, skipLiteral, find, rebalance, out, _ordering)) {
    premiseRedundant = false;
  }
  

  if(!premiseRedundant) {
    env.statistics->gveViolations++;
  }

  return SimplifyingGeneratingInference1::Result{&out, premiseRedundant};
}

} // namespace Inferences 
