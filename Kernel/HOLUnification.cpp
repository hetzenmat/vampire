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
* @file HOLUnification.cpp
* Defines class HOLUnification.
 */

#include "Kernel/HOLUnification.hpp"
#include "Kernel/ApplicativeHelper.hpp"

#include "Indexing/TermSharing.hpp"

#include "Lib/SkipList.hpp"

namespace Kernel
{
namespace UnificationAlgorithms
{

bool HOLUnification::unifyWithPlaceholders(TermSpec t1, TermSpec t2, RobSubstitution* sub)
{
  // TODO deal with the case where both terms are fully first-order...

  if (t1 == t2) {
    return true;
  }

  auto impl = [&]() -> bool {

    Recycled<Stack<std::pair<TermSpec, TermSpec>>> toDo;
    toDo->push({t1, t2});

    // Save encountered unification pairs to avoid
    // recomputing their unification
    Recycled<DHSet<std::pair<TermSpec,TermSpec>>> encountered;

    auto pushTodo = [&](std::pair<TermSpec,TermSpec> pair) {
      if (!encountered->find(pair)) {
        encountered->insert(pair);
        toDo->push(pair);
      }
    };

    while (toDo->isNonEmpty()) {
      auto x = toDo->pop();
      auto dt1 = sub->derefBound(x.first);
      auto dt2 = sub->derefBound(x.second);

      if (dt1 == dt2 || dt1.term.isPlaceholder() || dt2.term.isPlaceholder()) {
        // do nothing
        // we want unification to pass in these cases
      } else if(dt1.isVar() && !sub->occurs(dt1.varSpec(), dt2)) {
        sub->bind(dt1.varSpec(), dt2);
      } else if(dt2.isVar() && !sub->occurs(dt2.varSpec(), dt1)) {
        sub->bind(dt2.varSpec(), dt1);
      } else if(dt1.isTerm() && dt2.isTerm() && dt1.term.term()->functor() == dt2.term.term()->functor()) {

        for (unsigned i = 0; i < dt1.term.term()->arity(); i++) {
          pushTodo({dt1.nthArg(i), dt2.nthArg(i)});
        }

      } else {
        return false;
      }
    }
    return true;
  };

  BacktrackData localBD;
  sub->bdRecord(localBD);
  bool success = impl();
  sub->bdDone();

  if(!success) {
    localBD.backtrack();
  } else {
    if(sub->bdIsRecording()) {
      sub->bdCommit(localBD);
    }
    localBD.drop();
  }

  return success;
}

HOLUnification::OracleResult HOLUnification::fixpointUnify(TermSpec var, TermSpec t, RobSubstitution* sub)
{
  TermList v;
  // var can be an eta expanded var due to the normalisation of lambda prefixes
  // that takes place in iterator above
  if(!var.term.isEtaExpandedVar(v)) return OracleResult::OUT_OF_FRAGMENT;
  var = TermSpec(v, var.index); // set var to its eta-reduced variant

  struct TermListFP {
    TermSpec t;
    bool underFlex;
    unsigned depth;
  };

  bool tIsLambda = t.term.whnfDeref(sub).isLambdaTerm();
  TermSpec toFind = sub->root(var);
  TermSpec ts = sub->derefBound(t); // TODO do we even need this derefBound? Shouldn't t already be dereferenced???
  if (ts.isVar()) {
    if (toFind.isVar()) {
      sub->bind(toFind.varSpec(), ts);
    } else {
      auto glueVar = sub->introGlueVar(toFind);
      sub->bind(glueVar, ts);
    }

    return OracleResult::SUCCESS;
  }

  Recycled<Stack<TermListFP>> todo;
  todo->push(TermListFP { .t = t, .underFlex = false, .depth = 0,  });

  while (todo->isNonEmpty()){
    auto ts = todo->pop();
    auto term = ts.t.term.whnfDeref(sub);
    unsigned d = ts.depth;

    // TODO consider adding an encountered store similar to first-order occurs check...

    TermList head;
    TermStack args;

    while(term.isLambdaTerm()){
      term = term.lambdaBody();
      d++;
    }

    ApplicativeHelper::getHeadAndArgs(term, head, args);

    ASS(!head.isLambdaTerm());
    if (head.isVar()) {
      if(TermSpec(head, ts.t.index) == toFind) {
        if(ts.underFlex || (tIsLambda && args.size())){
          return OracleResult::OUT_OF_FRAGMENT;
        } else {
          return OracleResult::FAILURE;
        }
      }
    }

    if(head.deBruijnIndex().isSome()){
      unsigned index = head.deBruijnIndex().unwrap();
      if(index >= d){
        // contains a free index, cannot bind
        if(ts.underFlex){
          return OracleResult::OUT_OF_FRAGMENT;
        } else {
          return OracleResult::FAILURE;
        }
      }
    }

    bool argsUnderFlex = head.isVar() ? true : ts.underFlex;

    for(unsigned i = 0; i < args.size(); i++){
      todo->push(TermListFP { .t = TermSpec(args[i], ts.t.index), .underFlex = argsUnderFlex, .depth = d, } );
    }
  }

  if (toFind.isVar()) {
    sub->bind(toFind.varSpec(), ts);
  } else {
    auto glueVar = sub->introGlueVar(toFind);
    sub->bind(glueVar, ts);
  }

  return OracleResult::SUCCESS;
}

bool HOLUnification::associate(unsigned specialVar, TermSpec node, RobSubstitution* sub)
{
  return unifyWithPlaceholders(TermSpec(TermList::specialVar(specialVar), SPECIAL_INDEX), node, sub);
}

SubstIterator HOLUnification::unifiers(TermSpec t1, TermSpec t2, RobSubstitution* sub, bool topLevelCheck)
{

  if (env.options->applicativeUnify()) {
    if(sub->applicativeUnify(t1,t2)) {
      return pvi(getSingletonIterator(sub));
    }
    return SubstIterator::getEmpty();
  }

  if (t1.sameTermContent(t2)) return pvi(getSingletonIterator(sub));

  if (topLevelCheck) {
    // if topLevelCheck is set, we want to check that we
    // don't return a constraint of the form t1 != t2
    if (t1.isVar() || t2.isVar()) {
      auto var = t1.isVar() ? t1 : t2;
      auto otherTerm = var == t1 ? t2 : t1;
      auto res = fixpointUnify(var,otherTerm,sub);
      if(res == OracleResult::SUCCESS) return pvi(getSingletonIterator(sub));
      if(res == OracleResult::FAILURE) return SubstIterator::getEmpty();
      if(res == OracleResult::OUT_OF_FRAGMENT) return SubstIterator::getEmpty();
    } else {
      if(!ApplicativeHelper::splittable(t1.term, true) || !ApplicativeHelper::splittable(t2.term, true)) {
        return SubstIterator::getEmpty();
      }
    }
  }

  return vi(new HigherOrderUnifiersIt(t1, t2, sub, _funcExt));
}

}
}