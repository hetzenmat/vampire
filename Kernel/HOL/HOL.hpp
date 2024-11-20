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
 * @file HOL.hpp
 */

#ifndef __HOL__
#define __HOL__

#include "Kernel/Signature.hpp"
#include "Kernel/TypedTermList.hpp"

namespace HOL {

  using namespace Kernel;

  TermList app(TermList sort, TermList head, TermList arg);
  TermList app(TermList head, TermList arg);
  TermList app(TermList s1, TermList s2, TermList arg1, TermList arg2, bool shared = true);
  TermList app(TermList sort, TermList head, TermStack& terms); // todo const termstack
  TermList app(TermList head, TermStack& terms);

  inline TermList app2(TermList sort, TermList head, TermList arg1, TermList arg2) {
    return app(app(sort, head, arg1), arg2);
  }

  TermList app2(TermList head, TermList arg1, TermList arg2);

  TermList lambda(TermList varSort, TermList termSort, TermList term);
  TermList lambda(TermList varSort, TermList term);

  TermList matrix(TermList t);

  TermList getDeBruijnIndex(int index, TermList sort);

  TermList placeholder(TermList sort);

  TermList getNthArg(TermList arrowSort, unsigned argNum);
  TermList getResultApplieadToNArgs(TermList arrowSort, unsigned argNum);
  unsigned getArity(TermList sort);

  void getHeadAndArgs(TermList term, TermList& head, TermStack& args);

  inline void getHeadAndArgs(Term* term, TermList& head, TermStack& args) {
    getHeadAndArgs(TermList(term), head, args);
  }

  inline void getHeadAndArgs(const Term* term, TermList& head, TermStack& args) {
    getHeadAndArgs(const_cast<Term*>(term),head,args);
  }

  void getHeadSortAndArgs(TermList term, TermList& head, TermList& headSort, TermStack& args);
  void getHeadArgsAndArgSorts(TermList t, TermList& head, TermStack& args, TermStack& argSorts);

  TermList lhsSort(TermList t);
  TermList rhsSort(TermList t);

  void getMatrixAndPrefSorts(TermList t, TermList& matrix, TermStack& sorts);
  void getArgSorts(TermList t, TermStack& sorts);
  Signature::Proxy getProxy(const TermList& t);

  void getAbstractionTerms(Literal* lit, TermStack& terms);

  // returns true if we can split (decompose) term
  // during first-order unification without losing HOL
  // unifiers. Return false otherwise
  // Assumes that t is in head normal form
  bool splittable(TermList t, bool topLevel = false);

  inline bool isTrue(TermList term) { return term.isTerm() && env.signature->isFoolConstantSymbol(true, term.term()->functor()); }

  inline bool isFalse(TermList term) { return term.isTerm() && env.signature->isFoolConstantSymbol(false, term.term()->functor()); }

  inline bool isBool(TermList t) { return isTrue(t) || isFalse(t); }

  inline bool canHeadReduce(const TermList& head, const TermStack& args) { return head.isLambdaTerm() && args.size(); }

  bool isEtaExpandedVar(TermList t, TermList& var);

  void normaliseLambdaPrefixes(TermList& t1, TermList& t2);

  bool getProjAndImitBindings(TermList flexTerm, TermList rigidTerm, TermStack& bindings, TermList& freshVar);

  // creates a general binding of the form head (FV1 db1 ... dbn) (FV2 db1 ... dbn) ...
  // if surround is set to true, the general binding is surround by n lambdas
  TermList createGeneralBinding(TermList& freshVar, TermList head, TermStack& sorts, bool surround = true);

  TermList surroundWithLambdas(TermList t, TermStack& sorts, bool fromTop = false);
  TermList surroundWithLambdas(TermList t, TermStack& sorts, TermList sort, bool fromTop = false);

  inline TermList top() { return TermList(Term::foolTrue()); }

  inline TermList bottom() { return TermList(Term::foolFalse()); }

  inline TermList conj() { return TermList(Term::createConstant(env.signature->getBinaryProxy("vAND"))); }

  inline TermList disj() {return TermList(Term::createConstant(env.signature->getBinaryProxy("vOR"))); }

  inline TermList imp() { return TermList(Term::createConstant(env.signature->getBinaryProxy("vIMP"))); }

  inline TermList neg() { return TermList(Term::createConstant(env.signature->getNotProxy())); }

  inline TermList equality(TermList sort) { return TermList(Term::create1(env.signature->getEqualityProxy(), sort)); }

  inline TermList pi(TermList sort) { return TermList(Term::create1(env.signature->getPiSigmaProxy("vPI"), sort)); }

  inline TermList sigma(TermList sort) { return TermList(Term::create1(env.signature->getPiSigmaProxy("vSIGMA"), sort)); }

  TermList betaNF(TermList t);

  TermList etaNF(TermList t);

  inline TermList betaEtaNF(TermList t) {
    return etaNF(betaNF(t));
  }

  TypedTermList toPlaceholders(TypedTermList t);
}

#endif // __HOL__
