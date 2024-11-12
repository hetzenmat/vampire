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
 * @file ApplicativeHelper.hpp
 * Defines class ApplicativeHelper.
 */

#ifndef __ApplicativeHelper__
#define __ApplicativeHelper__

#include "Forwards.hpp"
#include "Kernel/Signature.hpp"
#include "Lib/Deque.hpp"
#include "Lib/BiMap.hpp"
#include "Kernel/TypedTermList.hpp"
#include "Kernel/TermTransformer.hpp"
#include "Kernel/RobSubstitution.hpp"
#include "Kernel/HOL/BetaNormaliser.hpp"
#include "Kernel/HOL/EtaNormaliser.hpp"

using namespace Kernel;
using namespace Shell;

namespace ApplicativeHelper {
  TermList app(TermList sort, TermList head, TermList arg);
  TermList app(TermList head, TermList arg);
  TermList app(TermList s1, TermList s2, TermList arg1, TermList arg2, bool shared = true);
  TermList app(TermList sort, TermList head, TermStack& terms); // todo const termstack
  TermList app(TermList head, TermStack& terms);

  inline TermList app2(TermList sort, TermList head, TermList arg1, TermList arg2) { return app(app(sort, head, arg1), arg2); }

  inline TermList app2(TermList head, TermList arg1, TermList arg2) {
    ASS(head.isTerm());

    TermList headSort = SortHelper::getResultSort(head.term());
    return app2(headSort, head, arg1, arg2);
  }

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

  inline TermList betaNF(TermList t) {
    return BetaNormaliser().normalise(t);
  }

  inline TermList etaNF(TermList t) {
    return EtaNormaliser().normalise(t);
  }

  inline TermList betaEtaNF(TermList t) {
    return etaNF(betaNF(t));
  }
}

class TermShifter : public TermTransformer
{
public:
  TermShifter() : _minFreeIndex(-1) {
    dontTransformSorts();
  }
  // positive value -> shift up
  // negative -> shift down
  // 0 record minimum free index
  TermList shift(TermList term, int shiftBy);
  TermList transformSubterm(TermList t) override;
  void onTermEntry(Term* t) override;
  void onTermExit(Term* t) override;
  bool exploreSubterms(TermList orig, TermList newTerm) override;

  Option<unsigned> minFreeIndex(){
    return _minFreeIndex > -1 ? Option<unsigned>((unsigned)_minFreeIndex) : Option<unsigned>();
  }

private:
  unsigned _cutOff; // any index higher than _cutOff is a free index
  int _shiftBy; // the amount to shift a free index by
  int _minFreeIndex;
};

class SortDeref : public TermTransformer
{
public:
  SortDeref(RobSubstitution* sub, int index) : _sub(sub), _index(index) {}
  explicit SortDeref(RobSubstitution* sub) : _sub(sub), _index(-1) {}

  TermSpec deref(TermList term);
  TermList transformSubterm(TermList t) override;
  void onTermEntry(Term* t) override;
  void onTermExit(Term* t) override;
  bool exploreSubterms(TermList orig, TermList newTerm) override;

private:
  RobSubstitution* _sub;
  int _index;
  Stack<unsigned> _typeArities;
  Stack<unsigned> _positions;
};


// replaces higher-order subterms (subterms with variable heads e.g., X a b &
// lambda terms) with a special polymorphic constant we call a "placeholder".
// Depending on the mode functional and Boolean subterms may also be replaced
class ToPlaceholders : public TermTransformer
{
public:
  ToPlaceholders()
      : _nextIsPrefix(false),
        _topLevel(true),
        _mode(env.options->functionExtensionality())
  {
    dontTransformSorts();
  }

  TermList replace(TermList term);
  TermList transformSubterm(TermList t) override;
  void onTermEntry(Term* t) override;
  void onTermExit(Term* t) override;

private:
  bool _nextIsPrefix;
  bool _topLevel;
  Shell::Options::FunctionExtensionality _mode;
};

#endif // __ApplicativeHelper__
