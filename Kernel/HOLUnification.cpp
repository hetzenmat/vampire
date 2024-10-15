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

class HOLUnification::HigherOrderUnifiersIt: public IteratorCore<RobSubstitution*> {
public:

  TermList applyTypeSub(TermList t){
    THROW_MH(""); // Do we need to deal with type substitutions for TH0?
    // in the monomorphic case, should be cheap
    // return SortDeref(_subst).deref(t);
  }

  HigherOrderUnifiersIt(TermSpec t1, TermSpec t2, RobSubstitution *subst, bool funcExt)
      : _used(false), _solved(false), _topLevel(true), _funcExt(funcExt), _depth(0),
        _unifiersReturned(0), _freshVar(0, VarBank::FRESH_BANK), _subst(subst)
  {

    BacktrackData bd;
    _bdStack->push(bd);
    _bindings->push(TermStack());

    if (!trySolveTrivialPair(t1, t2)) {
      ASS(t1.isTerm() || t2.isTerm());
      auto [sort, sortIndex] = t1.isTerm()
          ? std::pair(SortHelper::getResultSort(t1.term.term()), t1.index)
          : std::pair(SortHelper::getResultSort(t2.term.term()), t2.index);
      //_unifPairs.insert(HOLConstraint(applyTypeSub(t1), applyTypeSub(t2)));
      _unifPairs.insert(HOLConstraint({t1.term, t1.index}, {t2.term, t2.index} /*, sort, sortIndex*/));
    }
  }

  friend std::ostream& operator<<(std::ostream& out, HigherOrderUnifiersIt const& self)
  { return out << "Backtrack depth " << self._bdStack->size() << "\nBindings " <<
        *self._bindings << "\nCurr subst " << *self._subst /*<< "\nUnif pairs " << self._unifPairs*/; }

  bool solved() {
    SkipList<HOLConstraint,HOLCnstComp>::RefIterator it(_unifPairs);
    return !it.hasNext() || it.next().flexFlex();
  }

  bool trySolveTrivialPair(TermSpec t1, TermSpec t2) {

    if(t1.isVar() && t2.isVar()){
      if(t1 == t2) return true;
      _subst->bdRecord(_bdStack->top());
      _subst->bind(t1.varSpec(), t2);
      _subst->bdDone();
      applyBindingToPairs();
      return true;
    }
    return false;
  }

  bool backtrack() {
    bool success = false;
    while (!_bdStack->isEmpty() && !success) {
      _depth--;
      _bdStack->pop().backtrack();
      // if there are alterntative bindings available stop bracktracking
      success = !_bindings->top().isEmpty();
    }
    return success;
  }

  void applyBindingToPairs(bool sort = false) {
    Stack<HOLConstraint> temp;
    while(!_unifPairs.isEmpty()){
      HOLConstraint pair = popFromUnifPairs(_bdStack->top());
      TermSpec lhs = pair.lhs();
      TermSpec rhs = pair.rhs();
      if(sort){
        temp.push(HOLConstraint(SortDeref(_subst, lhs.index).deref(lhs.term), SortDeref(_subst, rhs.index).deref(rhs.term)));
      } else {
        temp.push(HOLConstraint({lhs.term.whnfDeref(_subst), 0}, {rhs.term.whnfDeref(_subst), 0})); // TODO MH: adapt whnfDeref
      }
    }

    while(!temp.isEmpty()){
      addToUnifPairs(temp.pop(), _bdStack->top());
    }
  }

  bool hasNext() {
    static unsigned maxUnifiers = env.options->takeNUnifiersOnly();
    static unsigned depth       = env.options->higherOrderUnifDepth();

    if(_subst->bdIsRecording())
      _subst->bdDone();

    if(maxUnifiers && _unifiersReturned == maxUnifiers){
      return false;
    }

    if((_solved || solved()) && !_used) // the solved() check ensures that when we start with a flex-flex we return true straight away
    { return true; }

    _used = false;

    // the logic here is really convoluted and should be cleaned up
    // the main complexity is due to the depth limit
    // Once the limit is reached, we continue popping constraints until
    // we reach a flexRigid pair and then stop and return
    // The next time we call hasNext, the system will be in a solved state
    // if next() has been called in between, since next clears all unif
    // pairs. Hence a backtrack will take place

    bool forward = !solved() || backtrack();
    while(forward && !solved()){
      if(_unifPairs.top().flexRigid() && _depth == depth)
      {
        // if we are in pragmatic mode, when we hit the depth we backtrack
        // In standard mode we return a unifier with constraints
        if(env.options->pragmatic() && depth){
          forward = backtrack();
          continue;
        } else {
          break;
        }
      }

      auto con = popFromUnifPairs(_bdStack->top());

      int lhsIndex = con.lhs().index;
      int rhsIndex = con.rhs().index;
      TermList lhs = con.lhs().term;
      TermList rhs = con.rhs().term;
      TermList lhsHead = con.lhsHead();
      TermList rhsHead = con.rhsHead();

      ASS(!lhsHead.isVar() || !rhsHead.isVar()); // otherwise we would be solved
      ASS(lhs.isVar() || rhs.isVar() || SortHelper::getResultSort(lhs.term()) == SortHelper::getResultSort(rhs.term()));

      ApplicativeHelper::normaliseLambdaPrefixes(lhs, rhs);

      // normalising can change the head of a term if it is a De Bruijn index
      // TODO only recompute head if it has changed above...
      lhsHead = lhs.head();
      rhsHead = rhs.head();

      if (lhs == rhs) { continue; }

      if (con.rigidRigid()) {
        TermList s = con.sort();
        if (_funcExt && _depth == 0 && (s.isArrowSort() || s.isVar() || (s.isBoolSort() && !_topLevel))) {
          addToUnifPairs(con, _bdStack->top());
          break;
        }
      }

      if (con.rigidRigid() && lhsHead.term()->functor() == rhsHead.term()->functor()) {
        // unify type
        bool success = true;
        bool workDone = false;
        for (unsigned j = 0; j < lhsHead.term()->arity(); j++) {
          if (lhsHead.nthArg(j) != rhsHead.nthArg(j)) {
            workDone = true;
            BacktrackData tempBD;
            _subst->bdRecord(tempBD);
            success = _subst->unify({lhsHead.nthArg(j), lhsIndex}, {rhsHead.nthArg(j), rhsIndex});
            _subst->bdDone();
            if (!success) {
              tempBD.backtrack();
              forward = backtrack();
              break;
            } else {
              tempBD.commitTo(_bdStack->top());
              tempBD.drop();
            }
          }
        }

        if (!success) {
          continue;
        }

        if (workDone) {
          // we never reach here in the monomorphic case as workDone should always be false
          applyBindingToPairs(true);
        }

        lhs = applyTypeSub(lhs);
        rhs = applyTypeSub(rhs);

        TermStack lhsArgs;
        TermStack argSorts;
        TermStack rhsArgs;
        TermStack sorts;
        TermList matrix;
        ApplicativeHelper::getMatrixAndPrefSorts(lhs, matrix, sorts);
        ApplicativeHelper::getHeadArgsAndArgSorts(matrix, lhsHead, lhsArgs, argSorts);
        ApplicativeHelper::getHeadAndArgs(rhs, rhsHead, rhsArgs);
        ASS(lhsArgs.size() == rhsArgs.size()); // size must be same due to normalisation of prefixes above

        for(unsigned i = 0; i < lhsArgs.size(); i++){
          auto t1 = lhsArgs[i].whnfDeref(_subst);
          int t1Index = 0/0; // TODO MH;
          t1 = ApplicativeHelper::surroundWithLambdas(t1, sorts, argSorts[i], /* traverse stack from top */ true);
          auto t2 = rhsArgs[i].whnfDeref(_subst);
          int t2Index = 0/0; // TODO MH;
          t2 = ApplicativeHelper::surroundWithLambdas(t2, sorts, argSorts[i], true);

          if (!trySolveTrivialPair({t1, t1Index}, {t2, t2Index})) {
            addToUnifPairs(HOLConstraint({t1, t1Index}, {t2, t2Index}), _bdStack->top());
          }
        }

      } else if(con.flexRigid()) {
        auto [flexTerm, flexTermIndex]  = lhsHead.isVar() ? std::pair(lhs, lhsIndex) : std::pair(rhs, rhsIndex);
        auto [rigidTerm, rigidTermIndex] = lhsHead.isVar() ? std::pair(rhs, rhsIndex) : std::pair(lhs, lhsIndex);
        auto [flexHead, flexHeadIndex]  = lhsHead.isVar() ? std::pair(lhsHead, lhsIndex) : std::pair(rhsHead, rhsIndex);

        if(_bdStack->size() == _bindings->size()){
          // reached here not via a backtrack. Need to add new bindings to bindings

          // oracle calls. no point calling oracles if we reach here via a backtrack
          // they must have already failed
          BacktrackData tempBD;
          _subst->bdRecord(tempBD);
          auto res = HOLUnification::fixpointUnify({flexTerm, flexTermIndex}, {rigidTerm, rigidTermIndex}, _subst);
          _subst->bdDone();

          if (res == OracleResult::OUT_OF_FRAGMENT) {
            tempBD.backtrack(); // don't think we need this, as we won't have bound anyhting...
            // TODO pattern oracle
            // TODO solid oracle?
          } else if (res == OracleResult::SUCCESS) {
            tempBD.commitTo(_bdStack->top());
            tempBD.drop();
            applyBindingToPairs();
            continue; // TODO apply new binding to pairs...???
          } else {
            forward = backtrack();
            continue;
          }

          TermStack projAndImitBindings;
          BacktrackData& bd = _bdStack->top();
          bd.addClosure([this, fv = _freshVar](){ _freshVar = fv; });

          ApplicativeHelper::getProjAndImitBindings(flexTerm, rigidTerm, projAndImitBindings, _freshVar);

          if(projAndImitBindings.isEmpty()){
            // no bindings for this pair of terms
            forward = backtrack();
            continue;
          }

          backtrackablePush(*_bindings,projAndImitBindings,bd);
        }

        _depth++;
        addToUnifPairs(con, _bdStack->top()); // add back to pairs with old data
        BacktrackData bd;
        _bdStack->push(bd); // reached a branch point

        ASS(_bindings->top().size());
        TermList binding = _bindings->top().pop();

        _subst->bdRecord(_bdStack->top());
        _subst->bind(VarSpec(flexHead.var(), flexHeadIndex), {binding, 0/0 /* TODO MH */ });
        _subst->bdDone();

        applyBindingToPairs();

      } else {
        // clash
        forward = backtrack();
      }

      _topLevel = false;
    }

    if(forward) _solved = true;

    return forward;
  }

  RobSubstitution* next() {
    // turn remaining unification pairs into standard constraints
    // these can either be the flex-flex pairs, or if depth limit reached
    // these can include other pairs as well
    BacktrackData& bd = _bdStack->top();
    if (!_subst->bdIsRecording()) {
      _subst->bdRecord(bd);
    }
    while (!_unifPairs.isEmpty()) {
      ASS(_subst->bdIsRecording());
      HOLConstraint con = popFromUnifPairs(bd);
      if (!trySolveTrivialPair(con.lhs(), con.rhs())) { // through head reduction a pair can become trivial
        //_subst->pushConstraint(con.constraint()); // TODO MH
      }
    }

    // don't stop recording here
    // instead, let RObSubstitution do its free variable renaming
    // on top member of BdStack, so that it is undone by a call to bactrack()
    _unifiersReturned++;
    _used = true;
    _solved = false;
    return _subst;
  }

  HOLConstraint popFromUnifPairs(BacktrackData& bd) {
    auto con = _unifPairs.pop();
    bd.addClosure([this, c = con](){ _unifPairs.insert(c); });
    return con;
  }

  void addToUnifPairs(HOLConstraint con, BacktrackData& bd) {
    _unifPairs.insert(con);
    bd.addClosure([this, c = con ](){ _unifPairs.remove(c); });
  }

private:

  class HOLCnstComp
  {
  public:
    inline static Comparison compare(const HOLConstraint& hc1, const HOLConstraint& hc2)
    {
      auto compareTerms = [](TermSpec t1, TermSpec t2){
        if(t1.isVar()){
          if(t2.isVar()){
            return (t1.term.isVar() < t2.term.var()) ? LESS : (t1.term.var() > t2.term.var())? GREATER : EQUAL;
          }
          return LESS;
        } else if(t2.isVar()){
          return GREATER;
        }

        unsigned id1 = t1.term.term()->getId();
        unsigned id2 = t2.term.term()->getId();

        return (id1<id2)? LESS : (id1>id2)? GREATER : EQUAL;
      };

      if(hc1.rigidRigid() && !hc2.rigidRigid()){
        return LESS;
      } else if (hc2.rigidRigid() && !hc1.rigidRigid()){
        return GREATER;
      } else if (hc1.flexRigid() && hc2.flexFlex()){
        return LESS;
      } else if (hc2.flexRigid() && hc1.flexFlex()){
        return GREATER;
      }

      auto res = compareTerms(hc1.lhs(), hc2.lhs());
      if(res == EQUAL){
        res = compareTerms(hc1.rhs(), hc2.rhs());
      }
      return res;
    }
  };

  bool _used;
  bool _solved;
  bool _topLevel;
  bool _funcExt;
  unsigned _depth;
  unsigned _unifiersReturned;
  SkipList<HOLConstraint,HOLCnstComp> _unifPairs;
  Recycled<Stack<BacktrackData>> _bdStack;
  Recycled<Stack<TermStack>> _bindings;
  TermList _freshVar;
  RobSubstitution* _subst;
};

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

class HigherOrderUnifiersIt;

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

SubstIterator HOLUnification::postprocess(RobSubstitution* sub, TermList t, TermList sort)
{
  // ignore the sub that has been passed in, since
  // that contains substitutions formed during tree traversal which
  // are not helpful here (but cannot be erased either!)
  TypedTermList res = ToBank(VarBank::RESULT_BANK).toBank(TypedTermList(t,sort));

  THROW_MH("");
  // return vi(new HigherOrderUnifiersItWrapper(_origQuery, _origQuerySort, res, res.sort(), _funcExt));
}

}
}
