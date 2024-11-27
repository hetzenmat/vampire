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
* @file HOLUnification.hpp
* Defines class HOLUnification.
*/

#ifndef __HOLUnification__
#define __HOLUnification__


#include "RobSubstitution.hpp"

#include "Kernel/Signature.hpp"
#include "Indexing/Index.hpp"

namespace Kernel
{

struct PartialUnifier {
  Indexing::ResultSubstitutionSP substitution;
  UnificationConstraintStack constraints;
};

using namespace Indexing;

namespace UnificationAlgorithms {

template <class Data>
class PreUnification {
public:
  using _ElementType = QueryRes<SmartPtr<PartialUnifier>, Data>;

  PreUnification& operator=(PreUnification&&) = default;
  PreUnification(PreUnification&&) = default;
  PreUnification(TypedTermList query, Data data, bool funcExt) {}
  PreUnification(TypedTermList query, Data data) : PreUnification(query, data, env.options->functionExtensionality() == Options::FunctionExtensionality::ABSTRACTION) {}
  bool hasNext() { NOT_IMPLEMENTED; }
  _ElementType next() { NOT_IMPLEMENTED; }

private:

};

// TODO if we implement solid fragment, this will not work...
enum class OracleResult {
  SUCCESS,
  FAILURE,
  OUT_OF_FRAGMENT
};

OracleResult fixpointUnify(TermSpec var, TermSpec t, RobSubstitution* sub) {

  // var can be an eta expanded var due to the normalisation of lambda prefixes

  auto res = var.term.isEtaExpandedVar();
  if (res.isNone())
    return OracleResult::OUT_OF_FRAGMENT;
  var = TermSpec(res.unwrap(), var.index);
}

//class HOLInstantiation;
//class HOLGeneralisation;

// class HOLConstraint //: public UnificationConstraint
//  {
// private:
//   TermSpec _lhs;
//   TermSpec _rhs;
//   TermList _t1head;
//   TermList _t2head;
// public:
//
//   HOLConstraint(){} // dummy constructor required for use in SkipList
//
//   // HOLConstraint(TermList t1, int t1index, TermList t2, int t2index)
//   HOLConstraint(TermSpec ll, TermSpec rr)
//       : // UnificationConstraint({t1,t1index}, {t2,t2index}, {sort,sortIndex}),
//         _lhs(ll),
//         _rhs(rr),
//         _t1head(ll.term.head()),
//         _t2head(rr.term.head())
//   {
//     ASS(!_t1head.isLambdaTerm() && !_t2head.isLambdaTerm()); // terms must be in whnf
//   }
//   //USE_ALLOCATOR(HOLConstraint)
//
//   TermSpec lhs() const { return _lhs; }
//   TermSpec rhs() const { return _rhs; }
//
//   bool flexFlex()   const { return _t1head.isVar() && _t2head.isVar(); }
//   bool rigidRigid() const { return _t1head.isTerm() && _t2head.isTerm(); }
//   bool flexRigid()  const { return (_t1head.isVar() && !_t2head.isVar())  || (_t2head.isVar() && !_t1head.isVar()); }
//
//   TermList lhsHead() const { return _t1head; }
//   TermList rhsHead() const { return _t2head; }
//
//   TermList sort() const {
//     ASS(_lhs.isTerm() || _rhs.isTerm());
//     if(_lhs.isTerm())
//     { return SortHelper::getResultSort(_lhs.term.term()); }
//     return SortHelper::getResultSort(_rhs.term.term());
//   }
//
//   HOLConstraint constraint() { return HOLConstraint(lhs(),rhs()); }
//  };
//
//
// class HigherOrderUnifiersIt;
//
// class HigherOrderUnifiersItWrapper/*: public IteratorCore<RobSubstitution*>*/ {
// public:
//   using _ElementType = RobSubstitution*;
//   // DECL_ELEMENT_TYPE(RobSubstitution*);
//   HigherOrderUnifiersItWrapper& operator=(HigherOrderUnifiersItWrapper&&) = default;
//   HigherOrderUnifiersItWrapper(HigherOrderUnifiersItWrapper&&) = default;
//   HigherOrderUnifiersItWrapper(TermSpec lhs, TermList lhsSort, TermSpec rhs, TermList rhsSort, bool funcExt);
//   bool hasNext();
//   RobSubstitution* next();
//
// private:
//   bool _success;
//   SubstIterator _inner;
//   Recycled<RobSubstitution> _subst;
// };
//
//
//
// class HOLUnification {
//  // when this class is used for tree unification the field
//  // below holds the original query before higher-order subterms have
//  // been replaced by placeholders
//  TermList _origQuery;
//  TermList _origQuerySort;
//  bool _funcExt;
//
//  // bool unifyWithPlaceholders(TermList t1, TermList t2, RobSubstitutionTL* sub);
//  bool unifyWithPlaceholders(TermSpec t1, TermSpec t2, RobSubstitution* sub);
//
//
//
//  inline bool sortCheck(TermList sort, bool topLevel = false){
//    return
//        _funcExt &&
//        (sort.isOrdinaryVar() || sort.isArrowSort() || (sort.isBoolSort() && !topLevel));
//  }
//
//
//
//
// public:
//
//   // static OracleResult fixpointUnify(TermList var, TermList t, RobSubstitutionTL* sub);
//   static OracleResult fixpointUnify(TermSpec var, TermSpec t, RobSubstitution* sub);
//
//
//
//  HOLUnification() : _funcExt( env.options->functionExtensionality() == Options::FunctionExtensionality::ABSTRACTION)
//  {}
//
//  HOLUnification(TypedTermList query)
//      : _funcExt( env.options->functionExtensionality() == Options::FunctionExtensionality::ABSTRACTION) {
//    TypedTermList t = ToBank(VarBank::QUERY_BANK).toBank(query);
//    _origQuery = t;
//    _origQuerySort = t.sort();
//  }
//
//  // bool associate(unsigned specialVar, TermList node, RobSubstitutionTL* sub);
//  bool associate(unsigned specialVar, TermSpec node, RobSubstitution* sub);
//
//  //SubstIterator unifiers(TermList t1, TermList t2, RobSubstitutionTL* sub, bool topLevelCheck = false);
//  SubstIterator unifiers(TermSpec t1, TermSpec t2, RobSubstitution* sub, bool topLevelCheck = false);
//
//  //SubstIterator postprocess(RobSubstitutionTL*, TermList t, TermList sort);
//  SubstIterator postprocess(RobSubstitution*, TermList t, TermList sort);
//
//  // void initSub(RobSubstitutionTL* sub) const { }
//  void initSub(RobSubstitution* sub) const { }
//
//  // method used to decide whether to return all children of a node during tree
//  // traversal or only the children with same top
//  bool usesUwa() const { return false; }
// };


}

}

#endif
