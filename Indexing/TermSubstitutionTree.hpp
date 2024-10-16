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
 * @file TermSubstitutionTree.hpp
 * Defines class TermSubstitutionTree.
 */


#ifndef __TermSubstitutionTree__
#define __TermSubstitutionTree__


#include "Forwards.hpp"
#include "Kernel/UnificationWithAbstraction.hpp"
#include "Kernel/Renaming.hpp"
#include "Kernel/TypedTermList.hpp"
#include "Lib/BiMap.hpp"

#include "Index.hpp"
#include "TermIndexingStructure.hpp"
#include "SubstitutionTree.hpp"
#include "Kernel/HOLUnification.hpp"

namespace Indexing {

/*
 * As of 22/03/2023 TermSubstitutionTrees carry our type checking.
 * Thus, there is no need to check whether the type of returned terms match those of the query
 * as this is now done within the tree.
 */


/** A wrapper class around SubstitutionTree that makes it usable  as a TermIndexingStructure */
template<class LeafData_>
class TermSubstitutionTree
: public TermIndexingStructure<LeafData_>
{
  using SubstitutionTree            = Indexing::SubstitutionTree<LeafData_>;
  using TermIndexingStructure       = Indexing::TermIndexingStructure<LeafData_>;
  using BindingMap                  = typename SubstitutionTree::BindingMap;
  using Node                        = typename SubstitutionTree::Node;
  using FastInstancesIterator       = typename SubstitutionTree::FastInstancesIterator;
  using FastGeneralizationsIterator = typename SubstitutionTree::FastGeneralizationsIterator;
  using LDIterator                  = typename SubstitutionTree::LDIterator;
  using Leaf                        = typename SubstitutionTree::Leaf;
  using LeafIterator                = typename SubstitutionTree::LeafIterator;
  using HOLAlgo = UnificationAlgorithms::HOLUnification;
  using HOLInstAlgo = UnificationAlgorithms::HOLInstantiation;
  using HOLGenAlgo = UnificationAlgorithms::HOLGeneralisation;

  Indexing::SubstitutionTree<LeafData_> _inner;
public:
  using LeafData = LeafData_;

  TermSubstitutionTree(Indexing::SubstitutionTree<LeafData_> inner, SplittingAlgo algo, bool extra)
    : _inner(std::move(inner)), _extra(extra), _algo(algo)
  { }

  TermSubstitutionTree(SplittingAlgo algo = SplittingAlgo::NONE, bool extra = false)
    : TermSubstitutionTree(decltype(_inner)(), algo, extra)
  { }


  void handle(LeafData d, bool insert) final override {
    // if(env.getMainProblem()->isHigherOrder() && _algo == SplittingAlgo::HOL_UNIF) {
    //   // replace higher-order terms with placeholder constants
    //   //tt = TypedTermList(ToPlaceholders().replace(tt), tt.sort());
    //   THROW_MH("");
    // }

    _inner.handle(std::move(d), insert);
  }

  void useExtra() {
    _extra = true;
  }

private:

  /*
   * The extra flag is a higher-order concern. it is set to true when
   * we require the term query result to include two terms, the result term
   * and another.
   *
   * The main use case is to store a different term in the leaf to the one indexed
   * in the tree. This is used for example in Skolemisation on the fly where we
   * store Terms of type $o (formulas) in the tree, but in the leaf we store
   * the skolem terms used to witness them (to facilitate the reuse of Skolems)
   */
  bool _extra; // TODO remove this (?)
  SplittingAlgo _algo;

  std::function<void(const char*, unsigned, const LeafData_&)> log = [](const char* file, unsigned line, const LeafData_& x) {};

  template<class Iterator, class... Args>
  auto getResultIterator(TypedTermList query, bool retrieveSubstitutions, Args... args)
  { 
    return iterTraits(_inner.template iterator<Iterator>(query, retrieveSubstitutions, /* reversed */  false, std::move(args)...))
      ; }

  bool generalizationExists(TermList t) override
  { return t.isVar() ? false : _inner.generalizationExists(TypedTermList(t.term())); }

  virtual void output(std::ostream& out) const final override { out << *this; }

  friend std::ostream& operator<<(std::ostream& out, TermSubstitutionTree const& self)
  { return out << self._inner; }
  friend std::ostream& operator<<(std::ostream& out, OutputMultiline<TermSubstitutionTree> const& self)
  { return out << multiline(self.self._inner, self.indent); }

public:
  VirtualIterator<Indexing::QueryRes<ResultSubstitutionSP, LeafData_>> getInstances(TypedTermList t, bool retrieveSubstitutions) final override
  { return pvi(getResultIterator<FastInstancesIterator>(t, retrieveSubstitutions)); }

  VirtualIterator<QueryRes<ResultSubstitutionSP, LeafData>> getGeneralizations(TypedTermList t, bool retrieveSubstitutions) final override
  { return pvi(getResultIterator<FastGeneralizationsIterator>(t, retrieveSubstitutions)); }


  VirtualIterator<QueryRes<AbstractingUnifier*, LeafData>> getUwa(TypedTermList t, Options::UnificationWithAbstraction uwa, bool fixedPointIteration) final override
  { return pvi(getResultIterator<typename SubstitutionTree::template Iterator<RetrievalAlgorithms::UnificationWithAbstraction>>(t, /* retrieveSubstitutions */ true, AbstractionOracle(uwa), fixedPointIteration)); }

  VirtualIterator<QueryRes<ResultSubstitutionSP, LeafData>> getUnifications(TypedTermList t, bool retrieveSubstitutions) override
  { return pvi(getResultIterator<typename SubstitutionTree::template Iterator<RetrievalAlgorithms::RobUnification>>(t, retrieveSubstitutions)); }

  VirtualIterator<QueryRes<ResultSubstitutionSP, LeafData>> getHOLUnifiers(TypedTermList t) final override {
    THROW_MH("");
  }

  VirtualIterator<QueryRes<ResultSubstitutionSP, LeafData>> getHOLInstances(TypedTermList t, bool retrieveSubstitutions = true) final override {
    return pvi(getResultIterator<FastInstancesIterator>(t, retrieveSubstitutions));
  }

  VirtualIterator<QueryRes<ResultSubstitutionSP, LeafData>> getHOLGeneralizations(TypedTermList t) final override {
    std::cout << multiline(*this, 4) << std::endl;
    return pvi(getResultIterator<FastInstancesIterator>(t, true));
    // return pvi(getResultIterator<SubstitutionTree::TreeIterator<HOLGenAlgo>>(t, true));
  }
};

} // namespace Indexing

#endif /* __TermSubstitutionTree__ */
