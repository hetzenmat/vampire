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
 * @file HOLSubstitutionTree.hpp
 */

#ifndef __HOLSubstitutionTree__
#define __HOLSubstitutionTree__

#include "TermSubstitutionTree.hpp"
#include "Kernel/Term.hpp"

#include <Kernel/HOL/ToPlaceholders.hpp>

namespace Indexing {

using namespace Kernel;

template<class Data>
class HOLSubstitutionTree final : public TermIndexingStructure<Data>  {

  using ResultIt = VirtualIterator<QueryRes<ResultSubstitutionSP, Data>>;
public:
  VirtualIterator<QueryRes<AbstractingUnifier*, Data>> getUwa(TypedTermList t, Options::UnificationWithAbstraction uwa, bool fixedPointIteration) override { NOT_IMPLEMENTED; }
  ResultIt getHOLUnifiers(TypedTermList t) override { NOT_IMPLEMENTED; }
  ResultIt getHOLInstances(TypedTermList t, bool retrieveSubstitutions) override  { NOT_IMPLEMENTED;; }
  ResultIt getHOLGeneralizations(TypedTermList t) override  { NOT_IMPLEMENTED; }

  void handle(Data d, bool insert) override {
    // replace higher-order terms with placeholder constants

    // if(env.getMainProblem()->isHigherOrder() && _algo == SplittingAlgo::HOL_UNIF) {
    //   // replace higher-order terms with placeholder constants
    //   //tt = TypedTermList(ToPlaceholders().replace(tt), tt.sort());
    //   THROW_MH("");
    // }

    inner.handle({ HOL::toPlaceholders(d.key()), d}, insert);
  }

  void output(std::ostream& out) const override { out << *this; }

  friend std::ostream& operator<<(std::ostream& out, HOLSubstitutionTree const& self) {
    return out << self.inner;
  }

  friend std::ostream& operator<<(std::ostream& out, OutputMultiline<HOLSubstitutionTree> const& self) {
    return out << multiline(self.self.inner, self.indent);
  }

private:

  struct LeafData {
    TypedTermList skeleton;
    Data original;

    TypedTermList const& key() const {
      return skeleton;
    }

    std::tuple<const TypedTermList &, const Data &> asTuple() const {
      return std::tie(skeleton, original);
    }

    IMPL_COMPARISONS_FROM_TUPLE(LeafData)

    friend std::ostream& operator<<(std::ostream& out, LeafData const& self) {
      return out << "LeafData(skeleton = " << self.skeleton << ", original = " << self.original << ")";
    }
  };

  TermSubstitutionTree<LeafData> inner;

};
}

#endif // __HOLSubstitutionTree__
