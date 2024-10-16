/*
 * This file is part of the source code of the software program
 * Vampire. It is protected by applicable
 * copyright laws.
 *
 * This source code is distributed under the licence found here
 * https://vprover.github.io/license.html
 * and in the source directory
 */


#include "Indexing/SubstitutionTree.hpp"
#include "Indexing/TermSubstitutionTree.hpp"
#include "Lib/Coproduct.hpp"
#include "Test/SyntaxSugar.hpp"
#include <memory>



namespace SubsTreeBuilder  {
  using namespace Indexing;

  template<class Data>
  struct Internal;

  template<class Data>
  struct Leaf {
    TermList term;
    Stack<Data> data;
  };

  template<class Data>
  using NodeCP = Coproduct<Leaf<Data>, std::shared_ptr<Internal<Data>>>;

  template<class Data>
  struct Node : public NodeCP<Data> {
    template<class A>
    Node(A a) : NodeCP<Data>(std::move(a)) {}
  };


  template<class Data>
  struct Internal {
    TermList term;
    unsigned var;
    Stack<Node<Data>> children;
    Internal(TermList term, unsigned var, Stack<Node<Data>> children) : term(term), var(var), children(std::move(children)) {}
  };

  template<class Data>
  Node<Data> internal(TermList term, unsigned var, Stack<Node<Data>> children) 
  { return Node<Data>(std::make_shared<Internal<Data>>(term, var, std::move(children))); }

  template<class Data>
  Node<Data> internal(TermList term, unsigned var, std::initializer_list<Node<Data>> children) 
  { return internal(term,var,Stack<Node<Data>>(children)); }

  template<class Data>
  Node<Data> leaf(TermList term, std::initializer_list<Data> data) 
  { return Node<Data>(Leaf<Data>{term, std::move(data),}); }

  template<class Data>
  Node<Data> root(unsigned var, Stack<Node<Data>> children) 
  { return internal(TermList(), var, children); }

  template<class Data>
  unsigned nextVar(Leaf<Data> const& node)
  { return 0; }

  template<class Data>
  unsigned nextVar(std::shared_ptr<Internal<Data>> const& node){
    return arrayIter(node->children)
        .map([](auto& child) { return nextVar(child); })
        .max().unwrapOr(0);
  }

  template<class Data>
  unsigned nextVar(Node<Data> const& node) 
  { return node.apply([](auto& x){ return nextVar(x); }); }


  template<class Data>
  typename SubstitutionTree<Data>::Node* toTreeNode(Leaf<Data> const& node)
  {
    auto out = SubstitutionTree<Data>::createLeaf(node.term);
    for (auto x : node.data) {
      out->insert(x);
    }
    return out;
  }

  template<class Data>
  typename SubstitutionTree<Data>::Node* toTreeNode(std::shared_ptr<Internal<Data>> const& node){
    auto out = SubstitutionTree<Data>::createIntermediateNode(node->term, node->var);
    for (auto c : node->children) {
      out->addChild(toTreeNode(c));
    }
    return out;
  }

  template<class Data>
  typename SubstitutionTree<Data>::Node* toTreeNode(Node<Data> const& node) 
  { return node.apply([](auto& x){ return toTreeNode(x); }); }

  template<class Data>
  SubstitutionTree<Data> subsTree(unsigned var, std::initializer_list<Node<Data>> children) 
  { return subsTree(var, Stack<Node<Data>>(children)); }

  template<class Data>
  SubstitutionTree<Data> subsTree(unsigned var, Stack<Node<Data>> children) 
  { 
    auto treeBuilder = internal(TermList(), var, std::move(children));
    return SubstitutionTree<Data>(toTreeNode(treeBuilder), nextVar(treeBuilder)); 
  }


  template<class Data>
  TermSubstitutionTree<Data> termSubsTree(unsigned var, std::initializer_list<Node<Data>> children) 
  { return TermSubstitutionTree<Data>(subsTree(var, std::move(children)), SplittingAlgo::NONE, /*extra=*/ false); }

  inline TermList S(unsigned i) 
  { return TermList::specialVar(i); }

} // namespace SubsTreeBuilder
