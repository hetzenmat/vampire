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
 * @file TermTransformer.hpp
 * Defines class TermTransformer.
 */

#ifndef __TermTransformer__
#define __TermTransformer__

#include "Forwards.hpp"
#include "Term.hpp"
#include "TypedTermList.hpp"


namespace Kernel {

/**
 * Common methods of TermTransformer and BottomUpTermTransformer extracted here.
 */
class TermTransformerCommon {
public:
  Literal* transformLiteral(Literal* lit);
  virtual Formula* transform(Formula* f) = 0;
  virtual Term* transform(Term* term) = 0;
protected:
  Term* transformSpecial(Term* specialTerm);
  virtual TermList transform(TermList ts) = 0;
};

/**
 * Class to allow for easy transformations of subterms in shared literals.
 *
 * The inheriting class implements function transformSubterm(TermList)
 * and then the functions transform(Literal*)/transform(Term*) use it to transform subterms
 * of the given literal/term.
 *
 * The literal and subterms returned by the transformSubterm(TermList) function have
 * to be shared.
 *
 * This class can be used to transform sort arguments as well by suitably
 * implementing the transformSubterm(TermList) function
 *
 * TermTransformer goes top down but does no recurse into the replaced term
 *
 * Note that if called via transform(Term* term) the given term itself will not get transformed, only possibly its proper subterms
 */
class TermTransformer : public TermTransformerCommon {
public:
  virtual ~TermTransformer() {}
  TermTransformer() : _sharedResult(true),
                      _dontTransformSorts(false) {}
  Term *transform(Term *term) override;

  Formula* transform(Formula* f) override;
  TermList transform(TermList ts) override;

  void dontTransformSorts() { _dontTransformSorts = true; }

protected:
  virtual TermList transformSubterm(TermList trm) = 0;

  virtual void onTermEntry(Term*){}
  virtual void onTermExit(Term*){}

  virtual bool exploreSubterms(TermList orig, TermList newTerm);

  bool _sharedResult;
  bool _dontTransformSorts;

  private:
  template<class T>
  Term* create(Term* t, TermList* argLst, bool shared)
  {  return shared ? T::create(static_cast<T*>(t), argLst) :  T::createNonShared(static_cast<T*>(t), argLst); }  
};

class SubtermReplacer : public TermTransformer {
public:
  SubtermReplacer(TermList what, TermList by, bool liftFree = false)
      : _what(what), _by(by), _liftFreeIndices(liftFree), _shiftBy(0)
  {
    ASS(what.isVar() || by.isVar() || SortHelper::getResultSort(what.term()) == SortHelper::getResultSort(by.term()));
    dontTransformSorts();
  }

  TermList transformSubterm(TermList t) override;

  Literal* transformLit(Literal* lit)
  {
    Term* t = transform(static_cast<Term*>(lit));
    ASS(t->isLiteral());
    return static_cast<Literal*>(t);
  }

// #if VHOL
  void onTermEntry(Term* t) override;
  void onTermExit(Term* t) override;
// #endif

private:
  TermList _what;
  TermList _by;

  // #if VHOL
  bool _liftFreeIndices; // true if need to lift free indices in _what
  int _shiftBy; // the amount to shift a free index by
  // #endif
};

class ToBank : public TermTransformer
{
public:
  explicit ToBank(VarBank bank) : _bank(bank) {}

  Term*         toBank(Term* t) { return transform(t); }
  Literal*      toBank(Literal* lit) { return transformLiteral(lit); }
  TypedTermList toBank(TypedTermList term);

  TermList transformSubterm(TermList t) override;
  bool exploreSubterms(TermList orig, TermList newTerm) override;
private:
  VarBank _bank;
};

/**
 * Has similar philosophy to TermTransformer, but:
 *  goes bottom up and so subterms of currently considered terms
 *  might already be some replacements that happened earlier, e.g.:
 *  transforming g(f(a,b)) will consider (provided transformSubterm is the identity function)
 *  the following sequence: a,b,f(a,b),g(f(a,b))
 *  and if transformSubterm is the identitify everywhere except for f(a,b) for which it returns c,
 *  the considered sequence will be: a,b,f(a,b)->c,g(c)
 */
class BottomUpTermTransformer : public TermTransformerCommon {
public:
  virtual ~BottomUpTermTransformer() {}
  Term* transform(Term* term) override;
protected:
  virtual TermList transformSubterm(TermList trm) = 0;
  Formula* transform(Formula* f) override;
  TermList transform(TermList ts) override;
};


}

#endif // __TermTransformer__
