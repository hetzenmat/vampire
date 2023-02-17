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
 * @file Clause.hpp
 * Defines class Clause for units consisting of clauses
 *
 * @since 09/05/2007 Manchester
 */

#ifndef __Clause__
#define __Clause__

#include <iosfwd>

#include "Forwards.hpp"

#include "Lib/Allocator.hpp"
#include "Lib/Event.hpp"
#include "Lib/InverseLookup.hpp"
#include "Lib/Metaiterators.hpp"
#include "Lib/Reflection.hpp"
#include "Lib/Stack.hpp"
#include "Lib/Environment.hpp"

#include "Unit.hpp"
#include "TermIterators.hpp"
#include "Kernel/Inference.hpp"
#include "Kernel/Term.hpp"

namespace Kernel {

using namespace Lib;

/**
 * Class to represent clauses.
 * @since 10/05/2007 Manchester
 *
 * When creating a clause object, several things usually need to be done
 * besides calling a constructor:
 * - Fill the Clause with Literals
 * - Increase a relevant counter in the env.statistics object
 */
class Clause
  : public Unit
{
private:
  /** Should never be used, declared just to get rid of compiler warning */
  ~Clause() { ASSERTION_VIOLATION; }
  /** Should never be used, just that compiler requires it */
  void operator delete(void* ptr) { ASSERTION_VIOLATION; }

  template<class VarIt>
  void collectVars2(DHSet<unsigned>& acc);
public:
  typedef ArrayishObjectIterator<const Clause> Iterator;

  DECL_ELEMENT_TYPE(Literal*);
  DECL_ITERATOR_TYPE(Iterator);

  /** Storage kind */
  enum Store {
    /** passive clause */
    PASSIVE = 0u,
    /** active clause */
    ACTIVE = 1u,
    /** queue of unprocessed clauses */
    UNPROCESSED = 2u,
    /** anything else */
    NONE = 3u,
    /** clause is selected from the passive container
     * and is not added to the active one yet */
    SELECTED = 4u
  };

  Clause(unsigned length,const Inference& inf);

  void* operator new(size_t,unsigned length);
  void operator delete(void* ptr,unsigned length);

  static Clause* fromStack(const Stack<Literal*>& lits, const Inference& inf);

  template<class Iter>
  static Clause* fromIterator(Iter litit, const Inference& inf)
  {
    CALL("Clause::fromIterator");

    static Stack<Literal*> st;
    st.reset();
    st.loadFromIterator(litit);
    return fromStack(st, inf);
  }

  static Clause* fromClause(Clause* c);

  /**
   * Return the (reference to) the nth literal
   *
   * Positions of literals in the clause are cached in the _literalPositions
   * object. In order to keep it in sync, content of the clause can be changed
   * only right after clause construction (before the first call to the
   * getLiteralPosition method), or during the literal selection (as the
   * _literalPositions object is updated in call to the setSelected method).
   */
  Literal*& operator[] (int n)
  { return _literals[n]; }
  /** Return the (reference to) the nth literal */
  Literal*const& operator[] (int n) const
  { return _literals[n]; }

  class FeatureIterator {
    Clause* _cl;
    unsigned _featureId;
    unsigned _pLen;
    unsigned _nLen;
    unsigned _justEq;
    unsigned _justNeq;
    unsigned _numVarOcc;

  public:
    static constexpr const unsigned NUM_FEATURES = 14;

    FeatureIterator(Clause* cl) :
      _cl(cl), _featureId(0),
      _pLen(0), _nLen(0), _justEq(1), _justNeq(1),
      _numVarOcc(0) { }

    void computeGenLengthAndVarOcc() {
      for (unsigned i = 0; i < _cl->length(); i++) {
        Literal* l = (*_cl)[i];
        _numVarOcc += l->numVarOccs();
        if (l->isPositive()) { _pLen++; } else { _nLen++; }
        if (l->isEquality()) { _justNeq = 0; } else { _justEq = 0; }
      }
    }

    bool hasNext() {
      return _featureId < NUM_FEATURES;
    }

    double next() {
      Inference& inf = _cl->inference();

      // TODO: could add, e.g., a one hot encoding of the deriving inference rules

      switch (_featureId++) {
        // good old AW
        case 0:
          return _cl->age();
        case 1:
          return _cl->weight();

        case 2:
          return _cl->length();

        case 3:
          computeGenLengthAndVarOcc();
          return _pLen;

        case 4:
          return _nLen;

        case 5:
          return _justEq;
        case 6:
          return _justNeq;

        case 7:
          return _numVarOcc;
        case 8:
          return (double)_numVarOcc/(double)_cl->weight();

        // CAREFUL: check in Preprocess.cpp the lines relavant to initializing the sine levels when changing the feature codes

        // SineLevels
        case 9:  // redundant: the same as SineLevel == 0
          return (_cl->derivedFromGoal() ? 1.0 : 0.0);
        case 10: // redundant: the same as SineLevel == 255
          return (inf.getSineLevel() == std::numeric_limits<decltype(inf.getSineLevel())>::max()) ? 1.0 : 0.0;
        case 11:
          if (inf.getSineLevel() == std::numeric_limits<decltype(inf.getSineLevel())>::max()) {
            return 1.0;
          } else if (inf.getSineLevel() == 0) {
            return 0.0;
          } else {
            ASS_G(env.maxSineLevel,2);
            return (0.5 * inf.getSineLevel()) / (env.maxSineLevel - 2);
          }

        // a bit of AVATAR
        case 12:
          return _cl->splitWeight();

        default:
          ASSERTION_VIOLATION;

        // TODO: add stuff regarding arithmetic
        // << (c->isPureTheoryDescendant() ? '1' : '0') << " "
        // << inf.th_ancestors << " "
        // << inf.all_ancestors << " "
        // << inf.th_ancestors / inf.all_ancestors << endl;
      }
    }
  };

  /** Return the length (number of literals) */
  unsigned length() const { return _length; }
  /** Alternative name for length to conform with other containers */
  unsigned size() const { return _length; }

  /** Return a pointer to the array of literals.
   * Caller should not manipulate literals, with the exception of
   * clause construction and literal selection. */
  Literal** literals() { return _literals; }

  /** True if the clause is empty */
  bool isEmpty() const { return _length == 0; }

  void destroy();
  void destroyExceptInferenceObject();
  vstring literalsOnlyToString() const;
  vstring toString() const;
  vstring toTPTPString() const;
  vstring toNiceString() const;

  /** Return the clause store */
  Store store() const { return _store; }
  void setStore(Store s);

  /** Return the age */
  unsigned age() const { return inference().age(); }
  /** Set the age to @b a */
  void setAge(unsigned a) { inference().setAge(a); }

  /** Return the number of selected literals */
  unsigned numSelected() const { return _numSelected; }
  /** Mark the first s literals as selected */
  void setSelected(unsigned s)
  {
    ASS(s >= 0);
    ASS(s <= _length);
    _numSelected = s;
    notifyLiteralReorder();
  }

  /** Return the weight */
  unsigned weight() const
  {
    if(!_weight) {
      _weight = computeWeight();
    }
    return _weight;
  }
  unsigned computeWeight() const;

  /**
   * weight used for clause selection
   */
  unsigned weightForClauseSelection(const Shell::Options& opt)
  {
    if(!_weightForClauseSelection) {
      _weightForClauseSelection = computeWeightForClauseSelection(opt);
    }
    return _weightForClauseSelection;
  }
  unsigned computeWeightForClauseSelection(const Shell::Options& opt) const;

  /*
   * single source of truth for computation of weightForClauseSelection
   */
  static unsigned computeWeightForClauseSelection(unsigned w, unsigned splitWeight, unsigned numeralWeight, bool derivedFromGoal, const Shell::Options& opt);

  /** Return the color of a clause */
  Color color() const
  {
    if(static_cast<Color>(_color)==COLOR_INVALID) {
      computeColor();
    }
    return static_cast<Color>(_color);
  }
  void computeColor() const;
  void updateColor(Color c) {
    _color = c;
  }

  bool isExtensionality() const { return _extensionality; }
  bool isTaggedExtensionality() const { return _extensionalityTag; }
  void setExtensionality(bool e) { _extensionality = e; }

  bool isComponent() const { return _component; }
  void setComponent(bool c) { _component = c; }

  bool skip() const;

  unsigned getLiteralPosition(Literal* lit);
  void notifyLiteralReorder();

  bool shouldBeDestroyed();
  void destroyIfUnnecessary();

  void incRefCnt() { _refCnt++; }
  void decRefCnt()
  {
    CALL("Clause::decRefCnt");

    ASS_G(_refCnt,0);
    _refCnt--;
    destroyIfUnnecessary();
  }

  unsigned getReductionTimestamp() { return _reductionTimestamp; }
  void invalidateMyReductionRecords()
  {
    _reductionTimestamp++;
    if(_reductionTimestamp==0) {
      INVALID_OPERATION("Clause reduction timestamp overflow!");
    }
  }
  bool validReductionRecord(unsigned savedTimestamp) {
    return savedTimestamp == _reductionTimestamp;
  }

  ArrayishObjectIterator<Clause> getSelectedLiteralIterator()
  { return ArrayishObjectIterator<Clause>(*this,numSelected()); }

  ArrayishObjectIterator<Clause> iterLits() &
  { return ArrayishObjectIterator<Clause>(*this,size()); }

  ArrayishObjectIterator<Clause, const_ref_t> iterLits() const&
  { return ArrayishObjectIterator<Clause, const_ref_t>(*this,size()); }

  ArrayishObjectIterator<Clause> getLiteralIterator()
  { return ArrayishObjectIterator<Clause>(*this,size()); }

  bool isGround();
  bool isPropositional();
  bool isHorn();

  VirtualIterator<unsigned> getVariableIterator();

  bool contains(Literal* lit);
#if VDEBUG
  void assertValid();
#endif

  SplitSet* splits() const { return _inference.splits(); }
  bool noSplits() const;

  /**
   * set splits
   * in order to keep all splitting-related functionality separate from Saturation,
   * the splits are not set during clause-construction but are added later by the Splitter-class.
   * we depend on the invariant that splits are set only once, and that splits are set before clause-weights are
   * computed and cached (which happens at the first call to weight())
   */
  void setSplits(SplitSet* splits) {
    CALL("Clause::setSplits");

    ASS(_weight == 0);
    _inference.setSplits(splits);
  }
   

  int getNumActiveSplits() const { return _numActiveSplits; }
  void setNumActiveSplits(int newVal) { _numActiveSplits = newVal; }
  void incNumActiveSplits() { _numActiveSplits++; }
  void decNumActiveSplits() { _numActiveSplits--; }

  VirtualIterator<vstring> toSimpleClauseStrings();

  void setAux()
  {
    ASS(_auxInUse);
    _auxTimestamp=_auxCurrTimestamp;
  }

  /** Set auxiliary value of this clause. */
  void setAux(void* ptr)
  {
    ASS(_auxInUse);
    _auxTimestamp=_auxCurrTimestamp;
    _auxData=ptr;
  }
  /**
   * If there is an auxiliary value stored in this clause,
   * return true and assign it into @b ptr. Otherwise
   * return false.
   */
  template<typename T>
  bool tryGetAux(T*& ptr)
  {
    ASS(_auxInUse);
    if(_auxTimestamp==_auxCurrTimestamp) {
      ptr=static_cast<T*>(_auxData);
      return true;
    }
    return false;
  }
  /** Return auxiliary value stored in this clause. */
  template<typename T>
  T* getAux()
  {
    ASS(_auxInUse);
    ASS(_auxTimestamp==_auxCurrTimestamp);
    return static_cast<T*>(_auxData);
  }
  bool hasAux()
  {
    return _auxTimestamp==_auxCurrTimestamp;
  }

  /**
   * Request usage of the auxiliary value in clauses.
   * All aux. values stored in clauses before are guaranteed
   * to be discarded.
   */
  static void requestAux()
  {
#if VDEBUG
    ASS(!_auxInUse);
    _auxInUse=true;
#endif
    _auxCurrTimestamp++;
    if(_auxCurrTimestamp==0) {
      INVALID_OPERATION("Auxiliary clause value timestamp overflow!");
    }
  }
  /**
   * Announce that the auxiliary value in clauses is no longer
   * in use and can be used by someone else.
   */
  static void releaseAux()
  {
#if VDEBUG
    ASS(_auxInUse);
    _auxInUse=false;
#endif
  }

  unsigned splitWeight() const;
  unsigned getNumeralWeight() const;

  void collectVars(DHSet<unsigned>& acc);
  void collectUnstableVars(DHSet<unsigned>& acc);

  
  unsigned varCnt();
  unsigned maxVar(); // useful to create fresh variables w.r.t. the clause

  unsigned numPositiveLiterals(); // number of positive literals in the clause

protected:
  /** number of literals */
  unsigned _length : 20;
  /** clause color, or COLOR_INVALID if not determined yet */
  mutable unsigned _color : 2;
  /** Clause was matched as extensionality and is tracked in the extensionality
    * clause container. The matching happens at activation. If the clause
    * becomes passive and is removed from the container, also this bit is unset.
    */
  unsigned _extensionality : 1;
  unsigned _extensionalityTag : 1;
  /** Clause is a splitting component. */
  unsigned _component : 1;

  /** storage class */
  Store _store : 3;
  /** number of selected literals */
  unsigned _numSelected : 20;

  /** weight */
  mutable unsigned _weight;
  /** weight for clause selection */
  unsigned _weightForClauseSelection;

  /** number of references to this clause */
  unsigned _refCnt;
  /** for splitting: timestamp marking when has the clause been reduced or restored by splitting */
  unsigned _reductionTimestamp;
  /** a map that translates Literal* to its index in the clause */
  InverseLookup<Literal>* _literalPositions;

  int _numActiveSplits;

  size_t _auxTimestamp;
  void* _auxData;

  static size_t _auxCurrTimestamp;
#if VDEBUG
  static bool _auxInUse;
#endif

//#endif

  /** Array of literals of this unit */
  Literal* _literals[1];
}; // class Clause

std::ostream& operator<<(std::ostream& out, Clause::Store const& clause);
}

#endif
