/**
 * @file EqHelper.cpp
 * Implements class EqHelper.
 */

#include "EqHelper.hpp"

namespace Kernel {

TermList EqHelper::getRHS(Literal* eq, TermList lhs)
{
  CALL("EqHelper::getRHS");
  ASS(eq->isEquality());

  if(*eq->nthArgument(0)==lhs) {
    return *eq->nthArgument(1);
  } else {
    ASS(*eq->nthArgument(1)==lhs);
    return *eq->nthArgument(0);
  }
}

Literal* EqHelper::replace(Literal* lit, TermList tSrc, TermList tDest)
{
  CALL("EqHelper::replace");
  ASS(lit->shared());

  static Stack<TermList*> toDo(8);
  static Stack<Term*> terms(8);
  static Stack<bool> modified(8);
  static Stack<TermList> args(8);
  ASS(toDo.isEmpty());
  ASS(terms.isEmpty());
  modified.reset();
  args.reset();

  modified.push(false);
  toDo.push(lit->args());

  for(;;) {
    TermList* tt=toDo.pop();
    if(tt->isEmpty()) {
      if(terms.isEmpty()) {
	//we're done, args stack contains modified arguments
	//of the literal.
	ASS(toDo.isEmpty());
	break;
      }
      Term* orig=terms.pop();
      if(!modified.pop()) {
	args.truncate(args.length() - orig->arity());
	args.push(TermList(orig));
	continue;
      }
      //here we assume, that stack is an array with
      //second topmost element as &top()-1, third at
      //&top()-2, etc...
      TermList* argLst=&args.top() - (orig->arity()-1);
      args.truncate(args.length() - orig->arity());

      args.push(TermList(Term::create(orig,argLst)));
      modified.setTop(true);
      continue;
    } else {
      toDo.push(tt->next());
    }

    TermList tl=*tt;
    if(tl==tSrc) {
      args.push(tDest);
      modified.setTop(true);
      continue;
    }
    if(tl.isVar()) {
      args.push(tl);
      continue;
    }
    ASS(tl.isTerm());
    Term* t=tl.term();
    terms.push(t);
    modified.push(false);
    toDo.push(t->args());
  }
  ASS(toDo.isEmpty());
  ASS(terms.isEmpty());
  ASS_EQ(modified.length(),1);
  ASS_EQ(args.length(),lit->arity());

  if(!modified.pop()) {
    //we call replace in superposition only if we already know,
    //there is something to be replaced.
    ASSERTION_VIOLATION;
    return lit;
  }

  //here we assume, that stack is an array with
  //second topmost element as &top()-1, third at
  //&top()-2, etc...
  TermList* argLst=&args.top() - (lit->arity()-1);
  return Literal::create(lit,argLst);
}

TermIterator EqHelper::getRewritableSubtermIterator(Literal* lit)
{
  CALL("EqHelper::getRewritableSubtermIterator");

//  if(lit->isEquality()) {
//    if(lit->isNegative()) {
//      return TermIterator::getEmpty();
//    }
  if(lit->isEquality() && lit->isPositive()) {
    TermList sel;
    switch(lit->getArgumentOrder())
    {
    case Term::INCOMPARABLE:
    {
      Term::NonVariableIterator nvi(lit);
      return getUniquePersistentIteratorFromPtr(&nvi);
    }
    case Term::EQUAL:
    case Term::GREATER:
      sel=*lit->nthArgument(0);
      break;
    case Term::LESS:
      sel=*lit->nthArgument(1);
#if VDEBUG
      break;
    default:
      ASSERTION_VIOLATION;
#endif
    }
    if(!sel.isTerm()) {
      return TermIterator::getEmpty();
    }
    return getUniquePersistentIterator(
	    getConcatenatedIterator(getSingletonIterator(sel),
	    vi( new Term::NonVariableIterator(sel.term()) )) );
  } else {
    Term::NonVariableIterator nvi(lit);
    return getUniquePersistentIteratorFromPtr(&nvi);
  }
}

TermIterator EqHelper::getLHSIterator(Literal* lit)
{
  CALL("EqHelper::getLHSIterator");

  if(lit->isEquality()) {
    if(lit->isNegative()) {
      return TermIterator::getEmpty();
    }
    TermList t0=*lit->nthArgument(0);
    TermList t1=*lit->nthArgument(1);
    switch(lit->getArgumentOrder())
    {
    case Term::INCOMPARABLE:
      return pvi( getConcatenatedIterator(getSingletonIterator(t0),
	      getSingletonIterator(t1)) );
    case Term::GREATER:
      return pvi( getSingletonIterator(t0) );
    case Term::LESS:
      return pvi( getSingletonIterator(t1) );
#if VDEBUG
    case Term::EQUAL:
      //there should be no equality literals of equal terms
    default:
      ASSERTION_VIOLATION;
#endif
    }
    return TermIterator::getEmpty();
  } else {
    return TermIterator::getEmpty();
  }
}

TermIterator EqHelper::getEqualityArgumentIterator(Literal* lit)
{
  CALL("EqHelper::getEqualityArgumentIterator");
  ASS(lit->isEquality());

  return pvi( getConcatenatedIterator(
	  getSingletonIterator(*lit->nthArgument(0)),
	  getSingletonIterator(*lit->nthArgument(1))) );
}


}
