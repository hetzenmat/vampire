/**
 * @file Global.cpp
 * Defines all global (static) members that must be initialised
 * in a fixed order. Created due to the usual C++ problems with the
 * order of initialisation of static members.
 *
 * @since 11/12/2003 Manchester
 */

#if VDEBUG
#  include "Debug/Assertion.hpp"
#endif

#include "Lib/Enumerator.hpp"

#include "Kernel/Formula.hpp"
#include "Kernel/Unit.hpp"

#include "Shell/UIHelper.hpp"

#include "Lib/Array.hpp"
#include "Lib/Environment.hpp"
#include "Lib/List.hpp"
#include "Lib/System.hpp"

// the elements below are simple and can be initisalised before
// any objects
Lib::Enumerator Lib::Enumerator::unitEnumerator;
unsigned Kernel::Unit::_lastNumber = 0;
bool Shell::UIHelper::cascMode=false;
bool Shell::UIHelper::cascModeChild=false;
bool Shell::UIHelper::satisfiableStatusWasAlreadyOutput=false;

/**
 * String names of connectives. Used in the function toXML().
 */
string Kernel::Formula::_connectiveNames[] =
  {"atomic", "and", "or", "imp", "iff", "xor", "not", "forall", "exists"};


// From here the order does matter

Lib::ZIArray<Lib::List<VoidFunc>*> Lib::System::s_terminationHandlers(2);

Lib::Environment* Lib::env = 0;

struct __Lib_System_Init_Invoker
{
  __Lib_System_Init_Invoker()
  {
    Lib::System::onInitialization();
  }
};

__Lib_System_Init_Invoker __Lib_System_Init_Invoker_obj;

