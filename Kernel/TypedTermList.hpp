/*
 * This file is part of the source code of the software program
 * Vampire. It is protected by applicable
 * copyright laws.
 *
 * This source code is distributed under the licence found here
 * https://vprover.github.io/license.html
 * and in the source directory
 */

#ifndef __Kernel_TypedTermList__
#define __Kernel_TypedTermList__

#include "Kernel/SortHelper.hpp"

namespace Kernel {
using SortId = Kernel::TermList;

class TypedTermList : public TermList
{
  SortId _sort;
public:

    // TODO get rid of default constructor
  TypedTermList() {}
  TypedTermList(TermList t, SortId sort) : TermList(t), _sort(sort) 
  { 
    ASS_NEQ(sort, AtomicSort::superSort());
    ASS(!sort.isEmpty())
  }
  TypedTermList(Term* t) : TypedTermList(TermList(t), SortHelper::getResultSort(t)) {}
  SortId sort() const { return _sort; }

  friend std::ostream& operator<<(std::ostream& out, TypedTermList const& self) 
  { return out << (TermList const&) self << ": " << self._sort; }

  std::string toString() const {
    std::stringstream buffer;
    buffer << (static_cast<TermList>(*this)).toString() << ": " << _sort.toString();
    return buffer.str();
  }
};

} // namespace Kernel 


#endif // __Kernel_TypedTermList__
