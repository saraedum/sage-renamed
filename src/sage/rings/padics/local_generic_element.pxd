import sage.structure.element
cimport sage.structure.element
from sage.structure.element cimport RingElement, ModuleElement, PrincipalIdealDomainElement

cdef class LocalGenericElement(PrincipalIdealDomainElement):
    cpdef RingElement _div_(self, RingElement right)
    cpdef ModuleElement _sub_(self, ModuleElement right)
