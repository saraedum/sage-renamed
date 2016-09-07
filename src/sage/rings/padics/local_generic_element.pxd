from sage.structure.element cimport PrincipalIdealDomainElement

cdef class LocalGenericElement(PrincipalIdealDomainElement):
    cpdef RingElement _div_(self, RingElement right)
    cpdef ModuleElement _sub_(self, ModuleElement right)
