include "../../ext/cdefs.pxi"

from sage.structure.element cimport RingElement, ModuleElement
from sage.rings.padics.padic_ext_element cimport pAdicExtElement

cdef class pAdicLaurentElement(pAdicExtElement):
    cdef __series_start
    cdef __series_raw
    cdef __series_developed
    cdef __series_relative
    cdef __series_valuation
    cdef __series_compressed
