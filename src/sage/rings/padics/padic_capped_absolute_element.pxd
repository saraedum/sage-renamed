include "sage/ext/cdefs.pxi"

ctypedef mpz_t celement
from sage.libs.pari.gen cimport gen as pari_gen
from sage.rings.padics.padic_capped_relative_element cimport CRElement

include "CA_template_header.pxi"

cdef class pAdicCappedAbsoluteElement(CAElement):
    cdef lift_c(self)
    cdef pari_gen _to_gen(self)
