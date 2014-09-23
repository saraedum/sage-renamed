"""
Elements with capped absolute precision of two step extensions of
`\mathbb{Q}_p` and `\mathbb{Z}_p` realized as power series over the unramified
first step.

AUTHORS:

- Julian Rueth (2012-10-22): initial version

"""
#*****************************************************************************
#       Copyright (C) 2012 Julian Rueth <julian.rueth@fsfe.org>
#
#  Distributed under the terms of the GNU General Public License (GPL)
#  as published by the Free Software Foundation; either version 2 of
#  the License, or (at your option) any later version.
#                  http://www.gnu.org/licenses/
#*****************************************************************************

from sage.rings.padics.padic_laurent_element import pAdicLaurentElement
from sage.structure.element import is_Element

cdef class pAdicLaurentCAElement(pAdicLaurentElement):
    """
    An element with capped absolute precision of a two step extension of
    `\mathbb{Q}_p` and `\mathbb{Z}_p` realized as a power series over the
    unramified first step.

    EXAMPLES::

        sage: K = ZpCA(3,10)
        sage: R.<u> = K[]
        sage: L.<u> = K.extension(u^2 + 3*u + 4)
        sage: R.<a> = L[]
        sage: M = ZpTwoStepExtensionFactory(L, a^3 - 9*u*a^2 + 3*u, ram_name='a'); a = M.uniformizer(); u = M(u)
        sage: a
        a + O(a^30)
        sage: u
        u + O(a^30)
        sage: M.zero()
        O(a^30)

    Elements can be initialized from lists of elements of the residue field::

        sage: k = M.residue_field()
        sage: M([k.zero(),k.one(),k.gen(),k.one()])
        a + u*a^2 + a^3 + O(a^4)

    """
    def __init__(self, parent, x, absprec=None):
        """
        Initializes ``self`` from ``x``.

        INPUT:

            - ``parent`` -- the parent of ``self``

            - ``x`` -- an element from which ``self`` can be initialized

            - ``absprec`` -- integer or ``None`` (default: None), reduce the
              precision of ``self`` to that value if not ``None``

        EXAMPLES::

            sage: K = ZpCA(3,10)
            sage: R.<u> = K[]
            sage: L.<u> = K.extension(u^2 + 3*u + 4)
            sage: R.<a> = L[]
            sage: M = ZpTwoStepExtensionFactory(L, a^3 - 9*u*a^2 + 3*u, ram_name='a'); a = M.uniformizer(); u = M(u)
            sage: M(None)
            O(a^30)
            sage: M(None,300)
            O(a^30)
            sage: M(None,20)
            O(a^20)

        """
        if is_Element(x) and x.parent() is parent.base_ring() and x.valuation() == parent.base_ring().precision_cap():
            x = None
        pAdicLaurentElement.__init__(self, parent, x, parent.precision_cap() if absprec is None else min(parent.precision_cap(),absprec))
