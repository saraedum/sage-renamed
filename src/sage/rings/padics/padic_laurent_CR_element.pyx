r"""
Elements with capped relative precision of two step extensions of
`\mathbb{Q}_p` and `\mathbb{Z}_p` realized as Laurent series or power series
over the unramified first step.

AUTHORS:

- Julian Rueth (2012-10-23): initial version

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

cdef class pAdicLaurentCRElement(pAdicLaurentElement):
    r"""
    An element with capped relative precision of a two step extension of
    `\mathbb{Q}_p` and `\mathbb{Z}_p` realized as Laurent series or power
    series over the unramified first step.

    EXAMPLES::

        sage: K = Qp(3,10)
        sage: R.<u> = K[]
        sage: L.<u> = K.extension(u^2 + 3*u + 4)
        sage: R.<a> = L[]
        sage: M = QpTwoStepExtensionFactory(L, a^3 - 9*u*a^2 + 3*u, ram_name='a'); a = M.uniformizer(); u = M(u)
        sage: a
        a + O(a^31)
        sage: u
        u + O(a^30)
        sage: M.zero()
        0

    Elements can be initialized from lists of elements of the residue field::

        sage: k = M.residue_field()
        sage: M([k.zero(),k.one(),k.gen(),k.one()])
        a + u*a^2 + a^3 + O(a^4)

    """
    pass
