"""
Elements with fixed modulus of general extensions of p-adic rings.

AUTHORS:

- Julian Rueth (2013-01-08): initial version

"""
#*****************************************************************************
#       Copyright (C) 2013 Julian Rueth <julian.rueth@fsfe.org>
#
#  Distributed under the terms of the GNU General Public License (GPL)
#  as published by the Free Software Foundation; either version 2 of
#  the License, or (at your option) any later version.
#                  http://www.gnu.org/licenses/
#*****************************************************************************

from sage.rings.padics.padic_general_element import pAdicGeneralElement

class pAdicGeneralFMElement(pAdicGeneralElement):
    """
    An element with fixed modulus of a general extension of a p-adic ring.

    EXAMPLES::

        sage: K = ZpFM(3,10)
        sage: R.<x> = K[]
        sage: M.<x> = pAdicExtension(K, x - 1)
        sage: x
        1 + O(3^10)
        sage: M.zero()
        O(3^10)

    """
    def __init__(self, parent, x, absprec=None):
        """
        Initializes ``self`` from ``x``.

        INPUT:

            - ``parent`` -- the parent of ``self``

            - ``x`` -- an element from which ``self`` can be initialized

            - ``absprec`` -- ignored parameter

        EXAMPLES::

            sage: K = ZpFM(3,10)
            sage: R.<x> = K[]
            sage: M.<x> = pAdicExtension(K, x - 1)
            sage: M(None)
            O(3^10)
            sage: M([R.one()])
            1 + O(3^10)

        """
        if x == parent.base_ring().zero():
            x = None
        pAdicGeneralElement.__init__(self, parent, x, parent.precision_cap())
