"""
Elements with capped relative precision of general extensions of p-adic rings.

AUTHORS:

- Julian Rueth (2013-01-09): initial version

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

class pAdicGeneralCRElement(pAdicGeneralElement):
    """
    An element with capped relative modulus of a general extension of a p-adic ring.

    EXAMPLES::

        sage: K = ZpFM(3,10)
        sage: R.<x> = K[]
        sage: M.<x> = pAdicExtension(K, x - 1)
        sage: x
        1 + O(3^10)
        sage: M.zero()
        O(3^10)

    """
    pass
