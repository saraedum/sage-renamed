"""
Discrete valuations

This file defines abstract base classes for discrete (pseudo-)valuations.

AUTHORS:

- Julian Rueth (2013-03-16): initial version

"""
#*****************************************************************************
#       Copyright (C) 2013 Julian Rueth <julian.rueth@fsfe.org>
#
#  Distributed under the terms of the GNU General Public License (GPL)
#  as published by the Free Software Foundation; either version 2 of
#  the License, or (at your option) any later version.
#                  http://www.gnu.org/licenses/
#*****************************************************************************
from sage.categories.homset import Hom
from sage.categories.morphism import Morphism
from sage.categories.sets_cat import Sets
from sage.categories.integral_domains import IntegralDomains
from sage.sets.set import Set
from sage.rings.all import ZZ, QQ
from sage.rings.polynomial.all import PolynomialRing
from sage.rings.infinity import infinity

discrete_valuation_codomain = Set(ZZ).union(Set([infinity]))

class DiscretePseudoValuation(Morphism):
    """
    Abstract base class for discrete pseudo-valuations, i.e., discrete
    valuations which might send more that just zero to infinity.

    .. NOTE::

        Discrete valuations are normalized such that they're codomain is `\ZZ
        \cup \{\infty\}`.

    INPUT:

    - ``domain`` -- a integral domain

    - ``check`` -- a boolean (default: ``True``), if ``True``, we check that
      ``domain`` is a integral domain.

    EXAMPLES::

        sage: pAdicValuation(ZZ, 2) # indirect doctest
        2-adic valuation

    """
    def __init__(self, domain, check = True):
        """
        Initialization.

        TESTS::

            sage: from sage.rings.padics.discrete_valuation import DiscretePseudoValuation
            sage: type(DiscretePseudoValuation(ZZ))
            <class 'sage.rings.padics.discrete_valuation.DiscretePseudoValuation'>

        """
        if check:
            if not domain in IntegralDomains():
                raise ValueError("domain of a discrete valuation must be a integral domain")
        Morphism.__init__(self, Hom(domain, discrete_valuation_codomain, Sets()))

    def _test_add(self, **options):
        tester = self._tester(**options)
        S = tester.some_elements(self.domain().some_elements())
        from sage.combinat.cartesian_product import CartesianProduct
        for x,y in tester.some_elements(CartesianProduct(S,S)):
            tester.assertGreaterEqual(self(x+y),min(self(x),self(y)))
            if self(x) != self(y):
                tester.assertEqual(self(x+y),min(self(x),self(y)))

    def _test_mul(self, **options):
        tester = self._tester(**options)
        for x in tester.some_elements(self.domain().some_elements()):
            if x.is_zero():
                tester.assertEqual(self(x), infinity)
            if self(x) is infinity:
                tester.assertFalse(x.is_unit())

        S = self.domain().some_elements()
        from sage.combinat.cartesian_product import CartesianProduct
        for x,y in tester.some_elements(CartesianProduct(S,S)):
            tester.assertEqual(self(x*y),self(x)+self(y))

    def __hash__(self):
        # TODO: Hash for sets seems to be broken
        return hash(self.domain())

    def is_equivalent(self, f, g):
        return self(f-g)>0

    def _value_group(self, r):
        R = PolynomialRing(QQ,'x') # hack - QQ does not support fractional ideals
        K = QQ.extension(R.gen(),'x')
        return K.ideal(r)

class DiscreteValuation(DiscretePseudoValuation):
    """
    Abstract base class for discrete valuations.

    .. NOTE::

        Discrete valuations are normalized such that they're codomain is `\ZZ
        \cup \{\infty\}`.

    INPUT:

    - ``domain`` -- a integral domain

    - ``check`` -- a boolean (default: ``True``), if ``True``, we check that
      ``domain`` is a integral domain.

    EXAMPLES::

        sage: pAdicValuation(Zp(2), 2) # indirect doctest
        2-adic valuation

    """
    def __init__(self, domain, check=True):
        """
        Initialization.

        TESTS::

            sage: from sage.rings.padics.discrete_valuation import DiscreteValuation
            sage: type(DiscreteValuation(ZZ))
            <class 'sage.rings.padics.discrete_valuation.DiscreteValuation'>

        """
        DiscretePseudoValuation.__init__(self, domain, check)
