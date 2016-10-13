r"""
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

# Fix doctests so they work in standalone mode (when invoked with sage -t, they run within the mac_lane/ directory)
import sys, os
if hasattr(sys.modules['__main__'], 'DC') and 'standalone' in sys.modules['__main__'].DC.options.optional:
    sys.path.append(os.getcwd())
    sys.path.append(os.path.dirname(os.getcwd()))

from sage.categories.homset import Hom
from sage.categories.morphism import Morphism
from sage.categories.sets_cat import Sets
from sage.categories.integral_domains import IntegralDomains
from sage.sets.set import Set
from sage.rings.all import ZZ, QQ
from sage.rings.polynomial.all import PolynomialRing
from sage.rings.infinity import infinity
from sage.categories.homsets import HomsetsOf
from sage.misc.classcall_metaclass import ClasscallMetaclass
from sage.misc.inherit_comparison import InheritComparisonMetaclass

discrete_valuation_codomain = Set(QQ).union(Set([infinity]))

class DiscretePseudoValuation(Morphism):
    r"""
    Abstract base class for discrete pseudo-valuations, i.e., discrete
    valuations which might send more that just zero to infinity.

    INPUT:

    - ``domain`` -- an integral domain

    - ``check`` -- a boolean (default: ``True``), if ``True``, we check that
      ``domain`` is an integral domain.

    EXAMPLES::

        sage: from mac_lane import * # optional: standalone
        sage: v = pAdicValuation(ZZ, 2); v # indirect doctest
        2-adic valuation

    TESTS:

    For a reason that is not clear to me, inheriting from `Morphism` does not
    correctly inherit from the element class of `HomsetsOf(Sets())`, so we need
    to skip the category doctests::

        sage: TestSuite(v).run(skip="_test_category")

    """
    def __init__(self, domain, check = True):
        r"""
        TESTS::

            sage: from sage.rings.padics.discrete_valuation import DiscretePseudoValuation # optional: integrated
            sage: isinstance(DiscretePseudoValuation(ZZ), DiscretePseudoValuation)
            True

        """
        if check:
            if domain not in IntegralDomains():
                raise ValueError("domain of a discrete valuation must be an integral domain")
        Morphism.__init__(self, Hom(domain, discrete_valuation_codomain, Sets()))

    def _test_add(self, **options):
        r"""
        Check that the (strict) triangle equality is satisfied for this
        valuation.

        TESTS::

            sage: from mac_lane import * # optional: standalone
            sage: v = pAdicValuation(ZZ, 3)
            sage: v._test_add()

        """
        tester = self._tester(**options)
        S = tester.some_elements(self.domain().some_elements())
        from sage.categories.cartesian_product import cartesian_product
        for x,y in tester.some_elements(cartesian_product([S,S])):
            tester.assertGreaterEqual(self(x+y),min(self(x),self(y)))
            if self(x) != self(y):
                tester.assertEqual(self(x+y),min(self(x),self(y)))

    def _test_mul(self, **options):
        r"""
        Check that multiplication translates to addition of valuations.

        TESTS::

            sage: from mac_lane import * # optional: standalone
            sage: v = pAdicValuation(QQ, 5)
            sage: v._test_mul()

        """
        tester = self._tester(**options)
        for x in tester.some_elements(self.domain().some_elements()):
            if x.is_zero():
                tester.assertEqual(self(x), infinity)
            if self(x) is infinity:
                tester.assertFalse(x.is_unit())

        S = list(self.domain().some_elements())
        from sage.categories.cartesian_product import cartesian_product
        for x,y in tester.some_elements(cartesian_product([S,S])):
            tester.assertEqual(self(x*y),self(x)+self(y))

    def is_equivalent(self, f, g):
        r"""
        Return whether ``f`` and ``g`` are equivalent.

        EXAMPLES::

            sage: from mac_lane import * # optional: standalone
            sage: v = pAdicValuation(QQ, 2)
            sage: v.is_equivalent(2, 1)
            False
            sage: v.is_equivalent(2, -2)
            True
            sage: v.is_equivalent(2, 0)
            False
            sage: v.is_equivalent(0, 0)
            True

        """
        vf = self(f)
        vg = self(g)
        if self(f) == infinity and self(g) == infinity:
            return True
        if self(f) == infinity or self(g) == infinity:
            return False
        return self(f-g) > vf

    def __hash__(self):
        r"""
        The hash value of this valuation.

        We override the strange default provided by
        ``sage.categories.marphism.Morphism`` here and implement equality by
        ``id``. This works fine for objects which use unique representation
        which is the case for most valuations.

        EXAMPLES::

            sage: from mac_lane import *
            sage: v = pAdicValuation(QQ, 2)
            sage: hash(v) == hash(v)
            True

        """
        return id(self)

    def _cmp_(self, other):
        r"""
        Compare this element to ``other``.

        A concrete valuation can override this if there is a total ordering
        on some valuations. Beware that you need to check the type of
        ``other`` which might not be a valuation at all but just a map from the
        domain to `\QQ \cup\{\infty\}`.

        EXAMPLES::

            sage: from mac_lane import *
            sage: v = pAdicValuation(QQ, 2)
            sage: v < v
            Traceback (most recent call last):
            ...
            NotImplementedError: Operator not implemented for this valuation.

        """
        raise NotImplementedError("No total ordering for this valuation.");

    def _richcmp_(self, other, op):
        r"""
        Compare this element to ``other``.

        We override the strange default provided by
        ``sage.categories.marphism.Morphism`` here and implement equality by
        ``id``. This works fine for objects which use unique representation
        which is the case for most valuations.

        A concrete valuation could override this for the equality operators.
        Beware that you need to check the type of ``other`` which might not be
        a valuation at all but just a map from the domain to `\QQ
        \cup\{\infty\}`.

        EXAMPLES::

            sage: from mac_lane import *
            sage: v = pAdicValuation(QQ, 2)
            sage: v == v
            True
            sage: v != v
            False
            sage: w = pAdicValuation(QQ, 3)
            sage: v == w
            False
            sage: v != w
            True

        """
        if op == 2: # ==
            return self is other
        if op == 3: # !=
            return not (self is other)
        raise NotImplementedError("Operator not implemented for this valuation.")

    # Remove the default implementation of Map.__reduce__ that does not play
    # nice with factories (a factory, does not override Map.__reduce__ because
    # it is not the generic reduce of object.)
    __reduce__ = object.__reduce__

class DiscreteValuation(DiscretePseudoValuation):
    r"""
    Abstract base class for discrete valuations.

    INPUT:

    - ``domain`` -- an integral domain

    - ``check`` -- a boolean (default: ``True``), if ``True``, we check that
      ``domain`` is an integral domain.

    EXAMPLES::

        sage: from mac_lane import * # optional: standalone
        sage: v = pAdicValuation(Zp(2), 2); v # indirect doctest
        2-adic valuation

    TESTS:

    For a reason that is not clear to me, inheriting from `Morphism` does not
    correctly inherit from the element class of `HomsetsOf(Sets())`, so we need
    to skip the category doctests::

        sage: TestSuite(v).run(skip="_test_category")

    """
    def __init__(self, domain, check=True):
        r"""
        TESTS::

            sage: from mac_lane import * # optional: standalone
            sage: from sage.rings.padics.discrete_valuation import DiscreteValuation
            sage: isinstance(DiscreteValuation(ZZ), DiscreteValuation)
            True

        """
        DiscretePseudoValuation.__init__(self, domain, check=check)

    def _test_not_pseudo(self, **options):
        r"""
        Test that only zero is sent to infinity.

        TESTS::

            sage: from mac_lane import * # optional: standalone
            sage: v = pAdicValuation(Zp(2), 2)
            sage: v._test_not_pseudo()

        """
        tester = self._tester(**options)
        for x in tester.some_elements(self.domain().some_elements()):
            tester.assertEqual(self(x)==infinity,x.is_zero())
