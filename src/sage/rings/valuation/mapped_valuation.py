# -*- coding: utf-8 -*-
r"""
Valuations which are implemented through a map to another valuation.

EXAMPLES:

Extensions of valuations over finite field extensions `L=K[x]/(G)` are realized
through an infinite valuation on `K[x]` which maps `G` to infinity::
    
    sage: from mac_lane import * # optional: standalone
    sage: K.<x> = FunctionField(QQ)
    sage: R.<y> = K[]
    sage: L.<y> = K.extension(y^2 - x)

    sage: v = FunctionFieldValuation(K, 0)
    sage: w = v.extension(L); w
    (x)-adic valuation

    sage: w._base_valuation
    [ Gauss valuation induced by (x)-adic valuation, v(y) = 1/2 , … ]

AUTHORS:

- Julian Rüth (2016-11-10): initial version

"""
#*****************************************************************************
#       Copyright (C) 2016 Julian Rüth <julian.rueth@fsfe.org>
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

from valuation import DiscreteValuation, DiscretePseudoValuation
from sage.misc.abstract_method import abstract_method

class MappedValuation_base(DiscretePseudoValuation):
    r"""
    A valuation which is implemented through another proxy "base" valuation.

    EXAMPLES::

        sage: from mac_lane import * # optional: standalone
        sage: K.<x> = FunctionField(QQ)
        sage: R.<y> = K[]
        sage: L.<y> = K.extension(y^2 - x)

        sage: v = FunctionFieldValuation(K, 0)
        sage: w = v.extension(L); w
        (x)-adic valuation

    TESTS::

        sage: TestSuite(w).run() # long time

    """
    def __init__(self, parent, base_valuation):
        r"""
        TESTS::

            sage: from mac_lane import * # optional: standalone
            sage: K.<x> = FunctionField(QQ)
            sage: R.<y> = K[]
            sage: L.<y> = K.extension(y^2 - x^2 + 1)

            sage: v = FunctionFieldValuation(K, 0)
            sage: w = v.extension(L); w
            (x)-adic valuation
            sage: isinstance(w, MappedValuation_base)
            True

        """
        DiscretePseudoValuation.__init__(self, parent)

        self._base_valuation = base_valuation 

    @abstract_method
    def _repr_(self):
        r"""
        Return a printable representation of this valuation.

        Subclasses must override this method.

        EXAMPLES::

            sage: from mac_lane import * # optional: standalone
            sage: K = QQ
            sage: R.<t> = K[]
            sage: L.<t> = K.extension(t^2 + 1)
            sage: v = pAdicValuation(QQ, 2)
            sage: v.extension(L) # indirect doctest
            2-adic valuation

        """

    def residue_ring(self):
        r"""
        Return the residue field of this valuation.

        EXAMPLES::

            sage: from mac_lane import * # optional: standalone
            sage: K = QQ
            sage: R.<t> = K[]
            sage: L.<t> = K.extension(t^2 + 1)
            sage: v = pAdicValuation(QQ, 2)
            sage: v.extension(L).residue_ring()
            Finite Field of size 2

        """
        return self._base_valuation.residue_ring()

    def uniformizer(self):
        r"""
        Return a uniformizing element of this valuation.

        EXAMPLES::

            sage: from mac_lane import * # optional: standalone
            sage: K = QQ
            sage: R.<t> = K[]
            sage: L.<t> = K.extension(t^2 + 1)
            sage: v = pAdicValuation(QQ, 2)
            sage: v.extension(L).uniformizer()
            t + 1

        """
        return self._from_base_domain(self._base_valuation.uniformizer())

    def _to_base_domain(self, f):
        r"""
        Return ``f`` as an element in the domain of ``_base_valuation``.

        EXAMPLES::

            sage: from mac_lane import * # optional: standalone
            sage: K.<x> = FunctionField(QQ)
            sage: R.<y> = K[]
            sage: L.<y> = K.extension(y^2 - x)

            sage: v = FunctionFieldValuation(K, 0)
            sage: w = v.extensions(L)[0]
            sage: w._to_base_domain(y).parent()
            Univariate Polynomial Ring in y over Rational function field in x over Rational Field

        """
        return self._base_valuation.domain().coerce(f)

    def _from_base_domain(self, f):
        r"""
        Return ``f`` as an element in the domain of this valuation.

        EXAMPLES::

            sage: from mac_lane import * # optional: standalone
            sage: K.<x> = FunctionField(QQ)
            sage: R.<y> = K[]
            sage: L.<y> = K.extension(y^2 - x)

            sage: v = FunctionFieldValuation(K, 0)
            sage: w = v.extension(L)
            sage: w._from_base_domain(w._base_valuation.domain().gen()).parent()
            Function field in y defined by y^2 - x

        """
        return self.domain().coerce(f)

    def _call_(self, f):
        r"""
        Evaluate this valuation at ``f``.

        EXAMPLES::

            sage: from mac_lane import * # optional: standalone
            sage: K.<x> = FunctionField(QQ)
            sage: R.<y> = K[]
            sage: L.<y> = K.extension(y^2 - x)

            sage: v = FunctionFieldValuation(K, 0)
            sage: w = v.extension(L)
            sage: w(y) # indirect doctest
            1/2

        """
        return self._base_valuation(self._to_base_domain(f))

    def reduce(self, f):
        r"""
        Return the reduction of ``f`` in the :meth:`residue_field` of this valuation.

        EXAMPLES::

            sage: from mac_lane import * # optional: standalone
            sage: K.<x> = FunctionField(QQ)
            sage: R.<y> = K[]
            sage: L.<y> = K.extension(y^2 - (x - 2))

            sage: v = FunctionFieldValuation(K, 0)
            sage: w = v.extension(L)
            sage: w.reduce(y)
            u1

        """
        return self._base_valuation.reduce(self._to_base_domain(f))

    def lift(self, F):
        r"""
        Lift ``F`` from the :meth;`residue_field` of this valuation into its
        domain.

        EXAMPLES::

            sage: from mac_lane import * # optional: standalone
            sage: K.<x> = FunctionField(QQ)
            sage: R.<y> = K[]
            sage: L.<y> = K.extension(y^2 - x)

            sage: v = FunctionFieldValuation(K, 2)
            sage: w = v.extension(L)
            sage: w.lift(w.residue_field().gen())
            y

        """
        F = self.residue_ring().coerce(F)
        F = self._to_base_residue_ring(F)
        f = self._base_valuation.lift(F)
        return self._from_base_domain(f)

    def _to_base_residue_ring(self, F):
        r"""
        Return ``F``, an element of :meth:`residue_ring`, as an element of the
        residue ring of the ``_base_valuation``.

        EXAMPLES::

            sage: from mac_lane import * # optional: standalone
            sage: K.<x> = FunctionField(QQ)
            sage: R.<y> = K[]
            sage: L.<y> = K.extension(y^2 - x)

            sage: v = FunctionFieldValuation(K, 0)
            sage: w = v.extensions(L)[0]
            sage: w._to_base_residue_ring(1)
            1

        """
        return self._base_valuation.residue_ring().coerce(F)

    def _from_base_residue_ring(self, F):
        r"""
        Return ``F``, an element of the residue ring of ``_base_valuation``, as
        an element of this valuation's :meth:`residue_ring`.

        EXAMPLES::

            sage: from mac_lane import * # optional: standalone
            sage: K.<x> = FunctionField(QQ)
            sage: R.<y> = K[]
            sage: L.<y> = K.extension(y^2 - x)

            sage: v = FunctionFieldValuation(K, 0)
            sage: w = v.extensions(L)[0]
            sage: w._from_base_residue_ring(1)
            1

        """
        return self.residue_ring().coerce(F)

    def _test_to_from_base_domain(self, **options):
        r"""
        Check the correctness of :meth:`to_base_domain` and
        :meth:`from_base_domain`.

        EXAMPLES::

            sage: from mac_lane import * # optional: standalone
            sage: K.<x> = FunctionField(QQ)
            sage: R.<y> = K[]
            sage: L.<y> = K.extension(y^2 - x)

            sage: v = FunctionFieldValuation(K, 0)
            sage: w = v.extensions(L)[0]
            sage: w._test_to_from_base_domain()

        """
        tester = self._tester(**options)

        for x in tester.some_elements(self.domain().some_elements()):
            tester.assertEqual(x, self._from_base_domain(self._to_base_domain(x)))
            # note that the converse might not be true


class FiniteExtensionFromInfiniteValuation(MappedValuation_base, DiscreteValuation):
    r"""
    A valuation on a quotient of the form `L=K[x]/(G)` with an irreducible `G`
    which is internally backed by a pseudo-valuations on `K[x]` which sends `G`
    to infinity.

    INPUT:

    - ``parent`` -- the containing valuation space (usually the space of
      discrete valuations on `L`)

    - ``base_valuation`` -- an infinite valuation on `K[x]` which takes `G` to
      infinity.

    EXAMPLES::

        sage: from mac_lane import * # optional: standalone
        sage: K.<x> = FunctionField(QQ)
        sage: R.<y> = K[]
        sage: L.<y> = K.extension(y^2 - x)

        sage: v = FunctionFieldValuation(K, 0)
        sage: w = v.extension(L); w
        (x)-adic valuation

    """
    def __init__(self, parent, base_valuation):
        r"""
        TESTS::
    
            sage: from mac_lane import * # optional: standalone
            sage: K.<x> = FunctionField(QQ)
            sage: R.<y> = K[]
            sage: L.<y> = K.extension(y^2 - x)
    
            sage: v = FunctionFieldValuation(K, 0)
            sage: w = v.extension(L)
            sage: isinstance(w, FiniteExtensionFromInfiniteValuation)
            True
            sage: TestSuite(w).run() # long time
    
        """
        MappedValuation_base.__init__(self, parent, base_valuation)
        DiscreteValuation.__init__(self, parent)

    def _eq_(self, other):
        r"""
        Return whether this valuation is indistinguishable from ``other``.

        EXAMPLES::

            sage: from mac_lane import * # optional: standalone
            sage: K = QQ
            sage: R.<t> = K[]
            sage: L.<t> = K.extension(t^2 + 1)
            sage: v = pAdicValuation(QQ, 2)
            sage: w = v.extension(L)
            sage: ww = v.extension(L)
            sage: w == ww # indirect doctest
            True

        """
        return isinstance(other, FiniteExtensionFromInfiniteValuation) and self._base_valuation == other._base_valuation

    def restriction(self, ring):
        r"""
        Return the restriction of this valuation to ``ring``.

        EXAMPLES::

            sage: from mac_lane import * # optional: standalone
            sage: K = QQ
            sage: R.<t> = K[]
            sage: L.<t> = K.extension(t^2 + 1)
            sage: v = pAdicValuation(QQ, 2)
            sage: w = v.extension(L)
            sage: w.restriction(K) is v
            True

        """
        if ring.is_subring(self._base_valuation.domain().base()):
            return self._base_valuation.restriction(ring)
        return super(FiniteExtensionFromInfiniteValuation, self).restriction(ring)

    def _weakly_separating_element(self, other):
        r"""
        Return an element in the domain of this valuation which has
        positive valuation with respect to this valuation and higher
        valuation with respect to this valuation than with respect to
        ``other``.

        EXAMPLES::

            sage: from mac_lane import * # optional: standalone
            sage: K = QQ
            sage: R.<t> = K[]
            sage: L.<t> = K.extension(t^2 + 1)
            sage: v = pAdicValuation(QQ, 2)
            sage: w = v.extension(L)
            sage: v = pAdicValuation(QQ, 5)
            sage: u,uu = v.extensions(L)
            sage: u.separating_element([w,uu]) # indirect doctest
            1/20*t + 7/20

        """
        if isinstance(other, FiniteExtensionFromInfiniteValuation):
            return self.domain()(self._base_valuation._weakly_separating_element(other._base_valuation))
        super(FiniteExtensionFromInfiniteValuation, self)._weakly_separating_element(other)


class FiniteExtensionFromLimitValuation(FiniteExtensionFromInfiniteValuation):
    r"""
    An extension of a valuation on a finite field extensions `L=K[x]/(G)` which
    is induced by an infinite limit valuation on `K[x]`.

    EXAMPLES::

        sage: from mac_lane import * # optional: standalone
        sage: K.<x> = FunctionField(QQ)
        sage: R.<y> = K[]
        sage: L.<y> = K.extension(y^2 - x)
        sage: v = FunctionFieldValuation(K, 1)
        sage: w = v.extensions(L); w
        [[ (x - 1)-adic valuation, v(y - 1) = 1 ]-adic valuation,
         [ (x - 1)-adic valuation, v(y + 1) = 1 ]-adic valuation]

    TESTS::

        sage: TestSuite(w[0]).run() # long time
        sage: TestSuite(w[1]).run() # long time

    """
    def __init__(self, parent, approximant, G, approximants):
        r"""
        EXAMPLES:

        Note that this implementation is also used when the underlying limit is
        only taken over a finite sequence of valuations::

            sage: from mac_lane import * # optional: standalone
            sage: K.<x> = FunctionField(QQ)
            sage: R.<y> = K[]
            sage: L.<y> = K.extension(y^2 - x)
            sage: v = FunctionFieldValuation(K, 2)
            sage: w = v.extension(L); w
            (x - 2)-adic valuation
            sage: isinstance(w, FiniteExtensionFromLimitValuation)
            True

        """
        # keep track of all extensions to this field extension so we can print
        # this valuation nicely, dropping any unnecessary information
        self._approximants = approximants

        from valuation_space import DiscretePseudoValuationSpace
        from limit_valuation import LimitValuation
        limit = LimitValuation(approximant, G)
        FiniteExtensionFromInfiniteValuation.__init__(self, parent, limit)

    def _repr_(self):
        """
        Return a printable representation of this valuation.

        EXAMPLES::

            sage: from mac_lane import * # optional: standalone
            sage: pAdicValuation(GaussianIntegers().fraction_field(), 2) # indirect doctest
            2-adic valuation

        """
        from limit_valuation import MacLaneLimitValuation
        if isinstance(self._base_valuation, MacLaneLimitValuation):
            # print the minimal information that singles out this valuation from all approximants
            assert(self._base_valuation._initial_approximation in self._approximants)
            approximants = [v.augmentation_chain()[::-1] for v in self._approximants]
            augmentations = self._base_valuation._initial_approximation.augmentation_chain()[::-1]
            unique_approximant = None
            for l in range(len(augmentations)):
                if len([a for a in approximants if a[:l+1] == augmentations[:l+1]]) == 1:
                    unique_approximant = augmentations[:l+1]
                    break
            assert(unique_approximant is not None)
            if unique_approximant[0].is_gauss_valuation():
                unique_approximant[0] = unique_approximant[0].restriction(unique_approximant[0].domain().base_ring())
            if len(unique_approximant) == 1:
                return repr(unique_approximant[0])
            from augmented_valuation import AugmentedValuation_base
            return "[ %s ]-adic valuation"%(", ".join("v(%r) = %r"%(v._phi, v._mu) if (isinstance(v, AugmentedValuation_base) and v.domain() == self._base_valuation.domain()) else repr(v) for v in unique_approximant))
        return "%s-adic valuation"%(self._base_valuation)

