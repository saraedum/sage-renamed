# -*- coding: utf-8 -*-
r"""
Value groups of discrete valuations

This file defines additive subgroups of \QQ generated by a rational number and
related structures.

EXAMPLES::

    sage: from mac_lane import * # optional: standalone
    sage: pAdicValuation(QQ, 2).value_group()
    Additive Abelian Group generated by 1

AUTHORS:

- Julian Rüth (2013-09-06): initial version

"""
#*****************************************************************************
#       Copyright (C) 2013-2016 Julian Rüth <julian.rueth@fsfe.org>
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

from sage.structure.parent import Parent
from sage.structure.unique_representation import UniqueRepresentation
from sage.rings.all import QQ, ZZ, infinity

class DiscreteValuationCodomain(UniqueRepresentation, Parent):
    r"""
    The codomain of discrete valuations, the rational numbers extended by
    `\infty`.

    EXAMPLES::

        sage: from mac_lane import * # optional: standalone
        sage: C = DiscreteValuationCodomain(); C
        Codomain of Discrete Valuations

    TESTS::

        sage: TestSuite(C).run()
        
    """
    def __init__(self):
        r"""
        TESTS::

            sage: from mac_lane import * # optional: standalone
            sage: isinstance(pAdicValuation(QQ, 2).codomain(), DiscreteValuationCodomain)
            True

        """
        from sage.sets.finite_enumerated_set import FiniteEnumeratedSet
        from sage.categories.additive_monoids import AdditiveMonoids
        UniqueRepresentation.__init__(self)
        Parent.__init__(self, facade=(QQ, FiniteEnumeratedSet([infinity])), category=AdditiveMonoids())

    def _element_constructor_(self, x):
        r"""
        Create an element from ``x``.

        INPUT:

        - ``x`` -- a rational number or `\infty`

        TESTS::

            sage: from mac_lane import * # optional: standalone
            sage: DiscreteValuationCodomain()(0)
            0
            sage: DiscreteValuationCodomain()(infinity)
            +Infinity
            sage: DiscreteValuationCodomain()(-infinity)
            Traceback (most recent call last):
            ...
            ValueError: must be a rational number or infinity

        """
        if x is infinity:
            return x
        if x not in QQ:
            raise ValueError("must be a rational number or infinity")
        from sage.misc.functional import coerce
        return coerce(QQ, x)

    def _repr_(self):
        r"""
        Return a printable representation.

        EXAMPLES::

            sage: from mac_lane import * # optional: standalone
            sage: DiscreteValuationCodomain() # indirect doctest
            Codomain of Discrete Valuations

        """
        return "Codomain of Discrete Valuations"

class DiscreteValueGroup(UniqueRepresentation, Parent):
    r"""
    The value group of a discrete valuation, an additive subgroup of \QQ
    generated by ``generator``.

    INPUT:

    - ``generator`` -- a rational number

    .. NOTE::

        We do not rely on the functionality provided by additive abelian groups
        in Sage since these require the underlying set to be the integers.
        Therefore, we roll our own \Z-module here.
        We could have used :class:`AdditiveAbelianGroupWrapper` here, but it
        seems to be somewhat outdated. In particular, generic group
        functionality should now come from the category and not from the
        super-class. A facade of \Q appeared to be the better approach.

    EXAMPLES::

        sage: from mac_lane import * # optional: standalone
        sage: D1 = DiscreteValueGroup(0); D1
        Trivial Additive Abelian Group
        sage: D2 = DiscreteValueGroup(4/3); D2
        Additive Abelian Group generated by 4/3
        sage: D3 = DiscreteValueGroup(-1/3); D3
        Additive Abelian Group generated by 1/3

    TESTS::

        sage: TestSuite(D1).run()
        sage: TestSuite(D2).run()
        sage: TestSuite(D3).run()

    """
    @staticmethod
    def __classcall__(cls, generator):
        r"""
        Normalizes ``generator`` to a positive rational so that this is a
        unique parent.

        TESTS::

            sage: from mac_lane import * # optional: standalone
            sage: DiscreteValueGroup(1) is DiscreteValueGroup(-1)
            True

        """
        from sage.misc.functional import coerce
        generator = coerce(QQ, generator)
        generator = generator.abs()
        return super(DiscreteValueGroup, cls).__classcall__(cls, generator)

    def __init__(self, generator):
        r"""
        TESTS::

            sage: from mac_lane import * # optional: standalone
            sage: isinstance(DiscreteValueGroup(0), DiscreteValueGroup)
            True

        """
        from sage.categories.modules import Modules
        from sage.categories.additive_monoids import AdditiveMonoids
        self._generator = generator

        # We can not set the facade to DiscreteValuationCodomain since there
        # are some issues with iterated facades currently
        UniqueRepresentation.__init__(self)
        Parent.__init__(self, facade=QQ, category=Modules(ZZ))

    def _element_constructor_(self, x):
        r"""
        Create an element in this group from ``x``.

        INPUT:

        - ``x`` -- a rational number

        TESTS::

            sage: from mac_lane import * # optional: standalone
            sage: DiscreteValueGroup(0)(0)
            0
            sage: DiscreteValueGroup(0)(1)
            Traceback (most recent call last):
            ...
            ValueError: `1` is not in Trivial Additive Abelian Group.
            sage: DiscreteValueGroup(1)(1)
            1
            sage: DiscreteValueGroup(1)(1/2)
            Traceback (most recent call last):
            ...
            ValueError: `1/2` is not in Additive Abelian Group generated by 1.

        """
        from sage.misc.functional import coerce
        x = coerce(QQ, x)
        if x == 0 or (self._generator != 0 and x/self._generator in ZZ):
            return x 

        raise ValueError("`{0}` is not in {1}.".format(x,self))

    def _repr_(self):
        r"""
        Return a printable representation for this group.

        EXAMPLES::

            sage: from mac_lane import * # optional: standalone
            sage: DiscreteValueGroup(0) # indirect doctest
            Trivial Additive Abelian Group

        """
        if self.is_trivial():
            return "Trivial Additive Abelian Group"
        return "Additive Abelian Group generated by %r"%(self._generator,)

    def __add__(self, other):
        r"""
        Return the subgroup of \QQ generated by this group and ``other``.

        INPUT:

        - ``other`` -- a discrete value group or a rational number

        EXAMPLES::

            sage: from mac_lane import * # optional: standalone
            sage: D = DiscreteValueGroup(1/2)
            sage: D + 1/3
            Additive Abelian Group generated by 1/6
            sage: D + D
            Additive Abelian Group generated by 1/2
            sage: D + 1
            Additive Abelian Group generated by 1/2
            sage: DiscreteValueGroup(2/7) + DiscreteValueGroup(4/9)
            Additive Abelian Group generated by 2/63

        """
        if not isinstance(other, DiscreteValueGroup):
            from sage.structure.element import is_Element
            if is_Element(other) and QQ.has_coerce_map_from(other.parent()):
                return self + DiscreteValueGroup(other)
            raise ValueError("`other` must be a DiscreteValueGroup or a rational number")
        return DiscreteValueGroup(self._generator.gcd(other._generator))

    def _mul_(self, other, switch_sides=False):
        r"""
        Return the group generated by ``other`` times the generator of this
        group.

        INPUT:

        - ``other`` -- a rational number

        EXAMPLES::

            sage: from mac_lane import * # optional: standalone
            sage: D = DiscreteValueGroup(1/2)
            sage: 1/2 * D
            Additive Abelian Group generated by 1/4
            sage: D * (1/2)
            Additive Abelian Group generated by 1/4
            sage: D * 0
            Trivial Additive Abelian Group

        """
        from sage.misc.functional import coerce
        other = coerce(QQ, other)
        return DiscreteValueGroup(self._generator*other)

    def index(self, other):
        r"""
        Return the index of ``other`` in this group.

        INPUT:

        - ``other`` -- a subgroup of this group

        EXAMPLES::

            sage: from mac_lane import * # optional: standalone
            sage: DiscreteValueGroup(3/8).index(DiscreteValueGroup(3))
            8
            sage: DiscreteValueGroup(3).index(DiscreteValueGroup(3/8))
            Traceback (most recent call last):
            ...
            ValueError: other must be a subgroup of this group
            sage: DiscreteValueGroup(3).index(DiscreteValueGroup(0))
            Traceback (most recent call last):
            ...
            ValueError: other must have finite index in this group
            sage: DiscreteValueGroup(0).index(DiscreteValueGroup(0))
            1
            sage: DiscreteValueGroup(0).index(DiscreteValueGroup(3))
            Traceback (most recent call last):
            ...
            ValueError: other must be a subgroup of this group

        """
        if not isinstance(other, DiscreteValueGroup):
            raise ValueError("other must be a DiscreteValueGroup")
        if other._generator not in self:
            raise ValueError("other must be a subgroup of this group")
        if other._generator == 0:
            if self._generator == 0:
                return ZZ(1)
            else:
                raise ValueError("other must have finite index in this group")
        return ZZ(other._generator / self._generator)

    def numerator(self):
        r"""
        Return the numerator of a generator of this group.

        EXAMPLES::

            sage: from mac_lane import * # optional: standalone
            sage: DiscreteValueGroup(3/8).numerator()
            3

        """
        return self._generator.numerator()

    def denominator(self):
        r"""
        Return the denominator of a generator of this group.

        EXAMPLES::

            sage: from mac_lane import * # optional: standalone
            sage: DiscreteValueGroup(3/8).denominator()
            8

        """
        return self._generator.denominator()

    def gen(self):
        r"""
        Return a generator of this group.

        EXAMPLES::

            sage: from mac_lane import * # optional: standalone
            sage: DiscreteValueGroup(-3/8).gen()
            3/8

        """
        return self._generator

    def some_elements(self):
        r"""
        Return some typical elements in this group.

        EXAMPLES::

            sage: from mac_lane import * # optional: standalone
            sage: DiscreteValueGroup(-3/8).some_elements()
            [3/8, -3/8, 0, 42, 3/2, -3/2, 9/8, -9/8]

        """
        return [self._generator, -self._generator] + [x for x in QQ.some_elements() if x in self]

    def is_trivial(self):
        r"""
        Return whether this is the trivial additive abelian group.

        EXAMPLES::

            sage: from mac_lane import * # optional: standalone
            sage: DiscreteValueGroup(-3/8).is_trivial()
            False
            sage: DiscreteValueGroup(0).is_trivial()
            True

        """
        return self._generator.is_zero()
