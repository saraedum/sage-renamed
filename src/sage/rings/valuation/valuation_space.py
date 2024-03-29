# -*- coding: utf-8 -*-
r"""
Spaces of valuations

This module provides spaces of exponential pseudo-valuations on integral
domains. It currently, only provides support for such valuations if they are
discrete, i.e., their image is a discrete additive subgroup of the rational
numbers extended by `\infty`.

EXAMPLES::

    sage: from mac_lane import * # optional: standalone
    sage: pAdicValuation(QQ, 2).parent()
    Discrete pseudo-valuations on Rational Field

AUTHORS:

- Julian Rüth (2016-10-14): initial version

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

from sage.categories.homset import Homset
from sage.misc.lazy_attribute import lazy_attribute
from sage.misc.abstract_method import abstract_method
from sage.structure.unique_representation import UniqueRepresentation

class DiscretePseudoValuationSpace(UniqueRepresentation, Homset):
    r"""
    The space of discrete pseudo-valuations on ``domain``.

    EXAMPLES::

        sage: from mac_lane import * # optional: standalone
        sage: H = DiscretePseudoValuationSpace(QQ)
        sage: pAdicValuation(QQ, 2) in H
        True

    .. NOTE::

        We do not distinguish between the space of discrete valuations and the
        space of discrete pseudo-valuations. This is entirely for practical
        reasons: We would like to model the fact that every discrete valuation
        is also a discrete pseudo-valuation. At first, it seems to be
        sufficient to make sure that the ``in`` operator works which can
        essentially be achieved by overriding ``_element_constructor_`` of
        the space of discrete pseudo-valuations to accept discrete valuations
        by just returning them. Currently, however, if one does not change the
        parent of an element in ``_element_constructor_`` to ``self``, then
        one can not register that conversion as a coercion. Consequently, the
        operators ``<=`` and ``>=`` can not be made to work between discrete
        valuations and discrete pseudo-valuations on the same domain (because
        the implementation only calls ``_richcmp`` if both operands have the
        same parent.) Of course, we could override ``__ge__`` and  ``__le__``
        but then we would likely run into other surprises.
        So in the end, we went for a single homspace for all discrete
        valuations (pseudo or not) as this makes the implementation much
        easier.

    TESTS::

        sage: TestSuite(H).run() # long time

    """
    def __init__(self, domain):
        r"""
        TESTS::

            sage: from mac_lane import * # optional: standalone
            sage: isinstance(pAdicValuation(QQ, 2).parent(), DiscretePseudoValuationSpace)
            True

        """
        from value_group import DiscreteValuationCodomain
        # A valuation is a map from an additive semigroup to an additive semigroup, however, it
        # does not preserve that structure. It is therefore only a morphism in the category of sets.
        from sage.categories.all import Sets

        UniqueRepresentation.__init__(self)
        Homset.__init__(self, domain, DiscreteValuationCodomain(), category = Sets())

        from sage.categories.domains import Domains
        if domain not in Domains():
            raise ValueError("domain must be an integral domain")

    @lazy_attribute
    def _abstract_element_class(self):
        r"""
        Return an abstract base class for all valuations in this space.

        This is used to extend every valuation with a number of generic methods
        that are independent of implementation details.

        Usually, extensions of this kind would be done by implementing an
        appropriate class ``MorphismMethods`` in the category of this homset.
        However, there is no category whose arrows are the valuations, so we
        need to move this magic down to the level of the actual homset.

        EXAMPLES::

            sage: from mac_lane import * # optional: standalone
            sage: isinstance(pAdicValuation(QQ, 2), DiscretePseudoValuationSpace.ElementMethods) # indirect doctest
            True

        """
        class_name = "%s._abstract_element_class"%self.__class__.__name__
        from sage.structure.dynamic_class import dynamic_class
        return dynamic_class(class_name, (super(DiscretePseudoValuationSpace,self)._abstract_element_class, self.__class__.ElementMethods))

    def _get_action_(self, S, op, self_on_left):
        r"""
        Return the ``op`` action of ``S`` on elements in this space.

        EXAMPLES::

            sage: from mac_lane import * # optional: standalone
            sage: v = pAdicValuation(QQ, 2)
            sage: from operator import mul
            sage: v.parent().get_action(ZZ, mul) # indirect doctest

        """
        from operator import mul, div
        from sage.rings.all import QQ, InfinityRing, ZZ
        if op == mul and not self_on_left and (S is InfinityRing or S is QQ or S is ZZ):
            return ScaleAction(S, self)
        if op == div and self_on_left and (S is InfinityRing or S is QQ or S is ZZ):
            return InverseScaleAction(self, S)
        return None

    def _an_element_(self):
        r"""
        Return a trivial valuation in this space.

        EXAMPLES::

            sage: from mac_lane import * # optional: standalone
            sage: DiscretePseudoValuationSpace(QQ).an_element() # indirect doctest
            Trivial pseudo-valuation on Rational Field

        """
        from trivial_valuation import TrivialPseudoValuation
        return TrivialPseudoValuation(self.domain())

    def _repr_(self):
        r"""
        Return a printable representation of this space.
        
        EXAMPLES::

            sage: from mac_lane import * # optional: standalone
            sage: DiscretePseudoValuationSpace(QQ) # indirect doctest
            Discrete pseudo-valuations on Rational Field

        """
        return "Discrete pseudo-valuations on %r"%(self.domain(),)

    def __contains__(self, x):
        r"""
        Return whether ``x`` is a valuation in this space.

        EXAMPLES:

            sage: from mac_lane import * # optional: standalone
            sage: H = DiscretePseudoValuationSpace(QQ)
            sage: H.an_element() in H
            True

        Elements of spaces which embed into this spaces are correctly handled::

            sage: pAdicValuation(QQ, 2) in H
            True

        """
        # override the logic from Homset with the original implementation for Parent
        # which entirely relies on a proper implementation of
        # _element_constructor_ and coercion maps
        from sage.structure.parent import Parent
        return Parent.__contains__(self, x)

    def __call__(self, x):
        r"""
        Create an element in this space from ``x``.

        EXAMPLES:

            sage: from mac_lane import * # optional: standalone
            sage: H = DiscretePseudoValuationSpace(QQ)
            sage: H(pAdicValuation(QQ, 2))
            2-adic valuation

        """
        # override the logic from Homset with the original implementation for Parent
        # which entirely relies on a proper implementation of
        # _element_constructor_ and coercion maps
        from sage.structure.parent import Parent
        return Parent.__call__(self, x)

    def _element_constructor_(self, x):
        r"""
        Create an element in this space from ``x``,

        EXAMPLES:

        We try to convert valuations defined on different domains by changing
        their base ring::

            sage: from mac_lane import * # optional: standalone
            sage: Z = DiscretePseudoValuationSpace(ZZ)
            sage: Q = DiscretePseudoValuationSpace(QQ)
            sage: v = pAdicValuation(ZZ, 2)
            sage: v in Q
            False
            sage: Q(v) in Q
            True
            sage: Q(v) in Z
            False
            sage: Z(Q(v)) in Z
            True

        We support coercions and conversions, even though they are not
        implemented here::

            sage: Z(v)
            2-adic valuation

        """
        if isinstance(x.parent(), DiscretePseudoValuationSpace):
            if x.domain() is not self.domain():
                try:
                    return self(x.change_domain(self.domain()))
                except NotImplementedError:
                    pass
            else:
                return x
        raise ValueError("element can not be converted into the space of %r"%(self,))

    class ElementMethods:
        r"""
        Provides methods for discrete pseudo-valuations that are added
        automatically to valuations in this space.

        EXAMPLES:

        Here is an example of a method that is automagically added to a
        discrete valuation::

            sage: from mac_lane import * # optional: standalone
            sage: H = DiscretePseudoValuationSpace(QQ)
            sage: pAdicValuation(QQ, 2).is_discrete_pseudo_valuation() # indirect doctest
            True

        The methods will be provided even if the concrete types is not created
        with :meth:`__make_element_class__`::

            sage: from valuation import DiscretePseudoValuation
            sage: m = DiscretePseudoValuation(H)
            sage: m.parent() is H
            True
            sage: m.is_discrete_pseudo_valuation()
            True

        However, the category framework advises you to use inheritance::

            sage: m._test_category()
            Traceback (most recent call last):
            ...
            AssertionError: False is not true

        Using :meth:`__make_element_class__`, makes your concrete valuation
        inherit from this class::

            sage: m = H.__make_element_class__(DiscretePseudoValuation)(H)
            sage: m._test_category()

        """
        def is_discrete_pseudo_valuation(self):
            r"""
            Return whether this valuation is a discrete pseudo-valuation.

            EXAMPLES::

                sage: from mac_lane import * # optional: standalone
                sage: pAdicValuation(QQ, 2).is_discrete_pseudo_valuation()
                True

            """
            return True

        @abstract_method
        def is_discrete_valuation(self):
            r"""
            Return whether this valuation is a discrete valuation, i.e.,
            whether it is a :meth:`is_discrete_pseudo_valuation` that only
            sends zero to `\infty`.

            EXAMPLES::

                sage: from mac_lane import * # optional: standalone
                sage: pAdicValuation(QQ, 2).is_discrete_valuation()
                True
            
            """

        def is_trivial(self):
            r"""
            Return whether this valuation is trivial, i.e., whether it is
            constant `\infty` or constant zero for everything but the zero
            element.

            Subclasses need to override this method if they do not implement
            :meth:`uniformizer`.

            EXAMPLES::

                sage: from mac_lane import * # optional: standalone
                sage: pAdicValuation(QQ, 7).is_trivial()
                False

            """
            from sage.rings.all import infinity
            if self(self.domain().one()) == infinity:
                # the constant infinity
                return True
            if self(self.uniformizer()) != 0:
                # not constant on the non-zero elements
                return False
            return True

        @abstract_method
        def uniformizer(self):
            r"""
            Return an element in :meth:`domain` which has positive valuation
            and generates the value group of this valuation.

            EXAMPLES::

                sage: from mac_lane import * # optional: standalone
                sage: pAdicValuation(QQ, 11).uniformizer()
                11

            Trivial valuations have no uniformizer::

                sage: v = DiscretePseudoValuationSpace(QQ).an_element()
                sage: v.is_trivial()
                True
                sage: v.uniformizer()
                Traceback (most recent call last):
                ...
                ValueError: Trivial valuations do not define a uniformizing element
                
            """

        def value_group(self, **options):
            r"""
            Return the value group of this discrete pseudo-valuation, a
            discrete additive subgroup of the rational numbers.

            EXAMPLES::

                sage: from mac_lane import * # optional: standalone
                sage: pAdicValuation(QQ, 2).value_group()
                Additive Abelian Group generated by 1

            A pseudo-valuation that is `\infty` everywhere, does not have a
            value group::

                sage: v = DiscretePseudoValuationSpace(QQ).an_element()
                sage: v.value_group()
                Traceback (most recent call last):
                ...
                ValueError: The trivial pseudo-valuation that is infinity everywhere does not have a value group.

            """
            from value_group import DiscreteValueGroup
            return DiscreteValueGroup(self(self.uniformizer()))

        def shift(self, x, s):
            r"""
            Return a modified version of ``x`` whose valuation is increased by ``s``.

            The element returned is such that repeated shifts which go back to
            the original valuation produce the same element in reduction.

            EXAMPLES:

            Negative shifts are not always possible::

                sage: from mac_lane import * # optional: standalone
                sage: v = pAdicValuation(ZZ, 2)
                sage: v.shift(2, -1)
                1
                sage: v.shift(2, -2)
                Traceback (most recent call last):
                ...
                ValueError: can not shift 2 down by 2 in Integer Ring with respect to 2-adic valuation

            The element is the same after several shifts that produce an
            element of the original valuation::

                sage: v.shift(v.shift(1, 10), -10)
                1

            However, this is not always possible unless we are over a field::

                sage: R.<x> = QQ[]
                sage: v = GaussValuation(R, pAdicValuation(QQ, 2))
                sage: w = v.augmentation(x, 1/2)

                sage: w.shift(1, -1/2)
                Traceback (most recent call last):
                ...
                NotImplementedError: Shifts with consistent reduction not implemented for this augmented valuation

            Of course, we could return ``x/2`` here, but what would
            ``v.shift(1, -1)`` return? ``x^2/4`` or rather ``1/2``?
            There is no way to make this consistent in general unless we go to
            the fraction field of ``R``.

            Multiplication by an :meth:`element_with_valuation` might sometimes
            produce useful results in such cases::

                sage: 1 * w.element_with_valuation(-1/2)
                1/2*x

            However, this does not preserve the element in reduction::

                sage: 1 * w.element_with_valuation(-1/2) * w.element_with_valuation(1/2)
                1/2*x^2

            In general this is only possible by using an
            :meth:`equivalence_unit` and its :meth:`equialence_reciprocal`.
            These do, however, not exist for all values of ``s``.

            """
            x = self.domain().coerce(x)
            from sage.rings.all import QQ, ZZ, infinity
            s = QQ.coerce(s)
            if s == 0:
                return x
            if x == 0:
                raise ValueError("can not shift zero")
            if s not in self.value_group():
                raise ValueError("s must be in the value group of this valuation")
            if s < 0 and ~self.uniformizer() not in self.domain():
                from sage.categories.fields import Fields
                assert(self.domain() not in Fields())
                if -s > self(x):
                    raise ValueError("can not shift %r down by %r in %r with respect to %r"%(x, -s, self.domain(), self))
            return self.domain()(x * (self.domain().fraction_field()(self.uniformizer()) ** ZZ(s/self.value_group().gen())))

        @abstract_method
        def residue_ring(self):
            r"""
            Return the residue ring of this valuation, i.e., the elements of
            non-negative valuation module the elements of positive valuation.

            This is identical to :meth:`residue_field` when a residue field
            exists.

            EXAMPLES::

                sage: from mac_lane import * # optional: standalone
                sage: pAdicValuation(QQ, 2).residue_ring()
                Finite Field of size 2
                sage: TrivialValuation(QQ).residue_ring()
                Rational Field

            Note that a residue ring always exists, even when a residue field
            may not::

                sage: TrivialPseudoValuation(QQ).residue_ring()
                Quotient of Rational Field by the ideal (1)
                sage: TrivialValuation(ZZ).residue_ring()
                Integer Ring
                sage: GaussValuation(ZZ['x'], pAdicValuation(ZZ, 2)).residue_ring()
                Univariate Polynomial Ring in x over Finite Field of size 2 (using NTL)


            """

        def residue_field(self):
            r"""
            Return the residue field of this valuation, i.e., the field of
            fractions of the :meth:`residue_ring`, the elements of non-negative
            valuation module the elements of positive valuation.

            EXAMPLES::

                sage: from mac_lane import * # optional: standalone
                sage: pAdicValuation(QQ, 2).residue_field()
                Finite Field of size 2
                sage: TrivialValuation(QQ).residue_field()
                Rational Field

                sage: TrivialValuation(ZZ).residue_field()
                Rational Field
                sage: GaussValuation(ZZ['x'], pAdicValuation(ZZ, 2)).residue_field()
                Rational function field in x over Finite Field of size 2

            """
            if not self.is_discrete_valuation():
                raise NotImplementedError

            ret = self.residue_ring()
            from sage.categories.fields import Fields
            if ret in Fields():
                return ret
            from sage.rings.polynomial.polynomial_ring import is_PolynomialRing
            if is_PolynomialRing(ret):
                from sage.rings.function_field.all import FunctionField
                return FunctionField(ret.base_ring().fraction_field(), names=(ret.variable_name(),))
            return ret.fraction_field()


        @abstract_method
        def reduce(self, x):
            r"""
            Return the image of ``x`` in the :meth:`residue_ring` of this
            valuation.

            EXAMPLES::

                sage: from mac_lane import * # optional: standalone
                sage: v = pAdicValuation(QQ, 2)
                sage: v.reduce(2)
                0
                sage: v.reduce(1)
                1
                sage: v.reduce(1/3)
                1
                sage: v.reduce(1/2)
                Traceback (most recent call last):
                ...
                ValueError: reduction is only defined for elements of non-negative valuation

            """

        @abstract_method
        def lift(self, X):
            r"""
            Return a lift of ``X`` in :meth:`domain` which reduces down to
            ``X`` again via :meth:`reduce`.

            EXAMPLES::

                sage: from mac_lane import * # optional: standalone
                sage: v = pAdicValuation(QQ, 2)
                sage: v.lift(v.residue_ring().one())
                1

            """

        def extension(self, ring):
            r"""
            Return the unique extension of this valuation to ``ring``.

            EXAMPLES::

                sage: from mac_lane import * # optional: standalone
                sage: v = pAdicValuation(ZZ, 2)
                sage: w = v.extension(QQ)
                sage: w.domain()
                Rational Field

            """
            extensions = self.extensions(ring)
            assert(len(extensions))
            if len(extensions) > 1:
                raise ValueError("there is no unique extension of %r from %r to %r"%(self, self.domain(), ring))
            return extensions[0]

        def extensions(self, ring):
            r"""
            Return the extensions of this valuation to ``ring``.

            EXAMPLES::

                sage: from mac_lane import * # optional: standalone
                sage: v = pAdicValuation(ZZ, 2)
                sage: v.extensions(QQ)
                [2-adic valuation]

            """
            if ring is self.domain():
                return [self]
            raise NotImplementedError("extending %r from %r to %r not implemented"%(self, self.domain(), ring))

        def restriction(self, ring):
            r"""
            Return the restriction of this valuation to ``ring``.

            EXAMPLES::

                sage: from mac_lane import * # optional: standalone
                sage: v = pAdicValuation(QQ, 2)
                sage: w = v.restriction(ZZ)
                sage: w.domain()
                Integer Ring

            """
            if ring is self.domain():
                return self
            raise NotImplementedError("restricting %r from %r to %r not implemented"%(self, self.domain(), ring))

        def change_domain(self, ring):
            r"""
            Return this valuation over ``ring``.

            Unlike :meth:`extension` or meth:`reduction`, this might not be
            completely sane mathematically. It is essentially a conversion of
            this valuation into another space of valuations.

            EXAMPLES::

                sage: from mac_lane import * # optional: standalone
                sage: v = pAdicValuation(QQ, 3)
                sage: v.change_domain(ZZ)
                3-adic valuation

            """
            if ring is self.domain():
                return self
            if self.domain().is_subring(ring):
                return self.extension(ring)
            if ring.is_subring(self.domain()):
                return self.restriction(ring)
            raise NotImplementedError("changing %r from %r to %r not implemented"%(self, self.domain(), ring))

        def scale(self, scalar):
            r"""
            Return this valuation scaled by ``scalar``.

            INPUT:

            - ``scalar`` -- a non-negative rational number or infinity

            EXAMPLES::

                sage: from mac_lane import * # optional: standalone
                sage: v = pAdicValuation(ZZ, 3)
                sage: w = v.scale(3)
                sage: w(3)
                3
        
            Scaling can also be done through multiplication with a scalar::

                sage: w/3 == v
                True

            Multiplication by zero produces the trivial discrete valuation::

                sage: w = 0*v
                sage: w(3)
                0
                sage: w(0)
                +Infinity

            Multiplication by infinity produces the trivial discrete
            pseudo-valuation::

                sage: w = infinity*v
                sage: w(3)
                +Infinity
                sage: w(0)
                +Infinity

            """
            from sage.rings.all import infinity
            if scalar == infinity:
                from trivial_valuation import TrivialPseudoValuation
                return TrivialPseudoValuation(self.domain())
            if scalar == 0:
                from trivial_valuation import TrivialValuation
                return TrivialValuation(self.domain())
            if scalar == 1:
                return self
            if scalar < 0:
                raise ValueError("scalar must be non-negative")
            if self.is_trivial():
                return self

            from scaled_valuation import ScaledValuation_generic
            if isinstance(self, ScaledValuation_generic):
                return self._base_valuation.scale(scalar * self._scale)

            from scaled_valuation import ScaledValuation
            return ScaledValuation(self, scalar)

        def separating_element(self, others):
            r"""
            Return an element in the domain of this valuation which has
            positive valuation with respect to this valuation but negative
            valuation with respect to the valuations in ``others``.

            EXAMPLES::

                sage: from mac_lane import * # optional: standalone
                sage: v2 = pAdicValuation(QQ, 2)
                sage: v3 = pAdicValuation(QQ, 3)
                sage: v5 = pAdicValuation(QQ, 5)
                sage: v2.separating_element([v3,v5])
                4/15

            """
            try:
                iter(others)
            except TypeError:
                raise ValueError("others must be a list of valuations")

            for other in others + [self]:
                if other.parent() is not self.parent():
                    raise ValueError("all valuations must be valuations on %r but %r is a valuation on %r"%(self.domain(), other, other.domain()))
                if not other.is_discrete_valuation():
                    raise ValueError("all valuationss must be discrete valuations but %r is not"%(other,))
                if other.is_trivial():
                    raise ValueError("all valuations must be non-trivial but %r is not"%(other,))

            if len(others)==0:
                return self.uniformizer()

            # see the proof of Lemma 6.9 in http://www1.spms.ntu.edu.sg/~frederique/antchap6.pdf
            ret = self._strictly_separating_element(others[0])
            for i in range(1, len(others)):
                # ret is an element which separates self and others[:i]
                if others[i](ret) < 0:
                    # it also separates self and others[i]
                    continue

                delta = self._strictly_separating_element(others[i])
                if others[i](ret) == 0:
                    # combining powers of ret and delta, we produce a
                    # separating element for self and others[:i+1]
                    factor = ret
                    ret = delta
                    while any(other(ret) >= 0 for other in others[:i]):
                        assert(others[i](ret) < 0)
                        ret *= factor
                else: # others[i](ret) > 0
                    # construct an element which approximates a unit with respect to others[i]
                    # and has negative valuation with respect to others[:i]
                    from sage.rings.all import NN
                    for r in iter(NN):
                        # When we enter this loop we are essentially out of
                        # luck.  The size of the coefficients is likely going
                        # through the roof here and this is not going to
                        # terminate in reasonable time.
                        factor = (ret**r)/(1+ret**r)
                        ret = factor * delta
                        if all([other(ret) < 0 for other in others[:i+1]]):
                            break
            return ret

        def _strictly_separating_element(self, other):
            r"""
            Return an element in the domain of this valuation which has
            positive valuation with respect to this valuation but negative
            valuation with respect to ``other``.

            .. NOTE::
            
                Overriding this method tends to be a nuissance as you need to
                handle all possible types (as in Python type) of valuations.
                This is essentially the same problem that you have when
                implementing operators such as ``+`` or ``>=``. A sufficiently
                fancy multimethod implementation could solve that here but
                there is currently nothing like that in Sage/Python.

            EXAMPLES::

                sage: from mac_lane import * # optional: standalone
                sage: v2 = pAdicValuation(QQ, 2)
                sage: v3 = pAdicValuation(QQ, 3)
                sage: v2._strictly_separating_element(v3)
                2/3

            """
            from sage.rings.all import ZZ, NN, infinity

            numerator = self._weakly_separating_element(other)
            n = self(numerator)
            nn = other(numerator)
            assert(n > 0)
            assert(nn != infinity)
            if (nn < 0):
                return numerator

            denominator = other._weakly_separating_element(self)
            d = self(denominator)
            dd = other(denominator)
            assert(dd > 0)
            assert(d != infinity)
            if d < 0:
                return self.domain()(1/denominator)

            # We need non-negative integers a and b such that
            # a*n - b*d > 0 and a*nn - b*dd < 0
            if nn == 0:
                # the above becomes b != 0 and a/b > d/n
                b = 1
                if d/n in ZZ:
                    a = d/n + 1
                else:
                    a = (d/n).ceil()
            else:
                # Since n,nn,d,dd are all non-negative this is essentially equivalent to
                # a/b > d/n and b/a > nn/dd
                # which is 
                # dd/nn > a/b > d/n
                assert(dd/nn > d/n)
                for b in iter(NN):
                    # we naĩvely find the smallest b which can satisfy such an equation
                    # there are faster algorithms for this
                    # https://dl.acm.org/citation.cfm?id=1823943&CFID=864015776&CFTOKEN=26270402
                    if b == 0:
                        continue
                    assert(b <= n + nn) # (a+b)/(n+nn) is a solution
                    if nn/dd/b in ZZ:
                        a = nn/dd/b + 1
                    else:
                        a = (nn/dd/b).ceil()
                    assert(a/b > d/n)
                    if dd/nn > a/b:
                        break
                
            ret = self.domain()(numerator**a / denominator**b)
            assert(self(ret) > 0)
            assert(other(ret) < 0)
            return ret

        def _weakly_separating_element(self, other):
            r"""
            Return an element in the domain of this valuation which has
            positive valuation with respect to this valuation and higher
            valuation with respect to this valuation than with respect to
            ``other``.

            .. NOTE::
            
                Overriding this method tends to be a nuissance as you need to
                handle all possible types (as in Python type) of valuations.
                This is essentially the same problem that you have when
                implementing operators such as ``+`` or ``>=``. A sufficiently
                fancy multimethod implementation could solve that here but
                there is currently nothing like that in Sage/Python.

            EXAMPLES::

                sage: from mac_lane import * # optional: standalone
                sage: v2 = pAdicValuation(QQ, 2)
                sage: v3 = pAdicValuation(QQ, 3)
                sage: v2._weakly_separating_element(v3)
                2

            """
            ret = self.uniformizer()
            if self(ret) > other(ret):
                return ret
            raise NotImplementedError("weakly separating element for %r and %r"%(self, other))

        def _test_scale(self, **options):
            r"""
            Check that :meth:`scale` works correctly.

            TESTS::

                sage: from mac_lane import * # optional: standalone
                sage: v = pAdicValuation(ZZ, 3)
                sage: v._test_scale()

            """
            tester = self._tester(**options)

            from sage.rings.all import infinity, QQ
            from trivial_valuation import TrivialValuation, TrivialPseudoValuation

            tester.assertEqual(QQ(0)*self, TrivialValuation(self.domain()))
            tester.assertEqual(infinity*self, TrivialPseudoValuation(self.domain()))

            for s in tester.some_elements(QQ.some_elements()):
                if s < 0:
                    with tester.assertRaises(ValueError):
                        s * self
                    continue
                if s == 0:
                    continue

                scaled = s * self

                tester.assertEqual(self.is_trivial(), scaled.is_trivial())
                if not self.is_trivial():
                    tester.assertEqual(self.uniformizer(), scaled.uniformizer())
                    tester.assertEqual(scaled(self.uniformizer()), s * self(self.uniformizer()))
                unscaled = scaled / s
                tester.assertEqual(self, unscaled)

        def _test_add(self, **options):
            r"""
            Check that the (strict) triangle equality is satisfied for the
            valuation of this ring.

            TESTS::

                sage: from mac_lane import * # optional: standalone
                sage: v = pAdicValuation(ZZ, 3)
                sage: v._test_add()

            """
            tester = self._tester(**options)
            S = self.domain().some_elements()
            from itertools import product
            for x,y in tester.some_elements(product(S,S)):
                tester.assertGreaterEqual(self(x+y),min(self(x),self(y)))
                if self(x) != self(y):
                    tester.assertEqual(self(x+y),min(self(x),self(y)))

        def _test_infinite_zero(self, **options):
            r"""
            Check that zero is sent to infinity.

            TESTS::

                sage: from mac_lane import * # optional: standalone
                sage: v = pAdicValuation(QQ, 5)
                sage: v._test_infinite_zero()

            """
            tester = self._tester(**options)
            from sage.rings.all import infinity
            tester.assertEqual(self(self.domain().zero()), infinity)

        def _test_mul(self, **options):
            r"""
            Check that multiplication translates to addition of valuations.

            TESTS::

                sage: from mac_lane import * # optional: standalone
                sage: v = pAdicValuation(QQ, 5)
                sage: v._test_mul()

            """
            tester = self._tester(**options)
            S = self.domain().some_elements()
            from itertools import product
            for x,y in tester.some_elements(product(S,S)):
                tester.assertEqual(self(x*y),self(x)+self(y))

        def _test_no_infinite_units(self, **options):
            r"""
            Checks that no units are sent to infinity.

            TESTS::

                sage: from mac_lane import * # optional: standalone
                sage: v = pAdicValuation(QQ, 5)
                sage: v._test_no_infinite_units()

            As multiplication translates to addition, pseudo-valuations which
            send a unit to infinity are necessarily trivial::

                sage: v = DiscretePseudoValuationSpace(QQ).an_element()
                sage: v(1)
                +Infinity
                sage: v.is_trivial()
                True

            """
            if not self.is_discrete_valuation() and self.is_trivial():
                return

            from sage.rings.all import infinity
            tester = self._tester(**options)
            for x in tester.some_elements(self.domain().some_elements()):
                if self(x) == infinity:
                    tester.assertFalse(x.is_unit())

        def _test_value_group(self, **options):
            r"""
            Check correctness of the value group.

            TESTS::

                sage: from mac_lane import * # optional: standalone
                sage: v = pAdicValuation(QQ, 5)
                sage: v._test_value_group()

            """
            from sage.rings.all import infinity
            tester = self._tester(**options)
            # check consistency of trivial valuations first
            if self.is_trivial():
                if self(self.domain().one()) == infinity:
                    # a trivial pseudo-valuation that sends everything to infinity
                    with tester.assertRaises(ValueError):
                        self.value_group()
                    return

            # check that all valuations are in the value group
            for x in tester.some_elements(self.domain().some_elements()):
                if self(x) != infinity:
                    tester.assertIn(self(x), self.value_group())

            if not self.is_trivial():
                # check that the uniformizer generates the value group
                tester.assertEqual(self.value_group().gen(), self(self.uniformizer()))

        def _test_shift(self, **options):
            r"""
            Check correctness of shifts.

            TESTS::

                sage: from mac_lane import * # optional: standalone
                sage: v = pAdicValuation(QQ, 5)
                sage: v._test_shift() # long time

            """
            tester = self._tester(**options)

            if self.is_trivial():
                # trivial valuations can not perform non-trivial shifts
                return

            S = self.domain().some_elements()
            V = self.value_group().some_elements()
            from itertools import product
            for x, n in tester.some_elements(product(S,V)):
                if x == 0 and n != 0:
                    with tester.assertRaises((ValueError, NotImplementedError)):
                        self.shift(x, n)
                    continue

                v = self(x)
                try:
                    y = self.shift(x, n)
                except NotImplementedError:
                    # not all valuations can implement consistent shifts
                    continue
                except ValueError:
                    from sage.categories.fields import Fields
                    if -n > v and self.domain() not in Fields():
                        continue
                    raise

                tester.assertIs(y.parent(), self.domain())
                tester.assertEqual(self(y), v + n)
                # shifts preserve reductions
                z = self.shift(y, -n)
                tester.assertEqual(self(z), v)
                if v >= 0:
                    tester.assertEqual(self.reduce(z), self.reduce(x))

        def _test_residue_ring(self, **options):
            r"""
            Check the correctness of residue rings.

            TESTS::

                sage: from mac_lane import * # optional: standalone
                sage: v = pAdicValuation(QQ, 5)
                sage: v._test_residue_ring()

            """
            tester = self._tester(**options)

            try:
                r = self.residue_ring()
            except NotImplementedError:
                # over non-fields (and especially polynomial rings over
                # non-fields) computation of the residue ring is often
                # difficult and not very interesting
                from sage.categories.fields import Fields
                if self.domain() in Fields():
                    raise
                return

            if r.zero() == r.one():
                # residue ring is the zero rng
                tester.assertGreater(self(1), 0)
                return

            c = self.residue_ring().characteristic()
            if c != 0:
                tester.assertGreater(self(c), 0)

        def _test_reduce(self, **options):
            r"""
            Check the correctness of reductions.

            TESTS::

                sage: from mac_lane import * # optional: standalone
                sage: v = pAdicValuation(QQ, 5)
                sage: v._test_reduce()

            """
            tester = self._tester(**options)

            try:
                k = self.residue_ring()
            except NotImplementedError:
                # over non-fields (and especially polynomial rings over
                # non-fields) computation of the residue ring is often
                # difficult and not very interesting
                from sage.categories.fields import Fields
                if self.domain() in Fields():
                    raise
                return

            for x in tester.some_elements(self.domain().some_elements()):
                if self(x) < 0:
                    with tester.assertRaises(ValueError):
                        self.reduce(x)
                    continue
                if self(x) == 0:
                    y = self.reduce(x)
                    tester.assertIn(y, self.residue_ring())
                    tester.assertNotEqual(y, 0)
                    if x.is_unit() and ~x in self.domain():
                        tester.assertTrue(y.is_unit())
                        tester.assertIn(~y, self.residue_ring())
                        tester.assertEqual(~y, self.reduce(self.domain()(~x)))
                if self(x) > 0:
                    tester.assertEqual(self.reduce(x), 0)

        def _test_lift(self, **options):
            r"""
            Check the correctness of lifts.

            TESTS::

                sage: from mac_lane import * # optional: standalone
                sage: v = pAdicValuation(QQ, 5)
                sage: v._test_lift()

            """
            tester = self._tester(**options)

            try:
                k = self.residue_ring()
            except NotImplementedError:
                # over non-fields (and especially polynomial rings over
                # non-fields) computation of the residue ring is often
                # difficult and not very interesting
                from sage.categories.fields import Fields
                if self.domain() in Fields():
                    raise
                return

            for X in tester.some_elements(self.residue_ring().some_elements()):
                x = self.lift(X)
                y = self.reduce(x)
                tester.assertEqual(X, y)
                if X != 0:
                    tester.assertEqual(self(x), 0)

        def _test_restriction(self, **options):
            r"""
            Check the correctness of reductions.

            TESTS::

                sage: from mac_lane import * # optional: standalone
                sage: v = pAdicValuation(QQ, 5)
                sage: v._test_restriction()

            """
            tester = self._tester(**options)

            tester.assertEqual(self.restriction(self.domain()), self)

        def _test_extension(self, **options):
            r"""
            Check the correctness of extensions.

            TESTS::

                sage: from mac_lane import * # optional: standalone
                sage: v = pAdicValuation(QQ, 5)
                sage: v._test_extension()

            """
            tester = self._tester(**options)

            tester.assertEqual(self.extension(self.domain()), self)
            tester.assertEqual(self.extensions(self.domain()), [self])

        def _test_change_domain(self, **options):
            r"""
            Check the correctness of :meth:`change_domain`.

            TESTS::

                sage: from mac_lane import * # optional: standalone
                sage: v = pAdicValuation(QQ, 5)
                sage: v._test_change_domain()

            """
            tester = self._tester(**options)

            tester.assertEqual(self.change_domain(self.domain()), self)

        def _test_no_infinite_nonzero(self, **options):
            r"""
            Check that only zero is sent to infinity.

            TESTS::

                sage: from mac_lane import * # optional: standalone
                sage: v = pAdicValuation(QQ, 5)
                sage: v._test_no_infinite_nonzero()

            """
            if not self.is_discrete_valuation():
                return

            from sage.rings.all import infinity
            tester = self._tester(**options)
            for x in tester.some_elements(self.domain().some_elements()):
                if self(x) is infinity:
                    tester.assertEqual(x, 0)

        def _test_residue_field(self, **options):
            r"""
            Check the correctness of residue fields.

            TESTS::

                sage: from mac_lane import * # optional: standalone
                sage: v = pAdicValuation(QQ, 5)
                sage: v._test_residue_field()

            """
            if not self.is_discrete_valuation():
                return

            tester = self._tester(**options)
            try:
                k = self.residue_field()
            except ValueError:
                from sage.categories.fields import Fields
                # a discrete valuation on a field has a residue field
                tester.assertFalse(self.domain() in Fields())
                return
            except NotImplementedError:
                # over non-fields (and especially polynomial rings over
                # non-fields) computation of the residue field is often
                # difficult and not very interesting
                from sage.categories.fields import Fields
                if self.domain() in Fields():
                    raise
                return

            c = self.residue_field().characteristic()
            if c != 0:
                tester.assertGreater(self(c), 0)

        def _test_ge(self, **options):
            r"""
            Check the correctness of the ``>=`` operator.

            TESTS::

                sage: from mac_lane import * # optional: standalone
                sage: v = pAdicValuation(QQ, 5)
                sage: v._test_ge()

            """
            tester = self._tester(**options)

            from trivial_valuation import TrivialPseudoValuation, TrivialValuation
            tester.assertGreaterEqual(self, self)
            tester.assertGreaterEqual(self, TrivialValuation(self.domain()))
            tester.assertLessEqual(self, TrivialPseudoValuation(self.domain()))

        def _test_le(self, **options):
            r"""
            Check the correctness of the ``<=`` operator.

            TESTS::

                sage: from mac_lane import * # optional: standalone
                sage: v = pAdicValuation(QQ, 5)
                sage: v._test_le()

            """
            tester = self._tester(**options)

            from trivial_valuation import TrivialPseudoValuation, TrivialValuation
            tester.assertGreaterEqual(self, self)
            tester.assertLessEqual(TrivialValuation(self.domain()), self)
            tester.assertGreaterEqual(TrivialPseudoValuation(self.domain()), self)

from sage.categories.action import Action
class ScaleAction(Action):
    r"""
    Action of integers, rationals and the infinity ring on valuations by
    scaling it.

    EXAMPLES::

        sage: from mac_lane import * # optional: standalone
        sage: v = pAdicValuation(QQ, 5)
        sage: from operator import mul
        sage: v.parent().get_action(IntegerRing, mul, self_on_left=False)

    """
    def _call_(self, s, v):
        r"""
        Let ``s`` act on ``v``.

        EXAMPLES::

            sage: from mac_lane import * # optional: standalone
            sage: v = pAdicValuation(QQ, 5)
            sage: 3*v # indirect doctest
            3 * 5-adic valuation
            
        """
        return v.scale(s)

class InverseScaleAction(Action):
    r"""
    Action of integers, rationals and the infinity ring on valuations by
    scaling it (with the inverse of the scalar.)

    EXAMPLES::

        sage: from mac_lane import * # optional: standalone
        sage: v = pAdicValuation(QQ, 5)
        sage: from operator import div
        sage: v.parent().get_action(IntegerRing, div, self_on_left=True)

    """
    def _call_(self, v, s):
        r"""
        Let ``s`` act on ``v`` (by division.)

        EXAMPLES::

            sage: from mac_lane import * # optional: standalone
            sage: v = pAdicValuation(QQ, 5)
            sage: v/3 # indirect doctest
            1/3 * 5-adic valuation
            
        """
        return v.scale(1/s)
