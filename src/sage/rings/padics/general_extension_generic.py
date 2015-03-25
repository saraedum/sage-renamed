"""
General extensions of `\mathbb{Q}_p` and `\mathbb{Z}_p`

This file implements the shared functionality for general extensions of p-adic rings.

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

from sage.misc.cachefunc import cached_method

from padic_extension_generic import pAdicExtensionGeneric

class GeneralExtensionGeneric(pAdicExtensionGeneric):
    """
    An extension of a p-adic ring, defined by an irreducible polynomial.
    """
    def __init__(self, prepoly, poly, prec, print_mode, names, element_class):
        """
        Initializes ``self``.

        INPUT:

            TODO

            - ``poly`` -- an irreducible polynomial over a p-adic ring

            - ``abs_ring`` -- a ring isomorphic to this ring which will be used
              to perform all calculations

            - ``to_abs_ring`` -- the image of the generator of this ring in ``abs_ring``

            - ``to_abs_ring_base`` -- a ring homomorphism from the base ring to
              ``abs_ring`` which, together with ``to_abs_ring`` defines an
              isomorphism

            - ``from_abs_ring`` -- a tuple consisting of the images of the
              generators of ``abs_ring`` in this ring (as a polynomial or
              rational function over the base ring)

            - ``prec`` -- a positive integer, the precision to use when
              representing elements this ring

            - ``print_mode`` -- a dictionary of print options

            - ``names`` -- a tuple ``(x,ubar)`` where ``x`` is a root of
              ``poly`` and ``ubar`` is the variable of the residue field.

            - ``element_class`` -- the class which implements the elements of
              this ring

        """
        pAdicExtensionGeneric.__init__(self, poly.base_ring(), poly, prec, print_mode, names, element_class)
        self._poly = poly
        assert self._poly.degree() >= 1
        self._polynomial_ring = poly.parent().change_var(names[0])
        self._prime = poly.base_ring().prime()
        self.__check = [ lambda: hasattr(self.implementation_ring(),"_check") and self.implementation_ring()._check() ]

    def _cache_key(self):
        return self._poly, self.defining_polynomial(), self._prime, self._poly.parent(), self._names

    def implementation_ring(self):
        """
        Return a ring isomorphic to this ring which implements the arithmetic
        in this ring.

        OUTPUT:

        A triple ``(R,from,to)`` where ``R`` is a ring, ``from`` is a morphism
        from ``R`` to this ring, and ``to`` is a morphism from this ring to
        ``R``.

        EXAMPLES::

            sage: K = Qp(3)
            sage: R.<x> = K[]
            sage: L.<a> = K.extension(x + 1)
            sage: L.implementation_ring()
            3-adic Field with capped relative precision 20

        """
        return self._implementation_ring()[0]

    def _from_implementation_ring(self):
        return self._implementation_ring()[1]

    def _to_implementation_ring(self):
        return self._implementation_ring()[2]

    @cached_method
    def _implementation_ring(self):
        base = self.base_ring()
        modulus = self._poly

        if any([c.valuation()<0 for c in modulus.list()]):
            raise NotImplementedError("modulus must be integral")
        if not modulus.is_monic():
            raise NotImplementedError("modulus must be monic")
        if modulus.base_ring() is not base:
            raise ValueError("modulus must be defined over base")

        from sage.rings.padics.factory import GenericExtensionFactory
        if GenericExtensionFactory.is_trivial(modulus):
            ret = self.__implementation_ring_trivial()
        elif GenericExtensionFactory.is_eisenstein(modulus):
            if base is base.ground_ring_of_tower():
                raise NotImplementedError("this case should be handled by EisensteinExtensionGeneric and its subclasses")
            elif base.maximal_unramified_subextension() is base and base.base() is base.ground_ring_of_tower():
                ret = self.__implementation_ring_eisenstein_over_simple_unramified()
            elif GenericExtensionFactory.is_eisenstein(base.modulus()) and base.maximal_unramified_subextension() is base.base():
                ret = self.__implementation_ring_eisenstein_over_eisenstein()
            else:
                ret = self.__implementation_ring_reduce_base()
        elif GenericExtensionFactory.is_totally_ramified(modulus):
            ret = self.__implementation_ring_totally_ramified()
        elif self.is_unramified():
            if base is base.ground_ring_of_tower():
                if GenericExtensionFactory.is_unramified(modulus):
                    raise NotImplementedError("this case should be handled by UnramifiedExtensionGeneric and its subclasses")
                ret = self.__implementation_ring_unramified_over_base()
            elif base.maximal_unramified_subextension() is base and base.base() is base.ground_ring_of_tower():
                ret = self.__implementation_ring_unramified_over_simple_unramified()
            elif GenericExtensionFactory.is_eisenstein(base.modulus()) and base.maximal_unramified_subextension() is base.base() and base.base() is base.ground_ring_of_tower():
                ret = self.__implementation_ring_unramified_over_simple_eisenstein()
            elif GenericExtensionFactory.is_eisenstein(base.modulus()) and base.maximal_unramified_subextension() is base.base() and base.base().base() is base.ground_ring_of_tower():
                ret = self.__implementation_ring_unramified_over_eisenstein_over_simple_unramified()
            else:
                ret = self.__implementation_ring_reduce_base()
        else:
            ret = self.__implementation_ring_general()

        assert ret[0] is not self
        assert ret[1].domain() is ret[0]
        assert ret[1].codomain() is self._polynomial_ring
        assert ret[2].domain() is self._polynomial_ring
        assert ret[2].codomain() is ret[0]

        return ret

    def __implementation_ring_reduce_base(self):
        base = self.base_ring()
        modulus = self._poly

        # reduce to the case where base is an Eisenstein over unramified extension
        base2, base2_to_base, base_to_base2 = base._isomorphic_ring()

        implementation_ring = base2.extension(modulus.map_coefficients(base_to_base2), names=modulus.parent().variable_names(),check=False)

        from_implementation_ring = implementation_ring.hom([self._polynomial_ring.gen()], base2_to_base)
        from sage.categories.homset import Hom
        from sage.categories.morphism import SetMorphism
        from sage.categories.rings import Rings
        to_implementation_ring = SetMorphism(Hom(self._polynomial_ring, implementation_ring, Rings()), lambda f: f.map_coefficients(base_to_base2)(implementation_ring.gen()))
        return implementation_ring, from_implementation_ring, to_implementation_ring

    def __implementation_ring_trivial(self):
        """
        Helper method for :meth:`__implementation_ring`` if ``modulus`` defines
        a trivial extension.

        Input and output are the same as in :meth:`__implementation_ring`.

        TESTS::

            sage: K = Qp(3,5)
            sage: R.<a> = K[]
            sage: L.<a> = K.extension(a + 1); L
            Trivial extension in a defined by (1 + O(3^5))*a + 1 + O(3^5) of 3-adic Field with capped relative precision 5
            sage: L.implementation_ring() # indirect doctest
            3-adic Field with capped relative precision 5
            sage: a == -1
            True

        Trivial over trivial extension::

            sage: K = Qp(3,5)
            sage: R.<a> = K[]
            sage: L.<a> = K.extension(a + 1)
            sage: R.<b> = L[]
            sage: M.<b> = L.extension(b + a); M
            Trivial extension in b defined by (1 + O(3^5))*b + 2 + 2*3 + 2*3^2 + 2*3^3 + 2*3^4 + O(3^5) of Trivial extension in a defined by (1 + O(3^5))*a + 1 + O(3^5) of 3-adic Field with capped relative precision 5
            sage: M.implementation_ring()
            Trivial extension in a defined by (1 + O(3^5))*a + 1 + O(3^5) of 3-adic Field with capped relative precision 5
            sage: b == 1
            True

        Trivial over unramified extension::

            sage: K.<u> = Qq(25,3)
            sage: R.<a> = K[]
            sage: L.<a> = K.extension(a - u); L
            Trivial extension in a defined by (1 + O(5^3))*a + 4*u + 4*u*5 + 4*u*5^2 + O(5^3) of Unramified Extension in u defined by (1 + O(5^3))*x^2 + (4 + O(5^3))*x + 2 + O(5^3) of 5-adic Field with capped relative precision 3
            sage: L.implementation_ring()
            Unramified Extension in u defined by (1 + O(5^3))*x^2 + (4 + O(5^3))*x + 2 + O(5^3) of 5-adic Field with capped relative precision 3
            sage: a == u
            True

        Trivial over Eisenstein extension::

            sage: K = Qp(7,4)
            sage: R.<a> = K[]
            sage: L.<a> = K.extension(a^2 - 7)
            sage: R.<b> = L[]
            sage: M.<b> = L.extension(b - a - 1); M
            Trivial extension in b defined by (1 + O(a^8))*b + 6 + 6*a + 6*a^2 + 6*a^3 + 6*a^4 + 6*a^5 + 6*a^6 + 6*a^7 + O(a^8) of Eisenstein Extension of 7-adic Field with capped relative precision 4 in a defined by (1 + O(7^4))*a^2 + 6*7 + 6*7^2 + 6*7^3 + 6*7^4 + O(7^5)
            sage: M.implementation_ring()
            Eisenstein Extension of 7-adic Field with capped relative precision 4 in a defined by (1 + O(7^4))*a^2 + 6*7 + 6*7^2 + 6*7^3 + 6*7^4 + O(7^5)
            sage: b == a + 1
            True

        Trivial over totally ramified extension::

            sage: K = Qp(7,4)
            sage: R.<a> = K[]
            sage: L.<a> = K.extension(a^2 + 7^3*a + 7^3)
            sage: R.<b> = L[]
            sage: M.<b> = L.extension(b - a); M
            Trivial extension in b defined by (1 + O(pi^8))*b + pi^3 + pi^6 + O(pi^8) of Totally ramified extension in a defined by (1 + O(7^4))*a^2 + (7^3 + O(7^7))*a + 7^3 + O(7^7) of 7-adic Field with capped relative precision 4
            sage: b == a
            True

        Trivial over general extension::

            # TODO

        """
        base = self.base_ring()
        modulus = self._poly

        if modulus.degree() != 1 or not modulus.is_monic():
            raise ValueError("modulus must be a monic polynomial of degree 1")

        implementation_ring = base
        from_implementation_ring = implementation_ring.hom(self._polynomial_ring) # the embedding
        to_implementation_ring = self._polynomial_ring.hom([-modulus[0]])
        return base, from_implementation_ring, to_implementation_ring

    def __implementation_ring_eisenstein_over_eisenstein(self):
        """
        Helper method for :meth:`__implementation_ring`` if ``modulus`` is
        Eisenstein.

        Input and output are the same as in :meth:`__implementation_ring`.

        ALGORITHM:

        ``base`` is an Eisenstein extension of an unramified extension;
        computing the resultant of the Eisenstein polynomial and modulus gives
        a single Eisenstein polynomial which defines the total extension over
        the unramified extension.

        TESTS:

        Eisenstein over Eisenstein::

            sage: K = Qp(2,4)
            sage: R.<a> = K[]
            sage: L.<a> = K.extension(a^2 - 2)
            sage: R.<b> = L[]
            sage: M.<b> = L.extension(b^2 - a); M
            Eisenstein extension in b defined by (1 + O(a^8))*b^2 + a + a^3 + a^5 + a^7 + O(a^9) of Eisenstein Extension of 2-adic Field with capped relative precision 4 in a defined by (1 + O(2^4))*a^2 + 2 + 2^2 + 2^3 + 2^4 + O(2^5)
            sage: M.implementation_ring()
            Eisenstein Extension of 2-adic Field with capped relative precision 4 in b defined by (1 + O(2^4))*b^4 + 2 + 2^2 + 2^3 + 2^4 + O(2^5)
            sage: b^4==2
            True

        Another example that came up in an application::

            sage: K = Qp(2,5)
            sage: R.<x> = K[]
            sage: f = x^4+2*x^3+2*x^2-2*x+2
            sage: L.<a> = K.extension(f)
            sage: g = (1 + O(a^20))*x^3 + (a^3 + a^5 + a^8 + a^9 + a^10 + a^12 + a^13 + a^15 + a^16 + a^17 + O(a^20))*x^2 + (a^2 + a^5 + a^7 + a^9 + a^10 + a^12 + a^13 + a^14 + a^18 + O(a^20))*x + a + a^2 + a^3 + a^4 + a^5 + a^6 + a^9 + a^10 + a^13 + a^14 + a^17 + a^18 + a^19 + O(a^20)
            sage: M.<b> = L.extension(g); M
            Eisenstein extension in b defined by (1 + O(a^20))*x^3 + (a^3 + a^5 + a^8 + a^9 + a^10 + a^12 + a^13 + a^15 + a^16 + a^17 + O(a^20))*x^2 + (a^2 + a^5 + a^7 + a^9 + a^10 + a^12 + a^13 + a^14 + a^18 + O(a^20))*x + a + a^2 + a^3 + a^4 + a^5 + a^6 + a^9 + a^10 + a^13 + a^14 + a^17 + a^18 + a^19 + O(a^21) of Eisenstein Extension of 2-adic Field with capped relative precision 5 in a defined by (1 + O(2^5))*x^4 + (2 + O(2^6))*x^3 + (2 + O(2^6))*x^2 + (2 + 2^2 + 2^3 + 2^4 + 2^5 + O(2^6))*x + 2 + O(2^6)
            sage: M.implementation_ring()
            Eisenstein Extension of 2-adic Field with capped relative precision 5 in x defined by (1 + O(2^5))*x^12 + (2 + 2^3 + 2^4 + 2^5 + O(2^6))*x^11 + (2^2 + 2^4 + O(2^6))*x^10 + (2^3 + 2^5 + O(2^6))*x^9 + (2^2 + 2^4 + O(2^6))*x^8 + (2 + 2^2 + O(2^6))*x^7 + (2^4 + O(2^6))*x^6 + (2^5 + O(2^6))*x^5 + (2^2 + 2^3 + 2^5 + O(2^6))*x^4 + (2 + 2^5 + O(2^6))*x^3 + (2^2 + 2^3 + 2^5 + O(2^6))*x^2 + (2^2 + 2^4 + O(2^6))*x + 2 + 2^4 + 2^5 + O(2^6)
            sage: g(b)
            O(b^60)

        """
        base = self.base_ring()
        modulus = self._poly

        # we cannot perform the krasner check here since we cannot honour the
        # check variable passed when creating this field. We cannot make it
        # part of the key used to create this field since evidently
        # field(check=True) and field(check=False) should not be distinct
        # objects; however, we cannot put it into the extra_args of the factory
        # since then the checks would not be performed if a field was created
        # first with check=False (which is usually the case, since the krasner
        # check uses check=False). We can also not simply always check since
        # the krasner check itself relies on the checks not being performed -
        # hence, we postpone the checks until the object is actually returned
        # to the user
        from factory import GenericExtensionFactory
        self.__check.append(lambda: GenericExtensionFactory.krasner_check(modulus, names=self.variable_names()))

        # modulus passed the krasner check, i.e., it uniquely defines a totally
        # ramified extension of base. Hence, lifting the coefficients of
        # modulus to higher precision does not change the extension this
        # defines; but it does change the root of modulus: the roots of a
        # lifted modulus might not be roots of all polynomials that reduce to
        # the unlifted modulus anymore. (see the comments below for
        # from_implementation_ring and to_implementation_ring)
        premodulus = modulus
        modulus = modulus.map_coefficients(lambda c:c.lift_to_precision())

        unramified_base = base.base()

        from sage.rings.all import PolynomialRing
        bivariate_ring = PolynomialRing(unramified_base, names=(base.variable_name(),modulus.variable_name()))
        univariate_over_unramified = bivariate_ring.remove_var(bivariate_ring.gen(1))

        epoly_ring = bivariate_ring.remove_var(bivariate_ring.gen(0))
        f = base.modulus()(bivariate_ring.gen(0))
        g = modulus.map_coefficients(lambda c:c.polynomial(), univariate_over_unramified)(bivariate_ring.gen(1))
        if self.base().residue_field().characteristic().divides(modulus.degree()) or True:
            import time
            epoly = f.sylvester_matrix(g, bivariate_ring.gen(0))(epoly_ring.zero(), epoly_ring.gen()).det()
            assert all([c.is_zero() for c in epoly.list()[modulus.degree()*base.modulus().degree()+1:]]), "epoly has too few leading zeros"
            epoly = epoly_ring(epoly.list()[:modulus.degree()*base.modulus().degree()+1])
        else:
            # this works in principle but the code below does not construct the right isomorphisms between the implementation ring this ring
            epoly = base.modulus()(base.modulus().parent().gen()**modulus.degree())(epoly_ring.gen())

        assert epoly.degree() == modulus.degree()*base.modulus().degree()

        # if we lost too much precision during the computation it might happen
        # that epoly does not define a unique extension anymore
        self.__check.append(lambda: GenericExtensionFactory.krasner_check(epoly, names=epoly.parent().variable_names()))
        # now we can safely lift epoly to higher precision
        epoly = epoly.map_coefficients(lambda c:c.lift_to_precision())

        implementation_ring = unramified_base.extension(epoly, names=epoly.parent().variable_names(), check=False) # postpone check until checks are called on self

        # since we lifted to higher precision several times, the isomorphism
        # between implementation_ring and self is not simply given by mapping a
        # root of premodulus to a root of epoly, i.e.,
        # implementation_ring.gen() <-> self.gen():
        # self.gen() is a root of all polynomials that reduce to premodulus,
        # implementation_ring.gen() is a root of all polynomials that reduce to
        # epoly.
        # By construction, self.gen() is also a root of epoly but not the other
        # way round.

        #TODO: figure this out - is this even true?

        # to get back to the Eisenstein over Eisenstein over unramified
        # extension, we ignore one of the Eisenstein extensions and simply not
        # reduce modulo the middle extension - this is probably not what we
        # want in the long run
        from_implementation_ring = implementation_ring.hom([self._polynomial_ring.gen()])

        # we find the image of the uniformizer of base in implementation_ring
        # by factoring its minpoly
        base_uniformizer = None
        for root in base.modulus().change_ring(implementation_ring).roots(multiplicities=False):
            if not g(root, implementation_ring.gen()):
                base_uniformizer = root
                break
        assert base_uniformizer is not None
        from sage.categories.rings import Rings
        from sage.categories.homset import Hom
        from sage.categories.morphism import SetMorphism
        to_implementation_ring = SetMorphism(Hom(self._polynomial_ring, implementation_ring, Rings()), lambda f: f.map_coefficients(base.hom([base_uniformizer]))(implementation_ring.uniformizer()))

        return implementation_ring, from_implementation_ring, to_implementation_ring

    def __implementation_ring_eisenstein_over_simple_unramified(self):
        """

        TESTS:

        Eisenstein over trivial. This does not call this method, it is tested
        here for consistency::

            sage: K = Qp(3,5)
            sage: R.<x> = K[]
            sage: L.<x> = K.extension(x + 3)
            sage: R.<a> = L[]
            sage: M.<a> = L.extension(a^2 + x); M
            Eisenstein extension in a defined by (1 + O(3^5))*a^2 + 2*3 + 2*3^2 + 2*3^3 + 2*3^4 + 2*3^5 + O(3^6) of Trivial extension in x defined by (1 + O(3^5))*x + 3 + O(3^6) of 3-adic Field with capped relative precision 5
            sage: M.implementation_ring()
            Eisenstein Extension of 3-adic Field with capped relative precision 5 in a defined by (1 + O(3^5))*a^2 + 2*3 + 2*3^2 + 2*3^3 + 2*3^4 + 2*3^5 + O(3^6)
            sage: a^2 == 3
            True

        Eisenstein over unramified::

            sage: K.<u> = Qq(25, 3)
            sage: R.<a> = K[]
            sage: L.<a> = K.extension(a^2 - 5*u); L
            Eisenstein extension in a defined by (1 + O(5^3))*a^2 + 4*u*5 + 4*u*5^2 + 4*u*5^3 + O(5^4) of Unramified Extension in u defined by (1 + O(5^3))*x^2 + (4 + O(5^3))*x + 2 + O(5^3) of 5-adic Field with capped relative precision 3
            sage: L.implementation_ring()
            Two step extension in ('u', 'a') defined by (1 + O(5^3))*a^2 + 4*u*5 + 4*u*5^2 + 4*u*5^3 + O(5^4) and (1 + O(5^3))*x^2 + (4 + O(5^3))*x + 2 + O(5^3) of 5-adic Field with capped relative precision 3
            sage: a^2 == 5*u
            True

        """
        base = self.base_ring()
        modulus = self._poly

        from sage.rings.padics.factory import TwoStepExtensionFactory
        implementation_ring = TwoStepExtensionFactory(base, modulus, names=modulus.parent().variable_names(), check=False)

        from_implementation_ring = implementation_ring.hom([self._polynomial_ring(base.gen()), self._polynomial_ring.gen()])
        to_implementation_ring = self._polynomial_ring.hom([implementation_ring.gen(1)])
        return implementation_ring, from_implementation_ring, to_implementation_ring

    def __implementation_ring_totally_ramified(self):
        """
        Helper method for :meth:`__implementation_ring`` if ``modulus`` defines
        a totally ramified extension but ``modulus`` is not Eisenstein.

        Input and output are the same as in :meth:`__implementation_ring`.

        ALGORITHM:

        TODO: why is this guaranteed to work?
        TODO: is this in some sense optimal?

        Uses :meth:`pAdicValuation.is_totally_ramified` to compute MacLane
        approximants. A product of the key polynomials of these defines a
        uniformizer.

        Empirically, this product gives a better minimal polynomial if it uses
        the minimal number of factors possible.  Currently, these factors are
        determined using brute force; there is probably a better way.

        TESTS::

            sage: K = Qp(3,5)
            sage: R.<x> = K[]
            sage: L.<a> = K.extension(x^2 + 3*x + 9); L
            Totally ramified extension in a defined by (1 + O(3^5))*x^2 + (3 + O(3^6))*x + 3^2 + O(3^7) of 3-adic Field with capped relative precision 5
            sage: L.implementation_ring()
            Eisenstein Extension of 3-adic Field with capped relative precision 5 in x defined by (1 + O(3^5))*x^2 + (2*3 + 2*3^2 + 2*3^3 + 2*3^4 + O(3^6))*x + 3 + O(3^6)

        Totally ramified over Eisenstein::

            sage: K = Qp(2,5)
            sage: R.<x> = K[]
            sage: f = x^4+2*x^3+2*x^2-2*x+2
            sage: L.<a> = K.extension(f)
            sage: R.<x> = L[]
            sage: g = f//(x-a); g
            (1 + O(a^20))*x^3 + (a + a^4 + a^5 + a^9 + a^10 + a^11 + a^12 + a^15 + a^17 + a^18 + a^20 + O(a^21))*x^2 + (a^2 + a^4 + a^6 + a^10 + a^14 + a^18 + a^20 + O(a^22))*x + a^3 + a^4 + a^7 + a^8 + a^10 + a^13 + a^14 + a^17 + a^18 + a^22 + O(a^23)
            sage: M.<b> = L.extension(g); M
            Totally ramified extension in b defined by (1 + O(a^20))*x^3 + (a + a^4 + a^5 + a^9 + a^10 + a^11 + a^12 + a^15 + a^17 + a^18 + a^20 + O(a^21))*x^2 + (a^2 + a^4 + a^6 + a^10 + a^14 + a^18 + a^20 + O(a^22))*x + a^3 + a^4 + a^7 + a^8 + a^10 + a^13 + a^14 + a^17 + a^18 + a^22 + O(a^23) of Eisenstein Extension of 2-adic Field with capped relative precision 5 in a defined by (1 + O(2^5))*x^4 + (2 + O(2^6))*x^3 + (2 + O(2^6))*x^2 + (2 + 2^2 + 2^3 + 2^4 + 2^5 + O(2^6))*x + 2 + O(2^6)
            sage: M.implementation_ring()
            Eisenstein extension in x defined by (1 + O(a^20))*x^3 + (a^3 + a^5 + a^8 + a^9 + a^10 + a^12 + a^13 + a^15 + a^16 + a^17 + a^20 + O(a^21))*x^2 + (a^2 + a^5 + a^7 + a^9 + a^10 + a^12 + a^13 + a^14 + a^18 + O(a^21))*x + a + a^2 + a^3 + a^4 + a^5 + a^6 + a^9 + a^10 + a^13 + a^14 + a^17 + a^18 + a^19 + a^20 + O(a^21) of Eisenstein Extension of 2-adic Field with capped relative precision 5 in a defined by (1 + O(2^5))*x^4 + (2 + O(2^6))*x^3 + (2 + O(2^6))*x^2 + (2 + 2^2 + 2^3 + 2^4 + 2^5 + O(2^6))*x + 2 + O(2^6)
            sage: g(b)
            O(pi^64)
            sage: f(M(a))
            O(pi^69)

        Totally ramified over totally ramified::

            sage: K = Qp(2,5)
            sage: R.<x> = K[]
            sage: f = x^2 + 4*x + 8
            sage: L.<a> = K.extension(f); L
            Totally ramified extension in a defined by (1 + O(2^5))*x^2 + (2^2 + O(2^7))*x + 2^3 + O(2^8) of 2-adic Field with capped relative precision 5
            sage: R.<x> = L[]
            sage: g= x^2 + a^2*x + a^3
            sage: M.<b> = L.extension(g); M
            Totally ramified extension in b defined by (1 + O(pi^10))*x^2 + (pi^6 + O(pi^13))*x + pi^9 + pi^11 + pi^12 + pi^13 + O(pi^16) of Totally ramified extension in a defined by (1 + O(2^5))*x^2 + (2^2 + O(2^7))*x + 2^3 + O(2^8) of 2-adic Field with capped relative precision 5
            sage: M.implementation_ring()
             Eisenstein extension in x defined by (1 + O(pi^5))*x^2 + (pi^2 + O(pi^6))*x + pi + pi^3 + pi^4 + pi^5 + O(pi^6) of Totally ramified extension in a defined by (1 + O(2^5))*x^2 + (2^2 + O(2^7))*x + 2^3 + O(2^8) of 2-adic Field with capped relative precision 5
            sage: g(b)
            O(pi^19)
            sage: f(M(a))
            O(pi^26)

        """
        base = self.base_ring()
        modulus = self._poly

        from factory import GenericExtensionFactory
        if GenericExtensionFactory.is_eisenstein(modulus):
            raise ValueError("modulus must not be Eisenstein")
        if not base.is_field():
            raise NotImplementedError("currently only implemented over fields")

        from padic_valuation import pAdicValuation
        v = pAdicValuation(base)
        is_totally_ramified, ramification_steps = v.is_totally_ramified(modulus, include_steps=True, assume_squarefree=True)
        assert is_totally_ramified, "MacLane approximants terminated at: %s"%ramification_steps
        #TODO: why is this true
        assert any([v(v.phi()).denominator() == modulus.degree() for v in ramification_steps])

        # find a product of keys which gives a uniformizer
        slopes = [v(v.phi()) for v in ramification_steps]
        keys = [v.phi() for v in ramification_steps]
        numerators = [(slope.numerator()*modulus.degree()//slope.denominator(), key) for slope,key in zip(slopes,keys)]
        numerators.append((-modulus.degree(),base.uniformizer()**-1))
        bfs = {0:[]}
        while not 1 in bfs:
            for onum in bfs.keys():
                for num, key in numerators:
                    nnum = onum+num
                    if nnum not in bfs or len(bfs[onum])+1 < len(bfs[nnum]):
                        bfs[nnum] = bfs[onum]+[key]

        # a uniformizer and its minpoly
        from sage.rings.polynomial.polynomial_quotient_ring import PolynomialQuotientRing_field
        uniformizer = PolynomialQuotientRing_field(modulus.parent(), modulus, (modulus.variable_name()+'bar',)).one()
        for key in bfs[1]:
            uniformizer*=key
        epoly = uniformizer.minpoly()

        assert epoly.degree() == modulus.degree(), epoly
        assert GenericExtensionFactory.is_eisenstein(epoly), epoly

        self.__check.append(lambda: GenericExtensionFactory.krasner_check(epoly, names=epoly.parent().variable_names()))
        epoly = epoly.map_coefficients(lambda c:c.lift_to_precision())

        # now we reduced to the case of an Eisenstein extension; solve that
        # case recursively and combine the pieces
        implementation_ring = base.extension(epoly,names=epoly.parent().variable_names(), check=False)

        # TODO: is this actually an isomorphism? Or do we have to do something
        # about the fact that we lifted the polynomials to higher precision?

        # to go the other way, we send the generator of this ring to any root
        # in the implementation ring (is there a better way?)
        image_of_gen = modulus.change_ring(implementation_ring).any_root()
        to_implementation_ring = self._polynomial_ring.hom([image_of_gen])

        # to get from the Eisenstein extension back to this ring, we note that
        # the uniformizer from above is the uniformizer in the Eisenstein
        # extension (can we get more precision here?)
        from_implementation_ring = implementation_ring.hom([uniformizer.lift()(self._polynomial_ring.gen())])

        return implementation_ring, from_implementation_ring, to_implementation_ring

    def __implementation_ring_unramified_over_base(self):
        """
        Helper method for :meth:`__implementation_ring`` if ``modulus``
        generates an unramified extension (but the reduction of ``modulus`` is
        not irreducible).

        Input and output are the same as in :meth:`__implementation_ring`.

        ALGORITHM:

        ``base`` is an Eisenstein extension of a `p`-adic ground ring; since
        unramified extensions are uniquely determined by their degree, we
        create a new unramified extension of the appropriate degree, and put
        the original Eisenstein extension on top of that extension.

        TESTS::

            sage: K = Qp(5)
            sage: R.<u> = K[]
            sage: L.<u> = K.extension(u^2 + 5*u + 25); L
            Unramified extension in u defined by (1 + O(5^20))*u^2 + (5 + O(5^21))*u + 5^2 + O(5^22) of 5-adic Field with capped relative precision 20

        """
        base = self.base_ring()
        modulus = self._poly

        assert base is base.ground_ring_of_tower()

        from sage.rings.all import GF, ZZ
        unram_name = "u%s"%modulus.degree()
        unramified_modulus = GF(base.prime()**modulus.degree(), conway=True, prefix="u").modulus().change_ring(ZZ).change_ring(base.ground_ring_of_tower()).change_variable_name(unram_name)
        implementation_ring = base.extension(unramified_modulus, names=unramified_modulus.parent().variable_names(), check=False)

        # TODO: think about precision issues in this isomorphism

        from sage.categories.rings import Rings
        from sage.categories.homset import Hom
        from sage.categories.morphism import SetMorphism
        gen_in_implementation_ring = modulus.change_ring(implementation_ring).any_root()
        to_implementation_ring = SetMorphism(Hom(self._polynomial_ring, implementation_ring, Rings()), lambda f: f(gen_in_implementation_ring))

        # sadly, one has to do some linear algebra to get the morphism from the
        # implementation ring back to self. The algorithm here writes the
        # unramified generator of implementation_ring as a linear combination
        # of the image of the uniformizer and the unramified generator of self
        basis = [ self._polynomial_ring.gen()**i for i in range(modulus.degree()) ]
        from sage.matrix.all import matrix
        A = matrix([ to_implementation_ring(b).vector() for b in basis ])
        from sage.modules.free_module_element import vector
        x = A.solve_right(vector(implementation_ring.gen().vector(base)))
        unramified_gen_in_self = sum([b*c for b,c in zip(basis,x)])

        from_implementation_ring = implementation_ring.hom([unramified_gen_in_self])

        return implementation_ring, from_implementation_ring, to_implementation_ring

    def __implementation_ring_unramified_over_simple_eisenstein(self):
        """
        Helper method for :meth:`__implementation_ring`` if ``modulus``
        generates an unramified extension.

        Input and output are the same as in :meth:`__implementation_ring`.

        ALGORITHM:

        ``base`` is an Eisenstein extension of a `p`-adic ground ring; since
        unramified extensions are uniquely determined by their degree, we
        create a new unramified extension of the appropriate degree, and put
        the original Eisenstein extension on top of that extension.

        TESTS::

            sage: K = Qp(2,5)
            sage: R.<a> = K[]
            sage: f = a^2 + 2*a + 2
            sage: L.<a> = K.extension(f)
            sage: R.<u> = L[]
            sage: g = u^2 + u + 1
            sage: M.<u> = L.extension(g); M
            Unramified extension in u defined by (1 + O(a^10))*u^2 + (1 + O(a^10))*u + 1 + O(a^10) of Eisenstein Extension of 2-adic Field with capped relative precision 5 in a defined by (1 + O(2^5))*a^2 + (2 + O(2^6))*a + 2 + O(2^6)
            sage: M.implementation_ring()
            Eisenstein extension in pi2 defined by (1 + O(2^5))*pi2^2 + (2 + O(2^6))*pi2 + 2 + O(2^6) of Unramified Extension in u2 defined by (1 + O(2^5))*u2^2 + (1 + O(2^5))*u2 + 1 + O(2^5) of 2-adic Field with capped relative precision 5
            sage: f(M(a)).is_zero()
            True

        """
        base = self.base_ring()
        modulus = self._poly

        assert base.base() is base.ground_ring_of_tower()

        from sage.rings.all import GF, ZZ
        unram_name = "u%s"%modulus.degree()
        unramified_modulus = GF(base.prime()**modulus.degree(),conway=True,prefix='z').modulus().change_ring(ZZ).change_ring(base.ground_ring_of_tower()).change_variable_name(unram_name)
        unramified_base = base.ground_ring_of_tower().extension(unramified_modulus, names=unramified_modulus.parent().variable_names())

        epoly = base.modulus().change_ring(unramified_base)
        ram_name = "pi%s"%epoly.degree()
        epoly = epoly.change_variable_name(ram_name)

        from factory import GenericExtensionFactory
        self.__check.append(lambda: GenericExtensionFactory.krasner_check(epoly, names=epoly.parent().variable_names()))
        epoly = epoly.map_coefficients(lambda c:c.lift_to_precision())

        implementation_ring = unramified_base.extension(epoly, names=epoly.parent().variable_names(), check=False)

        # TODO: think about precision issues in this isomorphism

        from sage.categories.rings import Rings
        from sage.categories.homset import Hom
        from sage.categories.morphism import SetMorphism
        base_to_implementation_ring = base.hom([implementation_ring.gen()])
        gen_in_implementation_ring = modulus.map_coefficients(base_to_implementation_ring).any_root()
        to_implementation_ring = SetMorphism(Hom(self._polynomial_ring, implementation_ring, Rings()), lambda f: f.map_coefficients(base_to_implementation_ring)(gen_in_implementation_ring))

        # sadly, one has to do some linear algebra to get the morphism from the
        # implementation ring back to self. The algorithm here writes the
        # unramified generator of implementation_ring as a linear combination
        # of the image of the uniformizer and the unramified generator of self
        basis = [ self._polynomial_ring.gen()**i * base.gen()**j for i in range(modulus.degree()) for j in range(base.degree()) ]
        from sage.matrix.all import matrix
        A = matrix([ to_implementation_ring(b).vector(implementation_ring.ground_ring_of_tower()) for b in basis ])
        from sage.modules.free_module_element import vector
        x = A.solve_right(vector(implementation_ring(implementation_ring.base().gen()).vector(implementation_ring.ground_ring_of_tower())))
        unramified_gen_in_self = sum([b*c for b,c in zip(basis,x)])

        from_implementation_ring = implementation_ring.hom([self._polynomial_ring(base.gen())], implementation_ring.base().hom([unramified_gen_in_self]))

        return implementation_ring, from_implementation_ring, to_implementation_ring

    def __implementation_ring_unramified_over_eisenstein_over_simple_unramified(self):
        """
        Helper method for :meth:`__implementation_ring` which handles
        unramified extensions of Eisenstein extensions of unramified extensions
        of `p`-adic base rings.

        Input and output are the same as in :meth:`__implementation_ring`.

        NOTE: This is very similar to :meth:`__implementation_ring_unramified_over_simple_eisenstein`.

        TESTS::

            sage: K = Qp(2,5)
            sage: R.<u> = K[]
            sage: f = u^2 + u + 1
            sage: L.<u> = K.extension(f)
            sage: R.<a> = L[]
            sage: g = a^2 - 2
            sage: M.<a> = L.extension(g)
            sage: R.<v> = M[]
            sage: h = v^2 + u*v + u
            sage: N.<v> = M.extension(h); N
            Unramified extension in v defined by (1 + O(a^10))*v^2 + (u_ + O(a^10))*v + u_ + O(a^10) of Eisenstein extension in a defined by (1 + O(2^5))*a^2 + 2 + 2^2 + 2^3 + 2^4 + 2^5 + O(2^6) of Unramified Extension in u defined by (1 + O(2^5))*u^2 + (1 + O(2^5))*u + 1 + O(2^5) of 2-adic Field with capped relative precision 5
            sage: N.implementation_ring()
            Eisenstein extension in pi2 defined by (1 + O(2^5))*pi2^2 + 2 + 2^2 + 2^3 + 2^4 + 2^5 + O(2^6) of Unramified Extension in u4 defined by (1 + O(2^5))*u4^4 + (1 + O(2^5))*u4 + 1 + O(2^5) of 2-adic Field with capped relative precision 5
            sage: f(N(u)).is_zero()
            True

        """
        base = self.base_ring()
        modulus = self._poly

        assert base.base().base() is base.ground_ring_of_tower()

        from sage.rings.all import GF, ZZ
        unram_name = "u%s"%(modulus.degree()*base.base().degree())
        unramified_modulus = GF(base.prime()**(modulus.degree()*base.base().degree()),conway=True,prefix="u").modulus().change_ring(ZZ).change_ring(base.ground_ring_of_tower()).change_variable_name(unram_name)
        unramified_base = base.ground_ring_of_tower().extension(unramified_modulus, names=(unram_name,))

        base_base_to_unramified_base = base.base().hom([base.base().modulus().change_ring(unramified_base).any_root()])
        epoly = base.modulus().map_coefficients(base_base_to_unramified_base)
        ram_name = "pi%s"%epoly.degree()
        epoly = epoly.change_variable_name(ram_name)

        from factory import GenericExtensionFactory
        self.__check.append(lambda: GenericExtensionFactory.krasner_check(epoly, names=epoly.parent().variable_names()))
        epoly = epoly.map_coefficients(lambda c:c.lift_to_precision())

        implementation_ring = unramified_base.extension(epoly, names=epoly.parent().variable_names())

        # TODO: think about precision issues in this isomorphism

        from sage.categories.rings import Rings
        from sage.categories.homset import Hom
        from sage.categories.morphism import SetMorphism
        base_to_implementation_ring = base.hom([implementation_ring.gen()], base_base_to_unramified_base)
        gen_in_implementation_ring = modulus.map_coefficients(base_to_implementation_ring).any_root()
        to_implementation_ring = SetMorphism(Hom(self._polynomial_ring, implementation_ring, Rings()), lambda f: f.map_coefficients(base_to_implementation_ring)(gen_in_implementation_ring))

        # sadly, one has to do some linear algebra to get the morphism from the
        # implementation ring back to self. The algorithm here writes the
        # unramified generator of implementation_ring as a linear combination
        # of the image of the uniformizer and the unramified generator of self
        basis = [ self._polynomial_ring.gen()**i * base.gen()**j * base.base().gen()**k for i in range(modulus.degree()) for j in range(base.degree()) for k in range(base.base().degree()) ]
        from sage.matrix.all import matrix
        A = matrix([ to_implementation_ring(b).vector(implementation_ring.ground_ring_of_tower()) for b in basis ])
        from sage.modules.free_module_element import vector
        x = A.solve_right(vector(implementation_ring(implementation_ring.base().gen()).vector(implementation_ring.ground_ring_of_tower())))
        unramified_gen_in_self = sum([b*c for b,c in zip(basis,x)])

        from_implementation_ring = implementation_ring.hom([self._polynomial_ring(base.gen())], implementation_ring.base().hom([unramified_gen_in_self]))

        return implementation_ring, from_implementation_ring, to_implementation_ring

    def __implementation_ring_general(self):
        """
        Helper method for :meth:`__implementation_ring` if ``modulus`` has an
        unramified and a totally ramified part.

        Input and output are the same as in :meth:`__implementation_ring`.

        ALGORITHM:

        we extend ``base`` with the unramified part of ``modulus``; the factors
        of ``modulus`` then define totally ramified extensions, handled by
        :meth:`__implementation_ring_totally_ramified`.

        TESTS::

            sage: K = Qp(2,5)
            sage: R.<t> = K[]
            sage: f = t^4 + 2*t^3 + 2*t^2 + 4*t + 4
            sage: L.<t> = K.extension(f); L # long time
            General extension in t defined by (1 + O(2^5))*t^4 + (2 + O(2^6))*t^3 + (2 + O(2^6))*t^2 + (2^2 + O(2^7))*t + (2^2 + O(2^7)) of 2-adic Field with capped relative precision 5
            sage: L.implementation_ring() # long time
            Eisenstein extension in t defined by (1 + O(2^5))*t^2 + ((x + 1)*2 + O(2^6))*t + x*2 + O(2^6) of Unramified Extension in x defined by (1 + O(2^5))*x^2 + (1 + O(2^5))*x + (1 + O(2^5)) of 2-adic Field with capped relative precision 5

        """
        base = self.base_ring()
        modulus = self._poly

        # determine the unramified part of modulus
        v = base.valuation().mac_lane_approximants(modulus, assume_squarefree=True)
        assert len(v)==1
        v = v[0]
        unram_degree = v.F()
        assert unram_degree != 1
        unram_name = "u%s"%unram_degree
        from sage.rings.all import GF, ZZ
        unramified_modulus = GF(len(base.residue_field())**v.F(),conway=True,prefix='q').modulus().change_ring(ZZ).change_ring(base).factor()
        assert all([e==1 and f.degree()==unram_degree for f,e in unramified_modulus])
        unramified_modulus = unramified_modulus[0][0]
        unramified_modulus.change_variable_name(unram_name)
        unramified_modulus = unramified_modulus.map_coefficients(lambda c:c.lift_to_precision())

        unram_part = base.extension(unramified_modulus, names=unramified_modulus.parent().variable_names())

        totally_ramified_modulus = modulus.change_ring(unram_part).factor()
        assert all([e==1 and f.degree()==modulus.degree()/unram_degree for f,e in totally_ramified_modulus])
        totally_ramified_modulus = totally_ramified_modulus[0][0]
        ram_name = "pi%s"%totally_ramified_modulus.degree()
        totally_ramified_modulus = totally_ramified_modulus.change_variable_name(ram_name)
        # we must not lift_to_precision the totally_ramified_modulus since no Krasner check has been performed yet

        implementation_ring = unram_part.extension(totally_ramified_modulus, names=totally_ramified_modulus.parent().variable_names())

        # TODO: figure out the precision in these isomorphisms

        to_implementation_ring = self._polynomial_ring.hom([implementation_ring.gen()])

        basis = [ self._polynomial_ring.gen()**i for i in range(modulus.degree()) ]
        from sage.matrix.all import matrix
        A = matrix([ to_implementation_ring(b).vector(base) for b in basis ])
        from sage.modules.free_module_element import vector
        x = A.solve_right(vector(implementation_ring(unram_part.gen()).vector(base)))
        unramified_gen_in_self = sum([b*c for b,c in zip(basis,x)])

        from_implementation_ring = implementation_ring.hom([self._polynomial_ring.gen()], unram_part.hom([unramified_gen_in_self]))

        return implementation_ring, from_implementation_ring, to_implementation_ring

    @cached_method
    def to_implementation_ring(self):
        from sage.categories.morphism import SetMorphism
        from sage.categories.homset import Hom
        return SetMorphism(Hom(self, self.implementation_ring(), self.category()), lambda f: f._element)

    @cached_method
    def from_implementation_ring(self):
        from sage.categories.morphism import SetMorphism
        from sage.categories.homset import Hom
        return SetMorphism(Hom(self.implementation_ring(), self, self.category()), lambda f: self(self._from_implementation_ring()(f).list()))

    def _repr_(self):
        """
        Returns a print representation of this extension.

        """
        type = "General"
        if self.is_trivial():
            type = "Trivial"
        elif self.is_eisenstein():
            type = "Eisenstein"
        elif self.is_unramified():
            type = "Unramified"
        elif self.is_totally_ramified():
            type = "Totally ramified"
        return "%s extension in %s defined by %s of %s"%(type, self.variable_name(), self.defining_polynomial(), self.ground_ring())

    def is_trivial(self):
        return self._poly.degree() == 1

    @cached_method
    def is_eisenstein(self):
        from sage.rings.padics.factory import GenericExtensionFactory
        return GenericExtensionFactory.is_eisenstein(self._poly)

    @cached_method
    def is_unramified(self):
        from sage.rings.padics.factory import GenericExtensionFactory
        if GenericExtensionFactory.is_unramified(self._poly):
            return True
        # a polynomial which is not irreducible in irreduction can still
        # generate an unramified extension, mac lane approximants can be used
        # to check whether the polynomial actually generates an unramified
        # extension
        return self._poly.base_ring().valuation().is_unramified(self._poly)

    @cached_method
    def is_totally_ramified(self):
        from sage.rings.padics.factory import GenericExtensionFactory
        return GenericExtensionFactory.is_totally_ramified(self._poly)

    def ramification_index(self):
        """
        Return the absolute ramification index of ``self``, i.e., the valuation
        of ``p`` in ``self``.

        """
        return self.implementation_ring().ramification_index()

    def degree(self):
        """
        Returns the degree of this ring over its base ring.

        OUTPUT:

        A positive integer, the degree of the defining polynomial.

        """
        return self.defining_polynomial().degree()

    def gen(self, n=0):
        """
        Returns a generator for self as an extension of its ground ring.

        """
        if n == 0:
            return self([self.base_ring().zero(), self.base_ring().one()])
        raise IndexError, "only one generator"

    def gens(self):
        """
        Returns a list of generators of self.

        """
        return [self.gen(0)]

    def inertia_subring(self):
        """
        Returns the inertia subring of ``self``.

        """
        return self.implementation_ring().inertia_subring()

    def residue_class_field(self):
        """
        Returns the residue class field.

        """
        return self.implementation_ring().residue_class_field()

    def prime(self):
        """
        Returns the characteristic of the residue field.

        """
        return self._prime

    def uniformizer(self):
        ret = self(None)
        ret._element = self.implementation_ring().uniformizer()
        return ret

    def _uniformizer_print(self):
        return None # not used

    def _ram_name(self):
        if self._printer._ram_name() is not None:
            return self._printer._ram_name()
        elif self.gen() == self.uniformizer():
            return self.variable_name()
        elif self.base_ring().gen() == self.uniformizer():
            return self.base_ring().variable_name()
        elif self.base_ring().uniformizer() == self.uniformizer():
            return self.base_ring()._ram_name()
        else:
            return "pi"

    def _unram_name(self):
        if self._printer._unram_name() is not None:
            return self._printer._unram_name()
        else:
            return "u_"

    def _isomorphic_ring(self):
        implementation_ring = self.implementation_ring()
        if implementation_ring._isomorphic_ring()[0] is implementation_ring:
            return implementation_ring, self.from_implementation_ring(), self.to_implementation_ring()

        ret, from_ret, to_ret = implementation_ring._isomorphic_ring()
        return ret, self.from_implementation_ring()*from_ret, to_ret*self.to_implementation_ring()

    def _check(self):
        while len(self.__check):
            self.__check[-1]()
            self.__check.pop()
