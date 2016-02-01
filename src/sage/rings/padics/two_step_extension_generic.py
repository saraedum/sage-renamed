"""
Two step extensions of `\mathbb{Q}_p` and `\mathbb{Z}_p`

This file implements the shared functionality for two step extensions, i.e., Eisenstein extensions of unramified extensions.

TODO: talk about this being like a GeneralExtensionGeneric but considered as
single extension, i.e., self.base() is the actual padic ground ring.

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

from padic_extension_generic import pAdicExtensionGeneric
from sage.rings.finite_rings.finite_field_constructor import GF

class TwoStepExtensionGeneric(pAdicExtensionGeneric):
    """
    An Eisenstein extension of an unramified extension of `\mathbb{Q}_p` or `\mathbb{Z}_p`.
    """
    def __init__(self, poly, prec, print_mode, names, element_class):
        """
        Initializes ``self``.

        INPUT:

            - ``poly`` -- an Eisenstein polynomial over an unramified simple
              extension of a `p`-adic base ring.

            - ``prec`` -- a positive integer, the precision to use when
              representing elements in ``self``

            - ``print_mode`` -- a dictionary of print options

            - ``names`` -- a tuple ``(a)`` where ``a`` is the variable of the
              Eisenstein step of the extension

            - ``element_class`` -- the class which implements the elements of
              ``self``

        """
        if names[0] == poly.parent().base().variable_name():
            raise ValueError("names of the generators should be different.") # eventually remove this, but it makes debugging much easier for the time being

        self.prime_pow = None

        self._inertia_subring = poly.base_ring()
        pAdicExtensionGeneric.__init__(self, poly.base_ring().base(), poly, prec, print_mode, (poly.base_ring().variable_name(),names[0]), element_class)
        self._epoly = poly.change_variable_name(names[0])
        self._prime = poly.base_ring().prime()
        self._res_field = self._inertia_subring.residue_field()
        self._populate_coercion_lists_(coerce_list=[self._inertia_subring],element_constructor=element_class)

    def _isomorphic_ring(self):
        ret = self._inertia_subring.extension(self._epoly,names=self._names[1])
        return ret, ret.hom([self.gen(1)],base=ret.base().hom([self.gen(0)])), self.hom([self._inertia_subring.gen(),ret.gen()])

    def hom(self, im_gens, base=None):
        from sage.categories.rings import Rings
        if im_gens in Rings():
            if base is not None:
                raise ValueError("base must be None if im_gens is a ring")
            if not im_gens.has_coerce_map_from(self):
                raise ValueError("must coerce into im_gens")
            return im_gens.coerce_map_from(self)

        if len(im_gens)!=2:
            raise ValueError("must specify image of the two generators")

        from sage.structure.element import get_coercion_model
        codomain = get_coercion_model().common_parent(*im_gens)

        from sage.categories.morphism import SetMorphism
        from sage.categories.homset import Hom
        from sage.rings.polynomial.polynomial_ring_constructor import PolynomialRing
        return SetMorphism(Hom(self, codomain, Rings()), lambda f:f.polynomial()(im_gens))

    def _repr_(self):
        """
        Returns a print representation of this extension.

        """
        return "Two step extension in %s defined by %s and %s of %s"%(self.variable_names(), self._epoly,  self._inertia_subring.modulus(), self.base())

    def ramification_index(self):
        """
        Return the absolute ramification index of ``self``, i.e., the valuation
        of ``p`` in ``self``.

        EXAMPLES::

            sage: K = ZpCR(3,10)
            sage: R.<u> = K[]
            sage: L.<u> = K.extension(u^2 + 3*u + 4)
            sage: R.<a> = L[]
            sage: M = ZpTwoStepExtensionFactory(L, a^3 - 9*u*a^2 + 3*u, ram_name='a'); a = M.uniformizer(); u = M(u)
            sage: M.ramification_index()
            3

        """
        return self._epoly.degree()

    def _uniformizer_print(self):
        return self.variable_names()[1]

    def _unram_print(self):
        return self.inertia_subring().variable_name()

    def degree(self):
        """
        Returns the degree of this ring over the padic base ring.

        OUTPUT:

        A positive integer, the degree of the Eisenstein step times the degree
        of the unramified step.

        EXAMPLES::

            sage: K = ZpCR(3,10)
            sage: R.<u> = K[]
            sage: L.<u> = K.extension(u^2 + 3*u + 4)
            sage: R.<a> = L[]
            sage: M = ZpTwoStepExtensionFactory(L, a^3 - 9*u*a^2 + 3*u, ram_name='a'); a = M.uniformizer(); u = M(u)
            sage: M.degree()
            6

        """
        return self._epoly.degree() * self._inertia_subring.degree()

    def gen(self, n=0):
        """
        Returns a generator for self as an extension of its ground ring.

        EXAMPLES::

            sage: K = ZpCR(3,10)
            sage: R.<u> = K[]
            sage: L.<u> = K.extension(u^2 + 3*u + 4)
            sage: R.<a> = L[]
            sage: M = ZpTwoStepExtensionFactory(L, a^3 - 9*u*a^2 + 3*u, ram_name='a'); a = M.uniformizer(); u = M(u)
            sage: M.gen()
            u + O(a^30)
            sage: M.gen(1)
            a + O(a^31)

        """
        if n == 0:
            return self([self.residue_field().gen()] + [self.residue_field().zero()]*(self.precision_cap()-1))
        if n == 1:
            return self([self.residue_field().zero(),self.residue_field().one()] + [self.residue_field().zero()]*(self.precision_cap()-1))
        raise IndexError, "only two generators"

    def gens(self):
        """
        Returns a list of generators of self.

        OUTPUT:

        Returns a list consisting of the generator of the Eisenstein extension
        followed by the generator of the unramified extension.

        EXAMPLES::

            sage: K = ZpCR(3,10)
            sage: R.<u> = K[]
            sage: L.<u> = K.extension(u^2 + 3*u + 4)
            sage: R.<a> = L[]
            sage: M = ZpTwoStepExtensionFactory(L, a^3 - 9*u*a^2 + 3*u, ram_name='a'); a = M.uniformizer(); u = M(u)
            sage: M.gens()
            [u + O(a^30), a + O(a^31)]

        """
        return [self.gen(0),self.gen(1)]

    def inertia_subring(self):
        """
        Returns the inertia subring of ``self``.

        EXAMPLES::

            sage: K = ZpCR(3,10)
            sage: R.<u> = K[]
            sage: L.<u> = K.extension(u^2 + 3*u + 4)
            sage: R.<a> = L[]
            sage: M = ZpTwoStepExtensionFactory(L, a^3 - 9*u*a^2 + 3*u, ram_name='a'); a = M.uniformizer(); u = M(u)
            sage: M.inertia_subring()
            Unramified Extension in u defined by (1 + O(3^10))*u^2 + (3 + O(3^10))*u + 1 + 3 + O(3^10) of 3-adic Ring with capped relative precision 10

        """
        return self._inertia_subring

    def residue_class_field(self):
        """
        Returns the residue class field.

        EXAMPLES::

            sage: K = ZpCR(3,10)
            sage: R.<u> = K[]
            sage: L.<u> = K.extension(u^2 + 3*u + 4)
            sage: R.<a> = L[]
            sage: M = ZpTwoStepExtensionFactory(L, a^3 - 9*u*a^2 + 3*u, ram_name='a'); a = M.uniformizer(); u = M(u)
            sage: M.residue_class_field()
            Finite Field in u0 of size 3^2

        """
        return self._res_field

    def prime(self):
        """
        Returns the characteristic of the residue field.

        EXAMPLES::

            sage: K = ZpCR(3,10)
            sage: R.<u> = K[]
            sage: L.<u> = K.extension(u^2 + 3*u + 4)
            sage: R.<a> = L[]
            sage: M = ZpTwoStepExtensionFactory(L, a^3 - 9*u*a^2 + 3*u, ram_name='a'); a = M.uniformizer(); u = M(u)
            sage: M.prime()
            3

        """
        return self._prime

    def uniformizer(self):
        return self.gen(1)

    def uniformizer_pow(self, n):
        return self.uniformizer()**n
