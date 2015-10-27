"""
p-Adic Extension Generic

A common superclass for all extensions of Qp and Zp.

AUTHORS:

- David Roe
"""

#*****************************************************************************
#       Copyright (C) 2007-2013 David Roe <roed.math@gmail.com>
#                               William Stein <wstein@gmail.com>
#
#  Distributed under the terms of the GNU General Public License (GPL)
#  as published by the Free Software Foundation; either version 2 of
#  the License, or (at your option) any later version.
#
#                  http://www.gnu.org/licenses/
#*****************************************************************************

from padic_generic import pAdicGeneric
from padic_base_generic import pAdicBaseGeneric
from functools import reduce
from sage.rings.padics.precision_error import PrecisionError

class pAdicExtensionGeneric(pAdicGeneric):
    def __init__(self, base, poly, prec, print_mode, names, element_class):
        """
        Initialization

        EXAMPLES::

            sage: R = Zp(5,5)
            sage: S.<x> = R[]
            sage: f = x^5 + 75*x^3 - 15*x^2 +125*x - 5
            sage: W.<w> = R.ext(f) #indirect doctest
        """
        #type checking done in factory
        self._given_poly = poly
        pAdicGeneric.__init__(self, base, base.prime(), prec, print_mode, names, element_class)
        self._populate_coercion_lists_(coerce_list=[base], element_constructor=element_class)

#     def __reduce__(self):
#         """
#         For pickling.

#         This function is provided because prime_pow needs to be set before _printer, so the standard unpickling fails.
#         """
#         from sage.rings.padics.factory import ExtensionFactory
#         return ExtensionFactory, (self.base_ring(), self._pre_poly, self.precision_cap(), self.print_mode(), None, self.variable_name())

    def _coerce_map_from_(self, R):
        """
        Returns True if there is a coercion map from R to self.

        EXAMPLES::

            sage: R = Zp(5); S.<x> = ZZ[]; f = x^5 + 25*x - 5; W.<w> = R.ext(f)
            sage: L = W.fraction_field()
            sage: w + L(w) #indirect doctest
            2*w + O(w^101)
            sage: w + R(5,2)
            w + w^5 + O(w^10)
        """
        # Far more functionality needs to be added here later.
        if isinstance(R, pAdicExtensionGeneric) and R.fraction_field() is self:
            if self._implementation == 'NTL':
                return True
            elif R._prec_type() == 'capped-abs':
                from sage.rings.padics.qadic_flint_CA import pAdicCoercion_CA_frac_field as coerce_map
            elif R._prec_type() == 'capped-rel':
                from sage.rings.padics.qadic_flint_CR import pAdicCoercion_CR_frac_field as coerce_map
            return coerce_map(R, self)

    def __cmp__(self, other):
        """
        Returns 0 if self == other, and 1 or -1 otherwise.

        We consider two p-adic rings or fields to be equal if they are equal mathematically, and also have the same precision cap and printing parameters.

        EXAMPLES::

            sage: R.<a> = Qq(27)
            sage: S.<a> = Qq(27,print_mode='val-unit')
            sage: R == S
            False
            sage: S.<a> = Qq(27,type='capped-rel')
            sage: R == S
            True
            sage: R is S
            True
        """
        c = cmp(type(self), type(other))
        if c != 0:
            return c
        groundcmp = self.ground_ring().__cmp__(other.ground_ring())
        if groundcmp != 0:
            return groundcmp
        c = cmp(self.defining_polynomial(), other.defining_polynomial()) # TODO: this is not correct
        if c != 0:
            return c
        c = cmp(self.precision_cap(), other.precision_cap())
        if c != 0:
            return c
        return self._printer.cmp_modes(other._printer)

    def __hash__(self):
        raise TypeError

    def _cache_key(self):
        from sage.misc.cachefunc import _cache_key
        return _cache_key(self.base()), self.defining_polynomial()._cache_key()

    #def absolute_discriminant(self):
    #    raise NotImplementedError

    #def discriminant(self):
    #    raise NotImplementedError

    #def is_abelian(self):
    #    raise NotImplementedError

    #def is_normal(self):
    #    raise NotImplementedError

    def degree(self):
        """
        Returns the degree of this extension.

        EXAMPLES::

            sage: R.<a> = Zq(125); R.degree()
            3
            sage: R = Zp(5); S.<x> = ZZ[]; f = x^5 - 25*x^3 + 5; W.<w> = R.ext(f)
            sage: W.degree()
            5
        """
        return self._given_poly.degree()

    def defining_polynomial(self):
        """
        Returns the polynomial defining this extension.

        EXAMPLES::

            sage: R = Zp(5,5)
            sage: S.<x> = R[]
            sage: f = x^5 + 75*x^3 - 15*x^2 +125*x - 5
            sage: W.<w> = R.ext(f)
            sage: W.defining_polynomial()
            (1 + O(5^5))*x^5 + (3*5^2 + O(5^6))*x^3 + (2*5 + 4*5^2 + 4*5^3 + 4*5^4 + 4*5^5 + O(5^6))*x^2 + (5^3 + O(5^6))*x + 4*5 + 4*5^2 + 4*5^3 + 4*5^4 + 4*5^5 + O(5^6)

        """
        return self._given_poly

    def modulus(self):
        """
        Returns the polynomial defining this extension.

        EXAMPLES::

            sage: R = Zp(5,5)
            sage: S.<x> = R[]
            sage: f = x^5 + 75*x^3 - 15*x^2 +125*x - 5
            sage: W.<w> = R.ext(f)
            sage: W.modulus()
            (1 + O(5^5))*x^5 + (3*5^2 + O(5^6))*x^3 + (2*5 + 4*5^2 + 4*5^3 + 4*5^4 + 4*5^5 + O(5^6))*x^2 + (5^3 + O(5^6))*x + 4*5 + 4*5^2 + 4*5^3 + 4*5^4 + 4*5^5 + O(5^6)
        """
        return self._given_poly

    def ground_ring(self):
        """
        Returns the ring of which this ring is an extension.

        EXAMPLE::

            sage: R = Zp(5,5)
            sage: S.<x> = R[]
            sage: f = x^5 + 75*x^3 - 15*x^2 +125*x - 5
            sage: W.<w> = R.ext(f)
            sage: W.ground_ring()
            5-adic Ring with capped relative precision 5
        """
        if isinstance(self._given_poly,tuple):
            return self._given_poly[0].base_ring()
        else:
            return self._given_poly.base_ring()

    def ground_ring_of_tower(self):
        """
        Returns the p-adic base ring of which this is ultimately an
        extension.

        Currently this function is identical to ground_ring(), since
        relative extensions have not yet been implemented.

        EXAMPLES::

            sage: Qq(27,30,names='a').ground_ring_of_tower()
            3-adic Field with capped relative precision 30
        """
        if isinstance(self.ground_ring(), pAdicBaseGeneric):
            return self.ground_ring()
        else:
            return self.ground_ring().ground_ring_of_tower()

    #def is_isomorphic(self, ring):
    #    raise NotImplementedError

    def polynomial_ring(self):
        """
        Returns the polynomial ring of which this is a quotient.

        EXAMPLES::

            sage: Qq(27,30,names='a').polynomial_ring()
            Univariate Polynomial Ring in x over 3-adic Field with capped relative precision 30
        """
        return self._given_poly.parent()

    #def teichmuller(self, x, prec = None):
    #    if prec is None:
    #        prec = self.precision_cap()
    #    x = self(x, prec)
    #    if x.valuation() > 0:
    #        return self(0)
    #    q = self.residue_class_field().order()
    #    u = 1 / self(1 - q, prec)
    #    delta = u * (1 - x ** (q - 1))
    #    xnew = x - x*delta*(1 - q * delta)
    #    while x != xnew:
    #        x = xnew
    #        delta = u*(1-x**(q-1))
    #        xnew = x - x*delta*(1-q*delta)
    #    return x

    def fraction_field(self, print_mode=None):
        r"""
        Returns the fraction field of this extension, which is just
        the extension of base.fraction_field() determined by the
        same polynomial.

        INPUT:

        - print_mode -- a dictionary containing print options.
          Defaults to the same options as this ring.

        OUTPUT:

        - the fraction field of self.

        EXAMPLES::

            sage: U.<a> = Zq(17^4, 6, print_mode='val-unit', print_max_terse_terms=3)
            sage: U.fraction_field()
            Unramified Extension in a defined by (1 + O(17^6))*x^4 + (7 + O(17^6))*x^2 + (10 + O(17^6))*x + 3 + O(17^6) of 17-adic Field with capped relative precision 6
            sage: U.fraction_field({"pos":False}) == U.fraction_field()
            False
        """
        if self.is_field() and print_mode is None:
            return self
        print_mode = self._modified_print_mode(print_mode)
        ground_mode = print_mode.copy()
        # We don't want to confuse the ground ring with different names.
        ground_mode['ram_name'] = None
        ground_mode['unram_name'] = None
        K = self.ground_ring().fraction_field(ground_mode)
        #we don't want to set the print options due to the ground ring since
        #different extension fields (with different options) can share the same ground ring.
        if self.is_lazy():
            return K.extension(self._pre_poly, prec = self.precision_cap(), halt = self.halting_parameter(), res_name = self.residue_field().variable_name(), print_mode=print_mode, implementation=self._implementation)
        else:
            return K.extension(self._pre_poly, prec = self.precision_cap(), res_name = self.residue_field().variable_name(), print_mode=print_mode, implementation=self._implementation)

    def integer_ring(self, print_mode=None):
        r"""
        Returns the ring of integers of self, which is just the
        extension of base.integer_ring() determined by the same
        polynomial.

        INPUT:

            - print_mode -- a dictionary containing print options.
              Defaults to the same options as this ring.

        OUTPUT:

            - the ring of elements of self with nonnegative valuation.

        EXAMPLES::

            sage: U.<a> = Qq(17^4, 6, print_mode='val-unit', print_max_terse_terms=3)
            sage: U.integer_ring()
            Unramified Extension in a defined by (1 + O(17^6))*x^4 + (7 + O(17^6))*x^2 + (10 + O(17^6))*x + 3 + O(17^6) of 17-adic Ring with capped relative precision 6
            sage: U.fraction_field({"pos":False}) == U.fraction_field()
            False
        """
        #Currently does not support fields with non integral defining polynomials.  This should change when the padic_general_extension framework gets worked out.
        if not self.is_field() and print_mode is None:
            return self
        print_mode = self._modified_print_mode(print_mode)
        ground_mode = print_mode.copy()
        # We don't want to confuse the ground ring with different names.
        ground_mode['ram_name'] = None
        ground_mode['unram_name'] = None
        K = self.ground_ring().integer_ring(ground_mode)
        #we don't want to set the print options due to the ground ring since
        #different extension fields (with different options) can share the same ground ring.
        if self.is_lazy():
            return K.extension(self._pre_poly, prec = self.precision_cap(), halt = self.halting_parameter(), res_name = self.residue_field().variable_name(), print_mode=print_mode)
        else:
            return K.extension(self._pre_poly, prec = self.precision_cap(), res_name = self.residue_field().variable_name(), print_mode=print_mode)

    #def hasGNB(self):
    #    raise NotImplementedError

    def random_element(self):
        """
        Returns a random element of self.

        This is done by picking a random element of the ground ring
        self.degree() times, then treating those elements as
        coefficients of a polynomial in self.gen().

        EXAMPLES::

            sage: R.<a> = Zq(125, 5); R.random_element()
            (3*a^2 + 3*a + 3) + (a^2 + 4*a + 1)*5 + (3*a^2 + 4*a + 1)*5^2 + (2*a^2 + 3*a + 3)*5^3 + (4*a^2 + 3)*5^4 + O(5^5)
            sage: R = Zp(5,3); S.<x> = ZZ[]; f = x^5 + 25*x^2 - 5; W.<w> = R.ext(f)
            sage: W.random_element()
            4 + 3*w + w^2 + 4*w^3 + w^5 + 3*w^6 + w^7 + 4*w^10 + 2*w^12 + 4*w^13 + 3*w^14 + O(w^15)
        """
        return reduce(lambda x,y: x+y,
                      [self.ground_ring().random_element() * self.gen()**i for i in
                           range(self.modulus().degree())],
                      0)

    def hom(self, im_gens, base=None):
        from sage.categories.rings import Rings
        if im_gens in Rings():
            if base is not None:
                raise ValueError("base must be None if im_gens is a ring")
            if not im_gens.has_coerce_map_from(self):
                raise ValueError("%s does not define a coercion to %s"%(self,im_gens))
            return im_gens.coerce_map_from(self)

        if len(im_gens) != 1:
            raise ValueError("im_gens must be a list of length 1")

        codomain = im_gens[0].parent()

        if base is None:
            hom = lambda f: f.polynomial()(im_gens[0])
        else:
            hom = lambda f: f.polynomial().map_coefficients(base)(im_gens[0])

        from sage.categories.morphism import SetMorphism
        from sage.categories.homset import Hom
        return SetMorphism(Hom(self, codomain, Rings()), hom)

    #def unit_group(self):
    #    raise NotImplementedError

    #def unit_group_gens(self):
    #    raise NotImplementedError

    #def principal_unit_group(self):
    #    raise NotImplementedError

    #def zeta(self, n = None):
    #    raise NotImplementedError

    #def zeta_order(self):
    #    raise NotImplementedError

    ### def __factor_univariate_polynomial_squarefree_norm(self, f, base):
    ###     """
    ###     Given a polynomial ``f(x)``, finds a constant ``s`` in this ring such
    ###     that ``f(x+s)`` has squarefree norm.

    ###     INPUT:

    ###         - ``f`` -- a squarefree univariate polynomial defined over this
    ###           ring

    ###     OUTPUT:

    ###     A tuple ``s,g,N`` such that ``f(s-x)=g(x)`` and ``N`` being the norm of
    ###     ``g(x)``.

    ###     ..NOTE::

    ###         This is a helper method for :meth:`_factor_univariate_polynomial`.

    ###     ALGORITHM:

    ###     An ``s`` with the required properties must exist [Tra1976]. If it
    ###     doesn't then this can only happen because the computations don't
    ###     actually take place with full precision. A ``PrecisionError`` is raised
    ###     in such a case.

    ###     REFERENCES:

    ###     .. [Tra1976] Barry M. Trager, Algebraic factoring and rational function
    ###     integration, SYMSAC '76 Proceedings of the third ACM symposium on
    ###     Symbolic and algebraic computation, p. 219-226

    ###     AUTHORS:

    ###         - Julian Rueth (2012-10-28): initial version

    ###     EXAMPLES::

    ###         sage: K = Qp(3,5)
    ###         sage: R.<a> = K[]
    ###         sage: L.<a> = K.extension(a^2-3)
    ###         sage: R.<t> = L[]
    ###         sage: L._pAdicExtensionGeneric__factor_univariate_polynomial_squarefree_norm(t, L)
    ###         (1, (1 + O(a^10))*t + 2*a + 2*a^3 + 2*a^5 + 2*a^7 + 2*a^9 + O(a^11), (1 + O(3^5))*t^2 + (O(3^6))*t + (2*3 + 2*3^2 + 2*3^3 + 2*3^4 + 2*3^5 + O(3^6)))

    ###     """
    ###     max_attempts = ((f.degree() + 1)*self.degree())^2

    ###     for s in range(max_attempts):
    ###         #print "Attempt %s to find a squarefree norm..."%s
    ###         g = f(f.parent().gen() - s*self.gens()[-1])
    ###         assert g.is_squarefree()
    ###         N = self.__factor_univariate_polynomial_norm(g, base)
    ###         #print N.gcd(N.derivative())
    ###         if N.is_squarefree():
    ###             #print "Found squarefree norm."
    ###             return s,g,N

    ###     raise PrecisionError("insufficient precision to determine a shift which leads to a squarefree norm")

#    def _factor_univariate_polynomial(self, f):
#        """
#        Computes the factorization of ``f`` into irreducible polynomials.
#
#        INPUT:
#
#            - ``f`` -- a univariate polynomial defined over this ring
#
#        OUTPUT:
#
#        A factorization of ``f`` into irreducible factors over this ring
#
#        ALGORITHM:
#
#        Uses the algorithm described in [Tra1976] to factor univariate
#        polynomials over arbitrary finite field extensions. The algorithm
#        determines a factorization by looking at the gcd of ``f`` and factors
#        of its norm. This is not very efficient, since the norm of ``f`` has a
#        much larger degree than ``f``.
#
#        REFERENCES:
#
#        .. [Tra1976] Barry M. Trager, Algebraic factoring and rational function
#        integration, SYMSAC '76 Proceedings of the third ACM symposium on
#        Symbolic and algebraic computation, p. 219-226
#
#        ..SEEALSO ::
#
#            :meth:`sage.rings.polynomial.polynomial_element.Polynomial.factor`
#
#        EXAMPLES:
#
#        We factor several polynomials over Eisenstein extensions::
#
#            sage: K = Qp(3,3)
#            sage: R.<a> = K[]
#            sage: L.<a> = K.extension(a^2-3)
#            sage: R.<t> = L[]
#            sage: t.factor() # indirect doctest
#            (1 + O(a^6))*t
#            sage: (t+a).factor()
#            (1 + O(a^6))*t + a + O(a^7)
#            sage: (t^2 - 2).factor()
#            (1 + O(a^6))*t^2 + 1 + 2*a^2 + 2*a^4 + O(a^6)
#            sage: (t^2 - 2 - a).factor()
#            (1 + O(a^6))*t^2 + 1 + 2*a + 2*a^2 + 2*a^3 + 2*a^4 + 2*a^5 + O(a^6)
#
#        Sometimes, one has to increase the precision for the algorithm to work.
#        In these cases, the factorization can only be determined to lower
#        precision::
#
#            sage: (t^2 - 3).factor()
#            Traceback (most recent call last):
#            ...
#            PrecisionError: insufficient precision to determine a shift which leads to a squarefree norm
#            sage: K = Qp(3,10)
#            sage: R.<a> = K[]
#            sage: L.<a> = K.extension(a^2-3)
#            sage: R.<t> = L[]
#            sage: (t^2 - 3).factor() # the precision dropped to O(a^9)
#            ((1 + O(a^9))*t + a + O(a^9)) * ((1 + O(a^9))*t + 2*a + 2*a^3 + 2*a^5 + 2*a^7 + O(a^9))
#
#        Over unramified extensions::
#
#            sage: K = Qp(3,3)
#            sage: R.<u> = K[]
#            sage: L.<u> = K.extension(u^2 + u - 1)
#            sage: R.<t> = L[]
#            sage: t.factor()
#            (1 + O(3^3))*t
#            sage: (t + u).factor()
#            (1 + O(3^3))*t + u + O(3^3)
#            sage: ((t - u)*(t + u)).factor()
#            ((1 + O(3^3))*t + 2*u + 2*u*3 + 2*u*3^2 + O(3^3)) * ((1 + O(3^3))*t + u + O(3^3))
#            sage: (t^2 - 2).factor()
#            ((1 + O(3^3))*t + (2*u + 1) + (u + 2)*3 + u*3^2 + O(3^3)) * ((1 + O(3^3))*t + (u + 2) + u*3 + (u + 2)*3^2 + O(3^3))
#            sage: (t^2 - 2 - u).factor()
#             ((1 + O(3^3))*t + (u + 1) + O(3^3)) * ((1 + O(3^3))*t + (2*u + 2) + (2*u + 2)*3 + (2*u + 2)*3^2 + O(3^3))
#            sage: (t^2 + t).factor()
#            ((1 + O(3^3))*t + 1 + O(3^3)) * ((1 + O(3^3))*t)
#
#        """
#        from sage.misc.misc import prod
#        from sage.structure.factorization import Factorization
#
#        if f.degree() == 1:
#            return Factorization([(f,1)])
#
#        print "Trying to factor a polynomial of degree %s and relative precision %s over an extension of degree %s\nf=%s\nK=%s"%(f.degree(),min([c.precision_absolute()-c.valuation() for c in f.coeffs() if not c.is_zero()]),self.degree(),f,self)
#
#        lc = f.leading_coefficient()
#        f *= lc.inverse_of_unit()
#        assert f.leading_coefficient().is_one()
#
#        if not f.is_squarefree():
#            F = f.squarefree_decomposition()
#            assert len(F)!=1 or F[0][1]!=1
#            F *= lc
#            return prod([g.factor()**e if g.degree() else Factorization([(g,e)]) for g,e in F])
#
#        # Hensel lift
#        HF = f.map_coefficients(lambda c:c.residue(),self.residue_field()).factor()
#        #print HF
#        if len(HF) > 1:
#            print "Hensel lifting factors..."
#            g = HF[0][0]**HF[0][1]*HF.unit()
#            h = prod([HF[i][0]**HF[i][1] for i in range(1,len(HF))])
#            o,s,t = g.xgcd(h)
#            def lift(fbar):
#                return fbar.map_coefficients(lambda c:self(c).lift_to_precision(self.precision_cap()),self)
#            g = lift(g)
#            gd = g.degree()
#            h = lift(h)
#            hd = h.degree()
#            s = lift(s)
#            sd = s.degree()
#            t = lift(t)
#            td = t.degree()
#
#            prec = 1
#            while prec < self.precision_cap():
#                print "Now at precision %s/%s with degrees %s,%s,%s,%s/%s"%(prec,self.precision_cap(),g.degree(),h.degree(),s.degree(),t.degree(),f.degree())
#                prec = min(prec*2,self.precision_cap())
#
#                g = g.map_coefficients(lambda c:c.lift_to_precision(prec))
#                h = h.map_coefficients(lambda c:c.lift_to_precision(prec))
#                s = s.map_coefficients(lambda c:c.lift_to_precision(prec))
#                t = t.map_coefficients(lambda c:c.lift_to_precision(prec))
#
#                e = f-g*h
#
#                q,r = (s*e).quo_rem(h)
#                g = g + t*e + q*g
#                g = g.truncate(gd+1)
#                h = h + r
#                h = h.truncate(hd+1)
#                b = s*g + t*h - 1
#                c,d = (s*b).quo_rem(h)
#                s = s - d
#                s = s.truncate(sd+1)
#                t = t - t*b - c*g
#                t = t.truncate(td+1)
#
#                assert (f-g*h).map_coefficients(lambda c:c.add_bigoh(prec))==0,"Hensel lifting failed - %s should be equal to %s x %s mod pi^%s but its difference is %s"%(f,g,h,prec,e)
#
#            assert g*h==f
#            unit = lc*g.leading_coefficient()*h.leading_coefficient()
#            assert unit.is_unit()
#            g *= g.leading_coefficient().inverse_of_unit()
#            h *= h.leading_coefficient().inverse_of_unit()
#            assert g*h==f
#            ret = Factorization(list(g.factor()*h.factor()),unit=lc)
#            assert ret.prod() == f*lc
#            return ret
#
#        # montes level 1 (Newton polygon)
#        phi = HF[0][0].map_coefficients(lambda c:self(c).lift_to_precision(self.precision_cap()),self)
#        #print "Developing wrt",phi
#        a = []
#        q = f
#        while q.degree() >= phi.degree():
#            #print q
#            q, r = q.quo_rem(phi)
#            a.append(r)
#        a.append(q)
#        from sage.rings.infinity import infinity
#        ND = [min([c.valuation() for c in d.list()]) if len(d.list()) else infinity for d in a]
#
#        if ND[0]!=infinity:
#            NP = [(0,ND[0])]
#            while NP[-1][0] != len(ND)-1:
#                best = (len(ND)-1, (ND[-1]-NP[-1][1])/(len(ND)-1-NP[-1][0]))
#                for j in range(len(ND)-2,NP[-1][0],-1):
#                    if ND[j] is infinity:
#                        continue
#                    test = (ND[j]-NP[-1][1])/(j-NP[-1][0])
#                    if test<best[1]:
#                        best = j,test
#                NP.append((best[0],ND[best[0]]))
#            if len(NP)>2:
#                print "(Montes') Newton Lift would help for this polynomial... %s"%NP
#
#            # montes level 1 (residual polynomial)
#            #side_len = NP[1][0]+1
#            #slope = (NP[1][1]-NP[0][1])/(NP[1][0]-NP[0][0])
#            #res_poly = [(a[j]/self.gens()[-1]**ND[j]).map_coefficients(lambda x:x.residue(),self.residue_field()) if ND[j] == ND[0]+slope*j else self.residue_field().zero() for j in range(side_len)]
#            #res_poly = sum([c*HF[0][0]**i for i,c in enumerate(res_poly)])
#            #print res_poly.factor()
#
#        base = self.inertia_subring()
#        if base is self:
#            base = self.ground_ring_of_tower()
#
#        s,g,N = self.__factor_univariate_polynomial_squarefree_norm(f, base)
#        assert g.degree()==f.degree()
#        assert g.leading_coefficient().is_one()
#
#        assert N.gcd(g) == g
#        ## do we need this?
#        ## N = N.map_coefficients(lambda c:c.add_bigoh(N.gcd(N.derivative())[0].precision_absolute()))
#        ## assert N.gcd(g) == g
#
#        F = N.factor()
#        if F.prod() != N:
#            print "p-adic factorization failed for %s. Factors don't multiply to the original polynomial by an error of %s. Will reduce the precision of the factors until they give the right result."%(N,F.prod()-N)
#            F = list(F)
#            for prec in range(F[0][0][0].precision_absolute()-1,-1,-1):
#                for i in range(len(F)):
#                    F[i] = F[i][0].map_coefficients(lambda c:c.add_bigoh(prec)),F[i][1]
#                if prod([h**e for h,e in F]) == N:
#                    if prec != F[0][0][0].precision_absolute(): print "Decreased precision to %s"%prec
#                    break
#        F = list(F)
#        assert all(e==1 for _,e in F)
#
#        if len(F)==1:
#            #print "Norm is irreducible"
#            #print N
#            return Factorization([(f,1)],unit=lc)
#        assert all([h.leading_coefficient().is_one() for h,e in F]),"Factorization of norm %s produced a leading coefficient which is not one: %s"%(N,F)
#
#        #print "Norm factored into %s factors"%len(F)
#
#        for prec in range(F[0][0][0].precision_absolute(),-1,-1):
#            g = g.map_coefficients(lambda c:c.add_bigoh(prec))
#            ret = [ h.gcd(g) for h,e in F ]
#            degree_sum = sum([h.degree() for h in ret])
#            assert degree_sum <= g.degree()
#            if degree_sum==g.degree():
#                if prec != F[0][0][0].precision_absolute(): print "reduced precision to %s"%prec
#                assert prod(ret) == g,prod(ret)-g
#                break
#            assert N.gcd(g).degree()==g.degree()
#
#        ret = [ (h(g.parent().gen()+s*self.gens()[-1]),1) for h in ret if not h.is_one() ]
#        for prec in range(ret[0][0][0].precision_absolute(),-1,-1):
#            ret = [ (h.map_coefficients(lambda c:c.add_bigoh(prec)),e) for h,e in ret]
#            if prod([h for h,e in ret])==f:
#                if prec != ret[0][0][0].precision_absolute(): print "reduced precision to %s"%prec
#                break
#        ret = Factorization(ret,unit=lc)
#        assert ret.prod()==f*lc,"%s should be %s but it differs by %s"%(ret,f*lc,ret.prod()-f*lc)
#        return ret
#
#    def __factor_univariate_polynomial_norm(self, f, base):
#        r"""
#        Returns the norm of the polynomial ``f``.
#
#        INPUT:
#
#            - ``f`` -- a univariate polynomial defined over this ring
#
#        OUTPUT:
#
#        The norm of ``f`` over the p-adic ground ring `\ZZ_p` or `\QQ_p`
#        respectively. The norm of ``f`` is a univariate polynomial over the
#        p-adic ground ring. If this ring is generated by `\alpha` over the
#        ground ring, and ``f`` can be written as ``f(x,\alpha)`` with
#        coefficients in the ground ring, then the norm of ``f`` is given by
#        `\prod f(x,\alpha_i)` where the product runs over all conjugates of
#        `\alpha`.
#
#        ..NOTE::
#
#            This is a helper method for :meth:`_factor_univariate_polynomial`.
#
#        REFERENCES:
#
#            [Tra1976] Barry M. Trager, Algebraic factoring and rational
#            function integration, SYMSAC '76 Proceedings of the third ACM
#            symposium on Symbolic and algebraic computation, p. 219-226
#
#        AUTHORS:
#
#            - Julian Rueth (2012-10-28): initial version
#
#        EXAMPLES:
#
#        We compute a few norms in Eisenstein extensions::
#
#            sage: K = Qp(3,5)
#            sage: R.<a> = K[]
#            sage: L.<a> = K.extension(a^2 - 3)
#            sage: R.<t> = L[]
#            sage: L._pAdicExtensionGeneric__factor_univariate_polynomial_norm(t)
#            (1 + O(3^5))*t^2
#            sage: L._pAdicExtensionGeneric__factor_univariate_polynomial_norm(t - a)
#            (1 + O(3^5))*t^2 + (O(3^6))*t + (2*3 + 2*3^2 + 2*3^3 + 2*3^4 + 2*3^5 + O(3^6))
#
#        In unramified extensions::
#
#            sage: K = Qp(3,5)
#            sage: R.<u> = K[]
#            sage: L.<u> = K.extension(u^2+u-1)
#            sage: R.<t> = L[]
#            sage: L._pAdicExtensionGeneric__factor_univariate_polynomial_norm(t)
#            (1 + O(3^5))*t^2
#            sage: L._pAdicExtensionGeneric__factor_univariate_polynomial_norm(t - u)
#            (1 + O(3^5))*t^2 + (1 + O(3^5))*t + (2 + 2*3 + 2*3^2 + 2*3^3 + 2*3^4 + O(3^5))
#
#        """
#        if not f.base_ring() is self:
#            raise ValueError("polynomial not defined over this ring")
#        if not f.parent().ngens()==1:
#            raise ValueError("polynomial is not univariate")
#
#        parent = f.parent().change_ring(base)
#
#        if len(f.coeffs())==0:
#            return parent.zero()
#
#        return sum([ c.matrix(base)*parent.gen()**i for i,c in enumerate(f.coeffs()) ]).det()
