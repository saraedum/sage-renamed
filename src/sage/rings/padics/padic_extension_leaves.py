"""
p-Adic Extension Leaves

The final classes for extensions of Zp and Qp (ie classes that are not
just designed to be inherited from).

AUTHORS:

- David Roe
"""
from __future__ import absolute_import

#*****************************************************************************
#       Copyright (C) 2008 David Roe <roed.math@gmail.com>
#                          William Stein <wstein@gmail.com>
#
#  Distributed under the terms of the GNU General Public License (GPL)
#  as published by the Free Software Foundation; either version 2 of
#  the License, or (at your option) any later version.
#
#                  http://www.gnu.org/licenses/
#*****************************************************************************

from sage.rings.integer_ring import ZZ
from sage.rings.rational_field import QQ
from sage.rings.finite_rings.integer_mod_ring import Zmod
from .pow_computer_ext import PowComputer_ext_maker
from .pow_computer_flint import PowComputer_flint_maker
from sage.libs.ntl.ntl_ZZ_pX import ntl_ZZ_pX

from .unramified_extension_generic import UnramifiedExtensionGeneric
from .eisenstein_extension_generic import EisensteinExtensionGeneric
#from padic_general_extension_generic import pAdicGeneralExtensionGeneric
from .two_step_extension_generic import TwoStepExtensionGeneric
from .general_extension_generic import GeneralExtensionGeneric

from .generic_nodes import pAdicCappedRelativeRingGeneric, \
                          pAdicCappedRelativeFieldGeneric, \
                          pAdicCappedAbsoluteRingGeneric, \
                          pAdicFixedModRingGeneric

from .padic_ZZ_pX_FM_element import pAdicZZpXFMElement
from .padic_ZZ_pX_CR_element import pAdicZZpXCRElement
from .padic_ZZ_pX_CA_element import pAdicZZpXCAElement
from .qadic_flint_CR import qAdicCappedRelativeElement
from .qadic_flint_CA import qAdicCappedAbsoluteElement
from .qadic_flint_FM import qAdicFixedModElement

def _make_integral_poly(prepoly, p, prec):
    """
    Converts a defining polynomial into one with integral coefficients.

    INPUTS:

    - ``prepoly`` - a univariate polynomial or symbolic expression

    - ``p`` -- a prime

    - ``prec`` -- the precision

    EXAMPLES::

        sage: from sage.rings.padics.padic_extension_leaves import _make_integral_poly
        sage: R.<x> = QQ[]
        sage: f = _make_integral_poly(x^2 - 2, 5, 3); f
        x^2 - 2
        sage: f.parent()
        Univariate Polynomial Ring in x over Integer Ring
        sage: f = _make_integral_poly(x^2 - 2/7, 5, 3); f
        x^2 + 89
        sage: f.parent()
        Univariate Polynomial Ring in x over Integer Ring
    """
    try:
        Zpoly = prepoly.change_ring(ZZ)
    except AttributeError:
        # should be a symoblic expression
        Zpoly = prepoly.polynomial(QQ)
    except (TypeError, ValueError):
        Zpoly = prepoly.change_ring(QQ)
    if Zpoly.base_ring() is not ZZ:
        Zpoly = Zpoly.change_ring(Zmod(p**prec)).change_ring(ZZ)
    return Zpoly


class UnramifiedExtensionRingCappedRelative(UnramifiedExtensionGeneric, pAdicCappedRelativeRingGeneric):
    """
    TESTS::

        sage: R.<a> = ZqCR(27,10000); R == loads(dumps(R))
        True
    """
    def __init__(self, prepoly, poly, prec, halt, print_mode, names, implementation="NTL"):
        """
        A capped relative representation of Zq.

        INPUT:

            - prepoly -- The original polynomial defining the
              extension.  This could be a polynomial with integer
              coefficients, for example, while poly has coefficients
              in Zp.

            - poly -- The polynomial with coefficients in
              self.base_ring() defining this extension.

            - prec -- The precision cap of this ring.

            - halt -- unused

            - print_mode -- A dictionary of print options.

            - names -- a 4-tuple, (variable_name, residue_name, unramified_subextension_variable_name, uniformizer_name)

        EXAMPLES::

            sage: R.<a> = ZqCR(27,10000); R #indirect doctest
            Unramified Extension in a defined by (1 + O(3^10000))*x^3 + (2 + O(3^10000))*x + 1 + O(3^10000) of 3-adic Ring with capped relative precision 10000

            sage: R.<a> = ZqCR(next_prime(10^30)^3, 3); R.prime()
            1000000000000000000000000000057
        """
        # Currently doesn't support polynomials with non-integral coefficients
        self._shift_seed = None
        self._pre_poly = prepoly
        self._implementation = implementation

        if implementation == 'NTL':
            ntl_poly = ntl_ZZ_pX([a.lift() for a in poly.list()], poly.base_ring().prime()**prec)
            if prec <= 30:
                self.prime_pow = PowComputer_ext_maker(poly.base_ring().prime(), prec, prec, prec, False, ntl_poly, "small", "u")
            else:
                self.prime_pow = PowComputer_ext_maker(poly.base_ring().prime(), 30, prec, prec, False, ntl_poly, "big", "u")
            element_class = pAdicZZpXCRElement
        elif implementation == "FLINT":
            Zpoly = _make_integral_poly(prepoly, poly.base_ring().prime(), prec)
            cache_limit = min(prec, 30)
            self.prime_pow = PowComputer_flint_maker(poly.base_ring().prime(), cache_limit, prec, prec, False, Zpoly, prec_type='capped-rel')
            element_class = qAdicCappedRelativeElement
        else:
            raise ValueError("unknown implementation `%s`"%implementation)
        UnramifiedExtensionGeneric.__init__(self, poly, prec, print_mode, names, element_class)
        if implementation != 'NTL':
            from .qadic_flint_CR import pAdicCoercion_ZZ_CR, pAdicConvert_QQ_CR
            self.register_coercion(pAdicCoercion_ZZ_CR(self))
            self.register_coercion(pAdicConvert_QQ_CR(self))

class UnramifiedExtensionFieldCappedRelative(UnramifiedExtensionGeneric, pAdicCappedRelativeFieldGeneric):
    """
    TESTS::

        sage: R.<a> = QqCR(27,10000); R == loads(dumps(R))
        True
    """
    def __init__(self, prepoly, poly, prec, halt, print_mode, names, implementation="NTL"):
        """
        A representation of Qq.

        INPUT:

            - prepoly -- The original polynomial defining the
              extension.  This could be a polynomial with integer
              coefficients, for example, while poly has coefficients
              in Qp.

            - poly -- The polynomial with coefficients in
              self.base_ring() defining this extension.

            - prec -- The precision cap of this ring.

            - halt -- unused

            - print_mode -- A dictionary of print options.

            - names -- a 4-tuple, (variable_name, residue_name, unramified_subextension_variable_name, uniformizer_name)

        EXAMPLES::

            sage: R.<a> = Qq(27,10000); R #indirect doctest
            Unramified Extension in a defined by (1 + O(3^10000))*x^3 + (2 + O(3^10000))*x + 1 + O(3^10000) of 3-adic Field with capped relative precision 10000

            sage: R.<a> = Qq(next_prime(10^30)^3, 3); R.prime()
            1000000000000000000000000000057
        """
        self._shift_seed = None
        self._pre_poly = prepoly
        self._implementation = implementation

        if implementation == 'NTL':
            ntl_poly = ntl_ZZ_pX([a.lift() for a in poly.list()], poly.base_ring().prime()**prec)
            if prec <= 30:
                self.prime_pow = PowComputer_ext_maker(poly.base_ring().prime(), prec, prec, prec, True, ntl_poly, "small", "u")
            else:
                self.prime_pow = PowComputer_ext_maker(poly.base_ring().prime(), 30, prec, prec, True, ntl_poly, "big", "u")
            element_class = pAdicZZpXCRElement
        elif implementation == "FLINT":
            Zpoly = _make_integral_poly(prepoly, poly.base_ring().prime(), prec)
            cache_limit = min(prec, 30)
            self.prime_pow = PowComputer_flint_maker(poly.base_ring().prime(), cache_limit, prec, prec, True, Zpoly, prec_type='capped-rel')
            element_class = qAdicCappedRelativeElement
        else:
            raise ValueError("unknown implementation `%s`"%implementation)

        UnramifiedExtensionGeneric.__init__(self, poly, prec, print_mode, names, element_class)
        if implementation == 'FLINT':
            from .qadic_flint_CR import pAdicCoercion_ZZ_CR, pAdicCoercion_QQ_CR
            self.register_coercion(pAdicCoercion_ZZ_CR(self))
            self.register_coercion(pAdicCoercion_QQ_CR(self))

#class UnramifiedExtensionRingLazy(UnramifiedExtensionGeneric, pAdicLazyRingGeneric):
#    def __init__(self, poly, prec, halt, print_mode, names):
#        UnramifiedExtensionGeneric.__init__(self, poly, prec, print_mode, names, UnramifiedExtensionLazyElement)
#        pAdicLazyRingGeneric.__init__(self, poly.base_ring().prime(), prec, print_mode, names, halt)

#class UnramifiedExtensionFieldLazy(UnramifiedExtensionGeneric, pAdicLazyFieldGeneric):
#    def __init__(self, poly, prec, halt, print_mode, names):
#        UnramifiedExtensionGeneric.__init__(self, poly, prec, print_mode, names, UnramifiedExtensionLazyElement)
#        pAdicLazyFieldGeneric.__init__(self, poly.base_ring().prime(), prec, print_mode, names, halt)

class UnramifiedExtensionRingCappedAbsolute(UnramifiedExtensionGeneric, pAdicCappedAbsoluteRingGeneric):
    """
    TESTS::

        sage: R.<a> = ZqCA(27,10000); R == loads(dumps(R))
        True
    """
    def __init__(self, prepoly, poly, prec, halt, print_mode, names, implementation="NTL"):
        """
        A capped absolute representation of Zq.

        INPUT:

            - prepoly -- The original polynomial defining the
              extension.  This could be a polynomial with integer
              coefficients, for example, while poly has coefficients
              in Zp.

            - poly -- The polynomial with coefficients in
              self.base_ring() defining this extension.

            - prec -- The precision cap of this ring.

            - halt -- unused

            - print_mode -- A dictionary of print options.

            - names -- a 4-tuple, (variable_name, residue_name, unramified_subextension_variable_name, uniformizer_name)

        EXAMPLES::

            sage: R.<a> = ZqCA(27,10000); R #indirect doctest
            Unramified Extension in a defined by (1 + O(3^10000))*x^3 + (O(3^10000))*x^2 + (2 + O(3^10000))*x + (1 + O(3^10000)) of 3-adic Ring with capped absolute precision 10000

            sage: R.<a> = ZqCA(next_prime(10^30)^3, 3); R.prime()
            1000000000000000000000000000057
        """
         # Currently doesn't support polynomials with non-integral coefficients
        self._shift_seed = None
        self._pre_poly = prepoly

        self._implementation = implementation

        if implementation == 'NTL':
            ntl_poly = ntl_ZZ_pX([a.lift() for a in poly.list()], poly.base_ring().prime()**prec)
            if prec <= 30:
                self.prime_pow = PowComputer_ext_maker(poly.base_ring().prime(), prec, prec, prec, False, ntl_poly, "small", "u")
            else:
                self.prime_pow = PowComputer_ext_maker(poly.base_ring().prime(), 30, prec, prec, False, ntl_poly, "big", "u")
            element_class = pAdicZZpXCAElement
        elif implementation == "FLINT":
            Zpoly = _make_integral_poly(prepoly, poly.base_ring().prime(), prec)
            cache_limit = min(prec, 30)
            self.prime_pow = PowComputer_flint_maker(poly.base_ring().prime(), cache_limit, prec, prec, False, Zpoly, prec_type='capped-abs')
            element_class = qAdicCappedAbsoluteElement
        else:
            raise ValueError("unknown implementation `%s`"%implementation)

        UnramifiedExtensionGeneric.__init__(self, poly, prec, print_mode, names, element_class)
        if implementation != 'NTL':
            from .qadic_flint_CA import pAdicCoercion_ZZ_CA, pAdicConvert_QQ_CA
            self.register_coercion(pAdicCoercion_ZZ_CA(self))
            self.register_conversion(pAdicConvert_QQ_CA(self))

class UnramifiedExtensionRingFixedMod(UnramifiedExtensionGeneric, pAdicFixedModRingGeneric):
    """
    TESTS::

        sage: R.<a> = ZqFM(27,10000); R == loads(dumps(R))
        True
    """
    def __init__(self, prepoly, poly, prec, halt, print_mode, names, implementation="NTL"):
        """
        A fixed modulus representation of Zq.

        INPUT:

            - prepoly -- The original polynomial defining the
              extension.  This could be a polynomial with integer
              coefficients, for example, while poly has coefficients
              in Qp.

            - poly -- The polynomial with coefficients in
              self.base_ring() defining this extension.

            - prec -- The precision cap of this ring.

            - halt -- unused

            - print_mode -- A dictionary of print options.

            - names -- a 4-tuple, (variable_name, residue_name, unramified_subextension_variable_name, uniformizer_name)

        EXAMPLES::

            sage: R.<a> = ZqFM(27,10000); R #indirect doctest
            Unramified Extension in a defined by (1 + O(3^10000))*x^3 + (O(3^10000))*x^2 + (2 + O(3^10000))*x + (1 + O(3^10000)) of 3-adic Ring of fixed modulus 3^10000

            sage: R.<a> = ZqFM(next_prime(10^30)^3, 3); R.prime()
            1000000000000000000000000000057
        """
        self._shift_seed = None
        self._pre_poly = prepoly
        if implementation == 'NTL':
            ntl_poly = ntl_ZZ_pX([a.lift() for a in poly.list()], poly.base_ring().prime()**prec)
            self.prime_pow = PowComputer_ext_maker(poly.base_ring().prime(), max(min(prec - 1, 30), 1), prec, prec, False, ntl_poly, "FM", "u")
            element_class = pAdicZZpXFMElement
        elif implementation == "FLINT":
            Zpoly = _make_integral_poly(prepoly, poly.base_ring().prime(), prec)
            cache_limit = 0 # prevents caching
            self.prime_pow = PowComputer_flint_maker(poly.base_ring().prime(), cache_limit, prec, prec, False, Zpoly, prec_type='fixed-mod')
            element_class = qAdicFixedModElement
        else:
            raise ValueError("unknown implementation `%s`"%implementation)

        UnramifiedExtensionGeneric.__init__(self, poly, prec, print_mode, names, element_class)
        if implementation != 'NTL':
            from .qadic_flint_FM import pAdicCoercion_ZZ_FM, pAdicConvert_QQ_FM
            self.register_coercion(pAdicCoercion_ZZ_FM(self))
            self.register_conversion(pAdicConvert_QQ_FM(self))

class EisensteinExtensionRingCappedRelative(EisensteinExtensionGeneric, pAdicCappedRelativeRingGeneric):
    """
    TESTS::

        sage: R = Zp(3, 10000, print_pos=False); S.<x> = ZZ[]; f = x^3 + 9*x - 3
        sage: W.<w> = R.ext(f); W == loads(dumps(W))
        True
    """
    def __init__(self, prepoly, poly, prec, halt, print_mode, names, implementation="NTL"):
        """
        A capped relative representation of an eisenstein extension of Zp.

        INPUT:

            - prepoly -- The original polynomial defining the
              extension.  This could be a polynomial with integer
              coefficients, for example, while poly has coefficients
              in Zp.

            - poly -- The polynomial with coefficients in
              self.base_ring() defining this extension.

            - prec -- The precision cap of this ring.

            - halt -- unused

            - print_mode -- A dictionary of print options.

            - names -- a 4-tuple, (variable_name, residue_name, unramified_subextension_variable_name, uniformizer_name)

        EXAMPLES::

            sage: R = Zp(3, 10000, print_pos=False); S.<x> = ZZ[]; f = x^3 + 9*x - 3
            sage: W.<w> = R.ext(f); W #indirect doctest
            Eisenstein Extension of 3-adic Ring with capped relative precision 10000 in w defined by (1 + O(3^10000))*x^3 + (3^2 + O(3^10001))*x - 3 + O(3^10001)
            sage: W.precision_cap()
            30000

            sage: R.<p> = Zp(next_prime(10^30), 3, print_pos=False); S.<x> = ZZ[]; f = x^3 + p^2*x - p
            sage: W.<w> = R.ext(f); W.prime()
            1000000000000000000000000000057
            sage: W.precision_cap()
            9
        """
        if implementation != "NTL":
            raise ValueError("unknown implementation")

        unram_prec = (prec + poly.degree() - 1) // poly.degree()
        ntl_poly = ntl_ZZ_pX([a.lift() for a in poly.list()], poly.base_ring().prime()**unram_prec)
        shift_seed = self._compute_shift_seed(prepoly, poly.base_ring())
        shift_poly = ntl_ZZ_pX([a.lift() for a in shift_seed.list()], shift_seed.base_ring().prime()**unram_prec)
        if unram_prec <= 30:
            self.prime_pow = PowComputer_ext_maker(poly.base_ring().prime(), unram_prec, unram_prec, prec, False, ntl_poly, "small", "e", shift_poly)
        else:
            self.prime_pow = PowComputer_ext_maker(poly.base_ring().prime(), 30, unram_prec, prec, False, ntl_poly, "big", "e", shift_poly)
        self._shift_seed = shift_seed
        self._pre_poly = prepoly
        self._implementation = implementation
        EisensteinExtensionGeneric.__init__(self, poly, prec, print_mode, names, pAdicZZpXCRElement)

class EisensteinExtensionFieldCappedRelative(EisensteinExtensionGeneric, pAdicCappedRelativeFieldGeneric):
    """
    TESTS::

        sage: R = Qp(3, 10000, print_pos=False); S.<x> = ZZ[]; f = x^3 + 9*x - 3
        sage: W.<w> = R.ext(f); W == loads(dumps(W))
        True
    """
    def __init__(self, prepoly, poly, prec, halt, print_mode, names, implementation="NTL"):
        """
        A capped relative representation of an eisenstein extension of Qp.

        INPUT:

            - prepoly -- The original polynomial defining the
              extension.  This could be a polynomial with integer
              coefficients, for example, while poly has coefficients
              in Qp.

            - poly -- The polynomial with coefficients in
              self.base_ring() defining this extension.

            - prec -- The precision cap of this ring.

            - halt -- unused

            - print_mode -- A dictionary of print options.

            - names -- a 4-tuple, (variable_name, residue_name, unramified_subextension_variable_name, uniformizer_name)

        EXAMPLES::

            sage: R = Qp(3, 10000, print_pos=False); S.<x> = ZZ[]; f = x^3 + 9*x - 3
            sage: W.<w> = R.ext(f); W #indirect doctest
            Eisenstein Extension of 3-adic Field with capped relative precision 10000 in w defined by (1 + O(3^10000))*x^3 + (3^2 + O(3^10001))*x - 3 + O(3^10001)
            sage: W.precision_cap()
            30000

            sage: R.<p> = Qp(next_prime(10^30), 3, print_pos=False); S.<x> = ZZ[]; f = x^3 + p^2*x - p
            sage: W.<w> = R.ext(f); W.prime()
            1000000000000000000000000000057
            sage: W.precision_cap()
            9
        """
        if implementation != "NTL":
            raise ValueError("unknown implementation `%s`"%implementation)
        # Currently doesn't support polynomials with non-integral coefficients
        unram_prec = (prec + poly.degree() - 1) // poly.degree()
        ntl_poly = ntl_ZZ_pX([a.lift() for a in poly.list()], poly.base_ring().prime()**unram_prec)
        shift_seed = self._compute_shift_seed(prepoly, poly.base_ring())
        shift_poly = ntl_ZZ_pX([a.lift() for a in shift_seed.list()], shift_seed.base_ring().prime()**unram_prec)
        if unram_prec <= 30:
            self.prime_pow = PowComputer_ext_maker(poly.base_ring().prime(), unram_prec, unram_prec, prec, True, ntl_poly, "small", "e", shift_poly)
        else:
            self.prime_pow = PowComputer_ext_maker(poly.base_ring().prime(), 30, unram_prec, prec, True, ntl_poly, "big", "e", shift_poly)
        self._shift_seed = shift_seed
        self._pre_poly = prepoly
        self._implementation = implementation
        EisensteinExtensionGeneric.__init__(self, poly, prec, print_mode, names, pAdicZZpXCRElement)

class EisensteinExtensionRingCappedAbsolute(EisensteinExtensionGeneric, pAdicCappedAbsoluteRingGeneric):
    """
    TESTS::

        sage: R = ZpCA(3, 10000, print_pos=False); S.<x> = ZZ[]; f = x^3 + 9*x - 3
        sage: W.<w> = R.ext(f); W == loads(dumps(W))
        True
    """
    def __init__(self, prepoly, poly, prec, halt, print_mode, names, implementation="NTL"):
        """
        A capped absolute representation of an eisenstein extension of Zp.

        INPUT:

            - prepoly -- The original polynomial defining the
              extension.  This could be a polynomial with integer
              coefficients, for example, while poly has coefficients
              in Zp.

            - poly -- The polynomial with coefficients in
              self.base_ring() defining this extension.

            - prec -- The precision cap of this ring.

            - halt -- unused

            - print_mode -- A dictionary of print options.

            - names -- a 4-tuple, (variable_name, residue_name, unramified_subextension_variable_name, uniformizer_name)

        EXAMPLES::

            sage: R = ZpCA(3, 10000, print_pos=False); S.<x> = ZZ[]; f = x^3 + 9*x - 3
            sage: W.<w> = R.ext(f); W
            Eisenstein Extension of 3-adic Ring with capped absolute precision 10000 in w defined by (1 + O(3^10000))*x^3 + (O(3^10000))*x^2 + (3^2 + O(3^10000))*x + (-3 + O(3^10000))
            sage: W.precision_cap()
            30000

            sage: R.<p> = ZpCA(next_prime(10^30), 3, print_pos=False); S.<x> = ZZ[]; f = x^3 + p^2*x - p
            sage: W.<w> = R.ext(f); W.prime()
            1000000000000000000000000000057
            sage: W.precision_cap()
            9
        """
        if implementation != "NTL":
            raise ValueError("unknown implementation `%s`"%implementation)

        unram_prec = (prec + poly.degree() - 1) // poly.degree()
        ntl_poly = ntl_ZZ_pX([a.lift() for a in poly.list()], poly.base_ring().prime()**unram_prec)
        shift_seed = self._compute_shift_seed(prepoly, poly.base_ring())
        shift_poly = ntl_ZZ_pX([a.lift() for a in shift_seed.list()], shift_seed.base_ring().prime()**unram_prec)
        if unram_prec <= 30:
            self.prime_pow = PowComputer_ext_maker(poly.base_ring().prime(), unram_prec, unram_prec, prec, False, ntl_poly, "small", "e", shift_poly)
        else:
            self.prime_pow = PowComputer_ext_maker(poly.base_ring().prime(), 30, unram_prec, prec, False, ntl_poly, "big", "e", shift_poly)
        self._shift_seed = shift_seed
        self._pre_poly = prepoly
        self._implementation = implementation
        EisensteinExtensionGeneric.__init__(self, poly, prec, print_mode, names, pAdicZZpXCAElement)

class EisensteinExtensionRingFixedMod(EisensteinExtensionGeneric, pAdicFixedModRingGeneric):
    """
    TESTS::

        sage: R = ZpFM(3, 10000, print_pos=False); S.<x> = ZZ[]; f = x^3 + 9*x - 3
        sage: W.<w> = R.ext(f); W == loads(dumps(W))
        True
    """
    def __init__(self, prepoly, poly, prec, halt, print_mode, names, implementation="NTL"):
        """
        A fixed modulus representation of an eisenstein extension of Zp.

        INPUT:

            - prepoly -- The original polynomial defining the
              extension.  This could be a polynomial with integer
              coefficients, for example, while poly has coefficients
              in Zp.

            - poly -- The polynomial with coefficients in
              self.base_ring() defining this extension.

            - prec -- The precision cap of this ring.

            - halt -- unused

            - print_mode -- A dictionary of print options.

            - names -- a 4-tuple, (variable_name, residue_name, unramified_subextension_variable_name, uniformizer_name)

        EXAMPLES::

            sage: R = ZpFM(3, 10000, print_pos=False); S.<x> = ZZ[]; f = x^3 + 9*x - 3
            sage: W.<w> = R.ext(f); W #indirect doctest
            Eisenstein Extension of 3-adic Ring of fixed modulus 3^10000 in w defined by (1 + O(3^10000))*x^3 + (O(3^10000))*x^2 + (3^2 + O(3^10000))*x + (-3 + 3^10000 + O(3^10000))
            sage: W.precision_cap()
            30000

            sage: R.<p> = ZpFM(next_prime(10^30), 3, print_pos=False); S.<x> = ZZ[]; f = x^3 + p^2*x - p
            sage: W.<w> = R.ext(f); W.prime()
            1000000000000000000000000000057
            sage: W.precision_cap()
            9
        """
        if implementation != "NTL":
            raise ValueError("unknown implementation `%s`"%implementation)

        unram_prec = (prec + poly.degree() - 1) // poly.degree()
        ntl_poly = ntl_ZZ_pX([a.lift() for a in poly.list()], poly.base_ring().prime()**unram_prec)
        shift_seed = self._compute_shift_seed(prepoly, poly.base_ring())
        shift_poly = ntl_ZZ_pX([a.lift() for a in shift_seed.list()], shift_seed.base_ring().prime()**unram_prec)
        #print poly.base_ring().prime(), prec, poly.degree(), ntl_poly
        # deal with prec not a multiple of e better.
        self.prime_pow = PowComputer_ext_maker(poly.base_ring().prime(), max(min(unram_prec - 1, 30), 1), unram_prec, prec, False, ntl_poly, "FM", "e", shift_poly)
        self._shift_seed = shift_seed
        self._pre_poly = prepoly
        self._implementation = implementation
        EisensteinExtensionGeneric.__init__(self, poly, prec, print_mode, names, pAdicZZpXFMElement)

class TwoStepExtensionRingCappedRelative(TwoStepExtensionGeneric, pAdicCappedRelativeRingGeneric):
    def __init__(self, prepoly, poly, prec, halt, print_mode, names, implementation):
        if implementation is not None:
            raise ValueError("implementation must be None")
        TwoStepExtensionGeneric.__init__(self, poly, prec, print_mode, names, pAdicLaurentCRElement)

class TwoStepExtensionFieldCappedRelative(TwoStepExtensionGeneric, pAdicCappedRelativeFieldGeneric):
    def __init__(self, prepoly, poly, prec, halt, print_mode, names, implementation):
        if implementation is not None:
            raise ValueError("implementation must be None")
        TwoStepExtensionGeneric.__init__(self, poly, prec, print_mode, names, pAdicLaurentCRElement)

class TwoStepExtensionRingCappedAbsolute(TwoStepExtensionGeneric, pAdicCappedAbsoluteRingGeneric):
    def __init__(self, prepoly, poly, prec, halt, print_mode, names, implementation):
        if implementation is not None:
            raise ValueError("implementation must be None")
        TwoStepExtensionGeneric.__init__(self, poly, prec, print_mode, names, pAdicLaurentCAElement)

class TwoStepExtensionRingFixedMod(TwoStepExtensionGeneric, pAdicFixedModRingGeneric):
    def __init__(self, prepoly, poly, prec, halt, print_mode, names, implementation):
        if implementation is not None:
            raise ValueError("implementation must be None")
        TwoStepExtensionGeneric.__init__(self, poly, prec, print_mode, names, pAdicLaurentFMElement)

class GeneralExtensionFieldCappedRelative(GeneralExtensionGeneric, pAdicCappedRelativeFieldGeneric):
    def __init__(self, prepoly, poly, prec, halt, print_mode, names, implementation):
        if implementation is not None:
            raise ValueError("implementation must be None")
        self.prime_pow = None # general extensions do not use the pow_computer yet
        GeneralExtensionGeneric.__init__(self, prepoly, poly, prec, print_mode, names, pAdicGeneralCRElement)

class GeneralExtensionRingCappedRelative(GeneralExtensionGeneric, pAdicCappedRelativeRingGeneric):
    def __init__(self, prepoly, poly, prec, halt, print_mode, names, implementation):
        if implementation is not None:
            raise ValueError("implementation must be None")
        self.prime_pow = None # general extensions do not use the pow_computer yet
        GeneralExtensionGeneric.__init__(self, prepoly, poly, prec, print_mode, names, pAdicGeneralCRElement)

class GeneralExtensionRingCappedAbsolute(GeneralExtensionGeneric, pAdicCappedAbsoluteRingGeneric):
    def __init__(self, prepoly, poly, prec, halt, print_mode, names, implementation):
        if implementation is not None:
            raise ValueError("implementation must be None")
        self.prime_pow = None # general extensions do not use the pow_computer yet
        GeneralExtensionGeneric.__init__(self, prepoly, poly, prec, print_mode, names, pAdicGeneralCAElement)

class GeneralExtensionRingFixedMod(GeneralExtensionGeneric, pAdicFixedModRingGeneric):
    def __init__(self, prepoly, poly, prec, halt, print_mode, names, implementation):
        if implementation is not None:
            raise ValueError("implementation must be None")
        self.prime_pow = None # general extensions do not use the pow_computer yet
        GeneralExtensionGeneric.__init__(self, prepoly, poly, prec, print_mode, names, pAdicGeneralFMElement)
