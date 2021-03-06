"""
p-Adic Generic Element

Elements of `p`-Adic Rings and Fields

AUTHORS:

- David Roe

- Genya Zaytman: documentation

- David Harvey: doctests

- Julian Rueth: fixes for exp() and log(), implemented gcd, xgcd

"""

#*****************************************************************************
#       Copyright (C) 2007-2013 David Roe <roed@math.harvard.edu>
#                     2007      William Stein <wstein@gmail.com>
#                     2013-2014 Julian Rueth <julian.rueth@gmail.com>
#
#  Distributed under the terms of the GNU General Public License (GPL)
#  as published by the Free Software Foundation; either version 2 of
#  the License, or (at your option) any later version.
#
#                  http://www.gnu.org/licenses/
#*****************************************************************************
from __future__ import absolute_import

from sage.ext.stdsage cimport PY_NEW
cimport sage.rings.padics.local_generic_element
from sage.libs.gmp.mpz cimport mpz_set_si
from sage.rings.padics.local_generic_element cimport LocalGenericElement
from sage.rings.padics.precision_error import PrecisionError
from sage.rings.rational cimport Rational
from sage.rings.integer cimport Integer
from sage.rings.infinity import infinity
from sage.structure.element import coerce_binop


cdef long maxordp = (1L << (sizeof(long) * 8 - 2)) - 1

cdef class pAdicGenericElement(LocalGenericElement):
    cpdef int _cmp_(left, right) except -2:
        """
        First compare valuations, then compare normalized
        residue of unit part.

        EXAMPLES::

            sage: R = Zp(19, 5,'capped-rel','series'); K = Qp(19, 5, 'capped-rel', 'series')
            sage: a = R(2); a
            2 + O(19^5)
            sage: b = R(3); b
            3 + O(19^5)
            sage: a < b
            True
            sage: a = K(2); a
            2 + O(19^5)
            sage: b = K(3); b
            3 + O(19^5)
            sage: a < b
            True

        ::

            sage: R = Zp(5); a = R(5, 6); b = R(5 + 5^6, 8)
            sage: a == b #indirect doctest
            True

        ::

            sage: R = Zp(5)
            sage: a = R(17)
            sage: b = R(21)
            sage: a == b
            False
            sage: a < b
            True

        ::

            sage: R = ZpCA(5)
            sage: a = R(17)
            sage: b = R(21)
            sage: a == b
            False
            sage: a < b
            True

        ::

            sage: R = ZpFM(5)
            sage: a = R(17)
            sage: b = R(21)
            sage: a == b
            False
            sage: a < b
            True
        """
        m = min(left.precision_absolute(), right.precision_absolute())
        x_ordp = left.valuation()
        if x_ordp >= m :
            x_ordp = infinity
        y_ordp = right.valuation()
        if y_ordp >= m :
            y_ordp = infinity
        if x_ordp < y_ordp:
            return -1
        elif x_ordp > y_ordp:
            return 1
        else:  # equal ordp
            if x_ordp is infinity:
                return 0 # since both are zero
            else:
                return (<pAdicGenericElement>left.unit_part())._cmp_units(right.unit_part())

    cdef int _cmp_units(left, pAdicGenericElement right) except -2:
        raise NotImplementedError

    cdef int _set_from_Integer(self, Integer x, absprec, relprec) except -1:
        raise NotImplementedError
    cdef int _set_from_mpz(self, mpz_t x) except -1:
        raise NotImplementedError
    cdef int _set_from_mpz_rel(self, mpz_t x, long relprec) except -1:
        raise NotImplementedError
    cdef int _set_from_mpz_abs(self, mpz_t value, long absprec) except -1:
        raise NotImplementedError
    cdef int _set_from_mpz_both(self, mpz_t x, long absprec, long relprec) except -1:
        raise NotImplementedError

    cdef int _set_from_Rational(self, Rational x, absprec, relprec) except -1:
        raise NotImplementedError
    cdef int _set_from_mpq(self, mpq_t x) except -1:
        raise NotImplementedError
    cdef int _set_from_mpq_rel(self, mpq_t x, long relprec) except -1:
        raise NotImplementedError
    cdef int _set_from_mpq_abs(self, mpq_t value, long absprec) except -1:
        raise NotImplementedError
    cdef int _set_from_mpq_both(self, mpq_t x, long absprec, long relprec) except -1:
        raise NotImplementedError

    cdef int _pshift_self(self, long shift) except -1:
        raise NotImplementedError

    cdef int _set_inexact_zero(self, long absprec) except -1:
        raise NotImplementedError
    cdef int _set_exact_zero(self) except -1:
        raise TypeError("this type of p-adic does not support exact zeros")

    cpdef bint _is_exact_zero(self) except -1:
        """
        Returns True if self is exactly zero.  Since
        non-capped-relative elements cannot be exact, this function
        always returns False.

        EXAMPLES::

            sage: ZpCA(17)(0)._is_exact_zero()
            False
        """
        return False

    cpdef bint _is_inexact_zero(self) except -1:
        """
        Returns True if self is indistinguishable from zero, but not
        exactly zero.

        EXAMPLES::

            sage: Zp(5)(0,5)._is_inexact_zero()
            True
        """
        raise NotImplementedError

    cpdef bint _is_zero_rep(self) except -1:
        """
        Returns True is self is indistinguishable from zero.

        EXAMPLES::

            sage: ZpCA(17)(0,15)._is_zero_rep()
            True
        """
        return self._is_inexact_zero() or self._is_exact_zero()

    cdef bint _set_prec_abs(self, long absprec) except -1:
        self._set_prec_both(absprec, (<PowComputer_class>self.parent().prime_pow).prec_cap)

    cdef bint _set_prec_rel(self, long relprec) except -1:
        self._set_prec_both((<PowComputer_class>self.parent().prime_pow).prec_cap, relprec)

    cdef bint _set_prec_both(self, long absprec, long relprec) except -1:
        return 0

    def __floordiv__(self, right):
        """
        Divides self by right and throws away the nonintegral part if
        self.parent() is not a field.

        There are a number of reasonable definitions for floor
        division.  Any definition should satisfy the following
        identity:

        (1) a = (a // b) * b + a % b

        If a and b lie in a field, then setting a % b = 0 and a // b =
        a / b provides a canonical way of satisfying this equation.

        However, for elements of integer rings, there are many choices
        of definitions for a // b and a % b that satisfy this
        equation.  Since p-adic rings in Sage come equipped with a
        uniformizer pi, we can use the choice of uniformizer in our
        definitions.  Here are some other criteria we might ask for:

        (2) If b = pi^k, the series expansion (in terms of pi) of a //
        b is just the series expansion of a, shifted over by k terms.

        (2') The series expansion of a % pi^k has no terms above
        pi^(k-1).

        The conditions (2) and (2') are equivalent.  But when we
        generalize these conditions to arbitrary b they diverge.

        (3) For general b, the series expansion of a // b is just the
        series expansion of a / b, truncating terms with negative
        exponents of pi.

        (4) For general b, the series expansion of a % b has no terms
        above b.valuation() - 1.

        In order to satisfy (3), one defines

        a // b = (a / b.unit_part()) >> b.valuation()
        a % b = a - (a // b) * b

        In order to satisfy (4), one defines

        a % b = a.lift() % pi.lift()^b.valuation()
        a // b = ((a - a % b) >> b.valuation()) / b.unit_part()


        In Sage we choose option (3), mainly because it is more easily
        defined in terms of shifting and thus generalizes more easily
        to extension rings.

        EXAMPLES::

            sage: R = ZpCA(5); a = R(129378); b = R(2398125)
            sage: a // b #indirect doctest
            3 + 3*5 + 4*5^2 + 2*5^4 + 2*5^6 + 4*5^7 + 5^9 + 5^10 + 5^11 + O(5^12)
            sage: a / b
            4*5^-4 + 3*5^-3 + 2*5^-2 + 5^-1 + 3 + 3*5 + 4*5^2 + 2*5^4 + 2*5^6 + 4*5^7 + 5^9 + 5^10 + 5^11 + O(5^12)
            sage: a % b
            3 + 5^4 + 3*5^5 + 2*5^6 + 4*5^7 + 5^8 + O(5^16)
            sage: (a // b) * b + a % b
            3 + 2*5^4 + 5^5 + 3*5^6 + 5^7 + O(5^16)

        The alternative definition::

            sage: a
            3 + 2*5^4 + 5^5 + 3*5^6 + 5^7 + O(5^20)
            sage: c = ((a - 3)>>4)/b.unit_part(); c
            1 + 2*5 + 2*5^3 + 4*5^4 + 5^6 + 5^7 + 5^8 + 4*5^9 + 2*5^10 + 4*5^11 + 4*5^12 + 2*5^13 + 3*5^14 + O(5^16)
            sage: c*b + 3
            3 + 2*5^4 + 5^5 + 3*5^6 + 5^7 + O(5^20)
        """
        P = self.parent()
        if P.is_field():
            return self / right
        else:
            right = P(right)
            if right._is_inexact_zero():
                raise PrecisionError("cannot divide by something indistinguishable from zero")
            elif right._is_exact_zero():
                raise ZeroDivisionError("cannot divide by zero")
            return self._floordiv_(right)

    cpdef _floordiv_(self, right):
        """
        Implements floor division.

        EXAMPLES::

            sage: R = Zp(5, 5); a = R(77)
            sage: a // 15 # indirect doctest
            1 + 4*5 + 5^2 + 3*5^3 + O(5^4)
        """
        v, u = right.val_unit()
        return self.parent()(self / u) >> v

    def __getitem__(self, n):
        r"""
        Returns the coefficient of `p^n` in the series expansion of this
        element, as an integer in the range `0` to `p-1`.

        EXAMPLES::

            sage: R = Zp(7,4,'capped-rel','series'); a = R(1/3); a
            5 + 4*7 + 4*7^2 + 4*7^3 + O(7^4)
            sage: a[0] #indirect doctest
            doctest:warning
            ...
            DeprecationWarning: __getitem__ is changing to match the behavior of number fields. Please use expansion instead.
            See http://trac.sagemath.org/14825 for details.
            5
            sage: a[1]
            4

        Negative indices do not have the special meaning they have for regular
        python lists. In the following example, ``a[-1]`` is simply the
        coefficient of `7^{-1}`::

            sage: K = Qp(7,4,'capped-rel')
            sage: b = K(1/7 + 7); b
            7^-1 + 7 + O(7^3)
            sage: b[-2]
            0
            sage: b[-1]
            1
            sage: b[0]
            0
            sage: b[1]
            1
            sage: b[2]
            0

        It is an error to access coefficients which are beyond the precision
        bound::

            sage: b[3]
            Traceback (most recent call last):
            ...
            PrecisionError
            sage: b[-2]
            0

        Slices also work::

            sage: a[0:2]
            5 + 4*7 + O(7^2)
            sage: a[-1:3:2]
            5 + 4*7^2 + O(7^3)
            sage: b[0:2]
            7 + O(7^2)
            sage: b[-1:3:2]
            7^-1 + 7 + O(7^3)

        If the slice includes coefficients which are beyond the precision
        bound, they are ignored. This is similar to the behaviour of slices of
        python lists::

            sage: a[3:7]
            4*7^3 + O(7^4)
            sage: b[3:7]
            O(7^3)

        For extension elements, "zeros" match the behavior of
        ``list``::

            sage: S.<a> = Qq(125)
            sage: a[-2]
            []

        .. SEEALSO::

            :meth:`sage.rings.padics.local_generic_element.LocalGenericElement.slice`
        """
        from sage.misc.superseded import deprecation
        deprecation(14825, "__getitem__ is changing to match the behavior of number fields. Please use expansion instead.")
        return self.expansion(n)

    def __invert__(self):
        r"""
        Returns the multiplicative inverse of self.

        EXAMPLES::

            sage: R = Zp(7,4,'capped-rel','series'); a = R(3); a
            3 + O(7^4)
            sage: ~a #indirect doctest
            5 + 4*7 + 4*7^2 + 4*7^3 + O(7^4)

        .. NOTE::

            The element returned is an element of the fraction field.
        """
        return ~self.parent().fraction_field()(self, relprec = self.precision_relative())

    cpdef _mod_(self, right):
        """
        If self is in a field, returns 0.  If in a ring, returns a
        p-adic integer such that

        (1) a = (a // b) * b + a % b

        holds.

        WARNING: The series expansion of a % b continues above the
        valuation of b.

        The definitions of a // b and a % b are intertwined by
        equation (1).  If a and b lie in a field, then setting a % b =
        0 and a // b = a / b provides a canonical way of satisfying
        this equation.

        However, for elements of integer rings, there are many choices
        of definitions for a // b and a % b that satisfy this
        equation.  Since p-adic rings in Sage come equipped with a
        uniformizer pi, we can use the choice of uniformizer in our
        definitions.  Here are some other criteria we might ask for:

        (2) If b = pi^k, the series expansion (in terms of pi) of a //
        b is just the series expansion of a, shifted over by k terms.

        (2') The series expansion of a % pi^k has no terms above
        pi^(k-1).

        The conditions (2) and (2') are equivalent.  But when we
        generalize these conditions to arbitrary b they diverge.

        (3) For general b, the series expansion of a // b is just the
        series expansion of a / b, truncating terms with negative
        exponents of pi.

        (4) For general b, the series expansion of a % b has no terms
        above b.valuation() - 1.

        In order to satisfy (3), one defines

        a // b = (a / b.unit_part()) >> b.valuation()
        a % b = a - (a // b) * b

        In order to satisfy (4), one defines

        a % b = a.lift() % pi.lift()^b.valuation()
        a // b = ((a - a % b) >> b.valuation()) / b.unit_part()


        In Sage we choose option (3), mainly because it is more easily
        defined in terms of shifting and thus generalizes more easily
        to extension rings.

        EXAMPLES::

            sage: R = ZpCA(5); a = R(129378); b = R(2398125)
            sage: a % b
            3 + 5^4 + 3*5^5 + 2*5^6 + 4*5^7 + 5^8 + O(5^16)
        """
        if right == 0:
            raise ZeroDivisionError
        if self.parent().is_field():
            return self.parent()(0)
        else:
            return self - (self // right) * right

    #def _is_exact_zero(self):
    #    return False

    #def _is_inexact_zero(self):
    #    return self.is_zero() and not self._is_exact_zero()

    def str(self, mode=None):
        """
        Returns a string representation of self.

        EXAMPLES::

            sage: Zp(5,5,print_mode='bars')(1/3).str()[3:]
            '1|3|1|3|2'
        """
        return self._repr_(mode=mode)

    def _repr_(self, mode=None, do_latex=False):
        """
        Returns a string representation of this element.

        INPUT:

        - ``mode`` -- allows one to override the default print mode of
          the parent (default: ``None``).

        - ``do_latex`` -- whether to return a latex representation or
          a normal one.

        EXAMPLES::

            sage: Zp(5,5)(1/3) # indirect doctest
            2 + 3*5 + 5^2 + 3*5^3 + 5^4 + O(5^5)
        """
        return self.parent()._printer.repr_gen(self, do_latex, mode=mode)

    def additive_order(self, prec):
        r"""
        Returns the additive order of self, where self is considered
        to be zero if it is zero modulo `p^{\mbox{prec}}`.

        INPUT:

        - ``self`` -- a p-adic element
        - ``prec`` -- an integer

        OUTPUT:

        integer -- the additive order of self

        EXAMPLES::

            sage: R = Zp(7, 4, 'capped-rel', 'series'); a = R(7^3); a.additive_order(3)
            1
            sage: a.additive_order(4)
            +Infinity
            sage: R = Zp(7, 4, 'fixed-mod', 'series'); a = R(7^5); a.additive_order(6)
            1
        """
        if self.is_zero(prec):
            return Integer(1)
        else:
            return infinity

    def minimal_polynomial(self, name):
        """
        Returns a minimal polynomial of this `p`-adic element, i.e., ``x - self``

        INPUT:

        - ``self`` -- a `p`-adic element

        - ``name`` -- string: the name of the variable

        EXAMPLES::

            sage: Zp(5,5)(1/3).minimal_polynomial('x')
            (1 + O(5^5))*x + (3 + 5 + 3*5^2 + 5^3 + 3*5^4 + O(5^5))
        """
        R = self.parent()[name]
        return R.gen() - R(self)

    def norm(self, ground=None):
        """
        Returns the norm of this `p`-adic element over the ground ring.

        .. WARNING::

            This is not the `p`-adic absolute value.  This is a field
            theoretic norm down to a ground ring.  If you want the
            `p`-adic absolute value, use the ``abs()`` function
            instead.

        INPUT:

        - ``ground`` -- a subring of the parent (default: base ring)

        EXAMPLES::

            sage: Zp(5)(5).norm()
            5 + O(5^21)
        """
        if (ground is not None) and (ground != self.parent()):
            raise ValueError("Ground Ring not a subfield")
        else:
            return self

    def trace(self, ground=None):
        """
        Returns the trace of this `p`-adic element over the ground ring

        INPUT:

        - ``ground`` -- a subring of the ground ring (default: base
          ring)

        OUTPUT:

        - ``element`` -- the trace of this `p`-adic element over the
          ground ring

        EXAMPLES::

            sage: Zp(5,5)(5).trace()
            5 + O(5^6)
        """
        if (ground is not None) and (ground != self.parent()):
            raise ValueError("Ground ring not a subring")
        else:
            return self

    def algdep(self, n):
        """
        Returns a polynomial of degree at most `n` which is approximately
        satisfied by this number. Note that the returned polynomial need not be
        irreducible, and indeed usually won't be if this number is a good
        approximation to an algebraic number of degree less than `n`.

        ALGORITHM: Uses the PARI C-library ``algdep`` command.

        INPUT:

        - ``self`` -- a p-adic element
        - ``n`` -- an integer

        OUTPUT:

        polynomial -- degree n polynomial approximately satisfied by self

        EXAMPLES::

            sage: K = Qp(3,20,'capped-rel','series'); R = Zp(3,20,'capped-rel','series')
            sage: a = K(7/19); a
            1 + 2*3 + 3^2 + 3^3 + 2*3^4 + 2*3^5 + 3^8 + 2*3^9 + 3^11 + 3^12 + 2*3^15 + 2*3^16 + 3^17 + 2*3^19 + O(3^20)
            sage: a.algdep(1)
            19*x - 7
            sage: K2 = Qp(7,20,'capped-rel')
            sage: b = K2.zeta(); b.algdep(2)
            x^2 - x + 1
            sage: K2 = Qp(11,20,'capped-rel')
            sage: b = K2.zeta(); b.algdep(4)
            x^4 - x^3 + x^2 - x + 1
            sage: a = R(7/19); a
            1 + 2*3 + 3^2 + 3^3 + 2*3^4 + 2*3^5 + 3^8 + 2*3^9 + 3^11 + 3^12 + 2*3^15 + 2*3^16 + 3^17 + 2*3^19 + O(3^20)
            sage: a.algdep(1)
            19*x - 7
            sage: R2 = Zp(7,20,'capped-rel')
            sage: b = R2.zeta(); b.algdep(2)
            x^2 - x + 1
            sage: R2 = Zp(11,20,'capped-rel')
            sage: b = R2.zeta(); b.algdep(4)
            x^4 - x^3 + x^2 - x + 1
        """
        # TODO: figure out if this works for extension rings.  If not, move this to padic_base_generic_element.
        from sage.arith.all import algdep
        return algdep(self, n)

    def algebraic_dependency(self, n):
        """
        Returns a polynomial of degree at most `n` which is approximately
        satisfied by this number.  Note that the returned polynomial need not
        be irreducible, and indeed usually won't be if this number is a good
        approximation to an algebraic number of degree less than `n`.

        ALGORITHM: Uses the PARI C-library algdep command.

        INPUT:

        - ``self`` -- a p-adic element
        - ``n`` -- an integer

        OUTPUT:

        polynomial -- degree n polynomial approximately satisfied by self

        EXAMPLES::

            sage: K = Qp(3,20,'capped-rel','series'); R = Zp(3,20,'capped-rel','series')
            sage: a = K(7/19); a
            1 + 2*3 + 3^2 + 3^3 + 2*3^4 + 2*3^5 + 3^8 + 2*3^9 + 3^11 + 3^12 + 2*3^15 + 2*3^16 + 3^17 + 2*3^19 + O(3^20)
            sage: a.algebraic_dependency(1)
            19*x - 7
            sage: K2 = Qp(7,20,'capped-rel')
            sage: b = K2.zeta(); b.algebraic_dependency(2)
            x^2 - x + 1
            sage: K2 = Qp(11,20,'capped-rel')
            sage: b = K2.zeta(); b.algebraic_dependency(4)
            x^4 - x^3 + x^2 - x + 1
            sage: a = R(7/19); a
            1 + 2*3 + 3^2 + 3^3 + 2*3^4 + 2*3^5 + 3^8 + 2*3^9 + 3^11 + 3^12 + 2*3^15 + 2*3^16 + 3^17 + 2*3^19 + O(3^20)
            sage: a.algebraic_dependency(1)
            19*x - 7
            sage: R2 = Zp(7,20,'capped-rel')
            sage: b = R2.zeta(); b.algebraic_dependency(2)
            x^2 - x + 1
            sage: R2 = Zp(11,20,'capped-rel')
            sage: b = R2.zeta(); b.algebraic_dependency(4)
            x^4 - x^3 + x^2 - x + 1
        """
        return self.algdep(n)

    #def exp_artin_hasse(self):
    #    """
    #    Returns the Artin-Hasse exponential of self.

    #    This is defined by: E_p(x) = exp(x + x^p/p + x^(p^2)/p^2 + ...)
    #    """
    #    raise NotImplementedError

    def dwork_expansion(self, bd=20, a=0):
        r"""
        Return the value of a function defined by Dwork.

        Used to compute the `p`-adic Gamma function, see :meth:`gamma`.

        INPUT:

        - ``bd`` -- integer. Is a bound for precision, defaults to 20
        - ``a``  -- integer. Offset parameter, defaults to 0

        OUTPUT:

        A ``p``-- adic integer.

        .. NOTE::

            This is based on GP code written by Fernando Rodriguez
            Villegas (http://www.ma.utexas.edu/cnt/cnt-frames.html).
            William Stein sped it up for GP
            (http://sage.math.washington.edu/home/wstein/www/home/wbhart/pari-2.4.2.alpha/src/basemath/trans2.c).
            The output is a `p`-adic integer from Dwork's expansion,
            used to compute the `p`-adic gamma function as in [RV]_
            section 6.2.
            The coefficients of the expansion are now cached to speed up
            multiple evaluation, as in the trace formula for hypergeometric
            motives.

        REFERENCES:

        .. [RV] Rodriguez Villegas, Fernando. Experimental Number Theory.
           Oxford Graduate Texts in Mathematics 13, 2007.

        EXAMPLES::

            sage: R = Zp(17)
            sage: x = R(5+3*17+13*17^2+6*17^3+12*17^5+10*17^(14)+5*17^(17)+O(17^(19)))
            sage: x.dwork_expansion(18)
            16 + 7*17 + 11*17^2 + 4*17^3 + 8*17^4 + 10*17^5 + 11*17^6 + 6*17^7 
            + 17^8 + 8*17^10 + 13*17^11 + 9*17^12 + 15*17^13  + 2*17^14 + 6*17^15 
            + 7*17^16 + 6*17^17 + O(17^18)

            sage: R = Zp(5)
            sage: x = R(3*5^2+4*5^3+1*5^4+2*5^5+1*5^(10)+O(5^(20)))
            sage: x.dwork_expansion()
            4 + 4*5 + 4*5^2 + 4*5^3 + 2*5^4 + 4*5^5 + 5^7 + 3*5^9 + 4*5^10 + 3*5^11 
            + 5^13 + 4*5^14 + 2*5^15 + 2*5^16 + 2*5^17 + 3*5^18 + O(5^20)

        This test was added in :trac:`24433`::

            sage: F = Qp(7)
            sage: F(4).gamma()
            6 + O(7^20)
            sage: -F(1).dwork_expansion(a=3)
            6 + 4*7^19 + O(7^20)
        """
        R = self.parent()
        cdef int p = R.prime()
        cdef int b = a
        cdef int k

        s = R.zero().add_bigoh(bd)
        t = R.one().add_bigoh(bd)
        try:
            v = R.dwork_coeffs
        except AttributeError:
            v = None
        if v is not None and len(v) < p * bd:
            v = None
        if v is not None:
            for k in range(bd):
                s += t * v[p*k+b]
                t *= (self + k)
        else:
            u = [t]
            v = []
            for j in range(1, p):
                u.append(u[j-1] / j)
            for k in range(bd):
                v += [x << k for x in u]
                s += t * (u[a] << k)
                t *= (self + k)
                u[0] = ((u[-1] + u[0]) / (k+1)) >> 1
                for j in range(1, p):
                    u[j] = (u[j-1] + u[j]) / (j + (k+1) * p )
            R.dwork_coeffs = v
        return -s

    def gamma(self, algorithm='pari'):
        r"""
        Return the value of the `p`-adic Gamma function.

        INPUT:

        - ``algorithm`` -- string. Can be set to ``'pari'`` to call
          the pari function, or ``'sage'`` to call the function
          implemented in sage.  set to ``'pari'`` by default, since
          pari is about 10 times faster than sage.

        OUTPUT:

        - a `p`-adic integer

        .. NOTE::

            This is based on GP code written by Fernando Rodriguez
            Villegas (http://www.ma.utexas.edu/cnt/cnt-frames.html).
            William Stein sped it up for GP
            (http://sage.math.washington.edu/home/wstein/www/home/wbhart/pari-2.4.2.alpha/src/basemath/trans2.c).
            The 'sage' version uses dwork_expansion() to compute the
            `p`-adic gamma function of self as in [RV]_ section 6.2.

        EXAMPLES:

        This example illustrates ``x.gamma()`` for `x` a `p`-adic unit::

            sage: R = Zp(7)
            sage: x = R(2+3*7^2+4*7^3+O(7^20))
            sage: x.gamma('pari')
            1 + 2*7^2 + 4*7^3 + 5*7^4 + 3*7^5 + 7^8 + 7^9 + 4*7^10 + 3*7^12 
            + 7^13 + 5*7^14 + 3*7^15 + 2*7^16 + 2*7^17 + 5*7^18 + 4*7^19 + O(7^20)
            sage: x.gamma('sage')
            1 + 2*7^2 + 4*7^3 + 5*7^4 + 3*7^5 + 7^8 + 7^9 + 4*7^10 + 3*7^12 
            + 7^13 + 5*7^14 + 3*7^15 + 2*7^16 + 2*7^17 + 5*7^18 + 4*7^19 + O(7^20)
            sage: x.gamma('pari') == x.gamma('sage')
            True

        Now ``x.gamma()`` for `x` a `p`-adic integer but not a unit::

            sage: R = Zp(17)
            sage: x = R(17+17^2+3*17^3+12*17^8+O(17^13))
            sage: x.gamma('pari')
            1 + 12*17 + 13*17^2 + 13*17^3 + 10*17^4 + 7*17^5 + 16*17^7 
            + 13*17^9 + 4*17^10 + 9*17^11 + 17^12 + O(17^13)
            sage: x.gamma('sage')
            1 + 12*17 + 13*17^2 + 13*17^3 + 10*17^4 + 7*17^5 + 16*17^7 
            + 13*17^9 + 4*17^10 + 9*17^11 + 17^12 + O(17^13)
            sage: x.gamma('pari') == x.gamma('sage')
            True

        Finally, this function is not defined if `x` is not a `p`-adic integer::

            sage: K = Qp(7)
            sage: x = K(7^-5 + 2*7^-4 + 5*7^-3 + 2*7^-2 + 3*7^-1 + 3 + 3*7 
            ....:       + 7^3 + 4*7^4 + 5*7^5 + 6*7^8 + 3*7^9 + 6*7^10 + 5*7^11 + 6*7^12 
            ....:       + 3*7^13 + 5*7^14 + O(7^15))
            sage: x.gamma()
            Traceback (most recent call last):
            ...
            ValueError: The p-adic gamma function only works on elements of Zp

        TESTS:

        We check that :trac:`23784` is resolved::

            sage: Zp(5)(0).gamma()
            1 + O(5^20)

        Check the cached version of `dwork_expansion` from :trac:`24433`::

            sage: p = next_prime(200)
            sage: F = Qp(p)
            sage: l1 = [F(a/(p-1)).gamma(algorithm='pari') for a in range(p-1)]
            sage: l2 = [F(a/(p-1)).gamma(algorithm='sage') for a in range(p-1)]
            sage: all(l1[i] == l2[i] for i in range(p-1))
            True
        """
        if self.valuation() < 0:
            raise ValueError('The p-adic gamma function only works '
                             'on elements of Zp')
        parent = self.parent()
        n = self.precision_absolute()
        if n is infinity:
            # Have to deal with exact zeros separately
            return parent(1)
        if algorithm == 'pari':
            return parent(self.__pari__().gamma())
        elif algorithm == 'sage':
            p = parent.prime()
            bd = n + 2*n//p
            k = Integer(-self.residue(field=False)) # avoid GF(p) for efficiency
            x = (self+k) >> 1
            return -x.dwork_expansion(bd, a=k)

    @coerce_binop
    def gcd(self, other):
        r"""
        Return a greatest common divisor of ``self`` and ``other``.

        INPUT:

        - ``other`` -- an element in the same ring as ``self``

        AUTHORS:

        - Julian Rueth (2012-10-19): initial version

        .. NOTE::

            Since the elements are only given with finite precision,
            their greatest common divisor is in general not unique (not even up
            to units). For example `O(3)` is a representative for the elements
            0 and 3 in the 3-adic ring `\ZZ_3`. The greatest common
            divisor of `O(3)` and `O(3)` could be (among others) 3 or 0 which
            have different valuation. The algorithm implemented here, will
            return an element of??minimal valuation among the possible greatest
            common divisors.

        EXAMPLES:

        The greatest common divisor is either zero or a power of the
        uniformizing parameter::

            sage: R = Zp(3)
            sage: R.zero().gcd(R.zero())
            0
            sage: R(3).gcd(9)
            3 + O(3^21)

        A non-zero result is always lifted to the maximal precision possible in
        the ring::

            sage: a = R(3,2); a
            3 + O(3^2)
            sage: b = R(9,3); b
            3^2 + O(3^3)
            sage: a.gcd(b)
            3 + O(3^21)
            sage: a.gcd(0)
            3 + O(3^21)

        If both elements are zero, then the result is zero with the precision
        set to the smallest of their precisions::

            sage: a = R.zero(); a
            0
            sage: b = R(0,2); b
            O(3^2)
            sage: a.gcd(b)
            O(3^2)

        One could argue that it is mathematically correct to return `9 +
        O(3^{22})` instead. However, this would lead to some confusing
        behaviour::

            sage: alternative_gcd = R(9,22); alternative_gcd
            3^2 + O(3^22)
            sage: a.is_zero()
            True
            sage: b.is_zero()
            True
            sage: alternative_gcd.is_zero()
            False

        If exactly one element is zero, then the result depends on the
        valuation of the other element::

            sage: R(0,3).gcd(3^4)
            O(3^3)
            sage: R(0,4).gcd(3^4)
            O(3^4)
            sage: R(0,5).gcd(3^4)
            3^4 + O(3^24)

        Over a field, the greatest common divisor is either zero (possibly with
        finite precision) or one::

            sage: K = Qp(3)
            sage: K(3).gcd(0)
            1 + O(3^20)
            sage: K.zero().gcd(0)
            0
            sage: K.zero().gcd(K(0,2))
            O(3^2)
            sage: K(3).gcd(4)
            1 + O(3^20)

        TESTS:

        The implementation also works over extensions::

            sage: K = Qp(3)
            sage: R.<a> = K[]
            sage: L.<a> = K.extension(a^3-3)
            sage: (a+3).gcd(3)
            1 + O(a^60)

            sage: R = Zp(3)
            sage: S.<a> = R[]
            sage: S.<a> = R.extension(a^3-3)
            sage: (a+3).gcd(3)
            a + O(a^61)

            sage: K = Qp(3)
            sage: R.<a> = K[]
            sage: L.<a> = K.extension(a^2-2)
            sage: (a+3).gcd(3)
            1 + O(3^20)

            sage: R = Zp(3)
            sage: S.<a> = R[]
            sage: S.<a> = R.extension(a^2-2)
            sage: (a+3).gcd(3)
            1 + O(3^20)

        For elements with a fixed modulus::

            sage: R = ZpFM(3)
            sage: R(3).gcd(9)
            3 + O(3^20)

        And elements with a capped absolute precision::

            sage: R = ZpCA(3)
            sage: R(3).gcd(9)
            3 + O(3^20)

        """
        if self.is_zero() and other.is_zero():
            if self.valuation() < other.valuation():
                return self
            else:
                return other

        if self.parent().is_field():
            return self.parent().one()

        if min(self.valuation(),other.valuation()) >= min(self.precision_absolute(),other.precision_absolute()):
            return self.parent().zero().add_bigoh(min(self.precision_absolute(),other.precision_absolute()))

        return self.parent().uniformiser_pow( min(self.valuation(),other.valuation()) )

    @coerce_binop
    def xgcd(self, other):
        r"""
        Compute the extended gcd of this element and ``other``.

        INPUT:

        - ``other`` -- an element in the same ring

        OUTPUT:

        A tuple ``r``, ``s``, ``t`` such that ``r`` is a greatest common
        divisor of this element and ``other`` and ``r = s*self + t*other``.

        AUTHORS:

        - Julian Rueth (2012-10-19): initial version

        .. NOTE::

            Since the elements are only given with finite precision, their
            greatest common divisor is in general not unique (not even up to
            units). For example `O(3)` is a representative for the elements 0
            and 3 in the 3-adic ring `\ZZ_3`. The greatest common
            divisor of `O(3)` and `O(3)` could be (among others) 3 or 0 which
            have different valuation. The algorithm implemented here, will
            return an element of minimal valuation among the possible greatest
            common divisors.

        EXAMPLES:

        The greatest common divisor is either zero or a power of the
        uniformizing parameter::

            sage: R = Zp(3)
            sage: R.zero().xgcd(R.zero())
            (0, 1 + O(3^20), 0)
            sage: R(3).xgcd(9)
            (3 + O(3^21), 1 + O(3^20), 0)

        Unlike for :meth:`gcd`, the result is not lifted to the maximal
        precision possible in the ring; it is such that ``r = s*self +
        t*other`` holds true::

            sage: a = R(3,2); a
            3 + O(3^2)
            sage: b = R(9,3); b
            3^2 + O(3^3)
            sage: a.xgcd(b)
            (3 + O(3^2), 1 + O(3), 0)
            sage: a.xgcd(0)
            (3 + O(3^2), 1 + O(3), 0)

        If both elements are zero, then the result is zero with
        the precision set to the smallest of their precisions::

            sage: a = R.zero(); a
            0
            sage: b = R(0,2); b
            O(3^2)
            sage: a.xgcd(b)
            (O(3^2), 0, 1 + O(3^20))

        If only one element is zero, then the result depends on its precision::

            sage: R(9).xgcd(R(0,1))
            (O(3), 0, 1 + O(3^20))
            sage: R(9).xgcd(R(0,2))
            (O(3^2), 0, 1 + O(3^20))
            sage: R(9).xgcd(R(0,3))
            (3^2 + O(3^22), 1 + O(3^20), 0)
            sage: R(9).xgcd(R(0,4))
            (3^2 + O(3^22), 1 + O(3^20), 0)

        Over a field, the greatest common divisor is either zero (possibly with
        finite precision) or one::

            sage: K = Qp(3)
            sage: K(3).xgcd(0)
            (1 + O(3^20), 3^-1 + O(3^19), 0)
            sage: K.zero().xgcd(0)
            (0, 1 + O(3^20), 0)
            sage: K.zero().xgcd(K(0,2))
            (O(3^2), 0, 1 + O(3^20))
            sage: K(3).xgcd(4)
            (1 + O(3^20), 3^-1 + O(3^19), 0)

        TESTS:

        The implementation also works over extensions::

            sage: K = Qp(3)
            sage: R.<a> = K[]
            sage: L.<a> = K.extension(a^3-3)
            sage: (a+3).xgcd(3)
            (1 + O(a^60),
             a^-1 + 2*a + a^3 + 2*a^4 + 2*a^5 + 2*a^8 + 2*a^9
              + 2*a^12 + 2*a^13 + 2*a^16 + 2*a^17 + 2*a^20 + 2*a^21 + 2*a^24
              + 2*a^25 + 2*a^28 + 2*a^29 + 2*a^32 + 2*a^33 + 2*a^36 + 2*a^37
              + 2*a^40 + 2*a^41 + 2*a^44 + 2*a^45 + 2*a^48 + 2*a^49 + 2*a^52
              + 2*a^53 + 2*a^56 + 2*a^57 + O(a^59),
             0)

            sage: R = Zp(3)
            sage: S.<a> = R[]
            sage: S.<a> = R.extension(a^3-3)
            sage: (a+3).xgcd(3)
            (a + O(a^61),
             1 + 2*a^2 + a^4 + 2*a^5 + 2*a^6 + 2*a^9 + 2*a^10
              + 2*a^13 + 2*a^14 + 2*a^17 + 2*a^18 + 2*a^21 + 2*a^22 + 2*a^25
              + 2*a^26 + 2*a^29 + 2*a^30 + 2*a^33 + 2*a^34 + 2*a^37 + 2*a^38
              + 2*a^41 + 2*a^42 + 2*a^45 + 2*a^46 + 2*a^49 + 2*a^50 + 2*a^53
              + 2*a^54 + 2*a^57 + 2*a^58 + O(a^60),
             0)

            sage: K = Qp(3)
            sage: R.<a> = K[]
            sage: L.<a> = K.extension(a^2-2)
            sage: (a+3).xgcd(3)
            (1 + O(3^20),
             2*a + (a + 1)*3 + (2*a + 1)*3^2 + (a + 2)*3^4 + 3^5
              + (2*a + 2)*3^6 + a*3^7 + (2*a + 1)*3^8 + (a + 2)*3^10 + 3^11
              + (2*a + 2)*3^12 + a*3^13 + (2*a + 1)*3^14 + (a + 2)*3^16
              + 3^17 + (2*a + 2)*3^18 + a*3^19 + O(3^20),
             0)

            sage: R = Zp(3)
            sage: S.<a> = R[]
            sage: S.<a> = R.extension(a^2-2)
            sage: (a+3).xgcd(3)
            (1 + O(3^20),
             2*a + (a + 1)*3 + (2*a + 1)*3^2 + (a + 2)*3^4 + 3^5
              + (2*a + 2)*3^6 + a*3^7 + (2*a + 1)*3^8 + (a + 2)*3^10 + 3^11
              + (2*a + 2)*3^12 + a*3^13 + (2*a + 1)*3^14 + (a + 2)*3^16 + 3^17
              + (2*a + 2)*3^18 + a*3^19 + O(3^20),
             0)

        For elements with a fixed modulus::

            sage: R = ZpFM(3)
            sage: R(3).xgcd(9)
            (3 + O(3^20), 1 + O(3^20), O(3^20))

        And elements with a capped absolute precision::

            sage: R = ZpCA(3)
            sage: R(3).xgcd(9)
            (3 + O(3^20), 1 + O(3^19), O(3^20))

        """
        s,t = self.parent().zero(), self.parent().zero()
        if self.is_zero() and other.is_zero():
            if self.valuation() <= other.valuation():
                s = self.parent().one()
            else:
                t = self.parent().one()
        elif self.parent().is_field():
            if not self.is_zero():
                s = ~self
            else:
                t = ~other
        elif self.valuation() < other.valuation():
            if self.is_zero():
                s = self.parent().one()
            else:
                s = self.unit_part().inverse_of_unit()
        else:
            if other.is_zero():
                t = self.parent().one()
            else:
                t = other.unit_part().inverse_of_unit()

        return s*self+t*other,s,t

    def is_square(self): #should be overridden for lazy elements
        """
        Returns whether self is a square

        INPUT:

        - ``self`` -- a p-adic element

        OUTPUT:

        boolean -- whether self is a square

        EXAMPLES::

            sage: R = Zp(3,20,'capped-rel')
            sage: R(0).is_square()
            True
            sage: R(1).is_square()
            True
            sage: R(2).is_square()
            False

        TESTS::

            sage: R(3).is_square()
            False
            sage: R(4).is_square()
            True
            sage: R(6).is_square()
            False
            sage: R(9).is_square()
            True

            sage: R2 = Zp(2,20,'capped-rel')
            sage: R2(0).is_square()
            True
            sage: R2(1).is_square()
            True
            sage: R2(2).is_square()
            False
            sage: R2(3).is_square()
            False
            sage: R2(4).is_square()
            True
            sage: R2(5).is_square()
            False
            sage: R2(6).is_square()
            False
            sage: R2(7).is_square()
            False
            sage: R2(8).is_square()
            False
            sage: R2(9).is_square()
            True

            sage: K = Qp(3,20,'capped-rel')
            sage: K(0).is_square()
            True
            sage: K(1).is_square()
            True
            sage: K(2).is_square()
            False
            sage: K(3).is_square()
            False
            sage: K(4).is_square()
            True
            sage: K(6).is_square()
            False
            sage: K(9).is_square()
            True
            sage: K(1/3).is_square()
            False
            sage: K(1/9).is_square()
            True

            sage: K2 = Qp(2,20,'capped-rel')
            sage: K2(0).is_square()
            True
            sage: K2(1).is_square()
            True
            sage: K2(2).is_square()
            False
            sage: K2(3).is_square()
            False
            sage: K2(4).is_square()
            True
            sage: K2(5).is_square()
            False
            sage: K2(6).is_square()
            False
            sage: K2(7).is_square()
            False
            sage: K2(8).is_square()
            False
            sage: K2(9).is_square()
            True
            sage: K2(1/2).is_square()
            False
            sage: K2(1/4).is_square()
            True
       """
        if self._is_exact_zero() or self._is_inexact_zero():
            return True
        elif self.parent().prime() != 2:
            return (self.valuation() % 2 == 0) and (self.unit_part().residue(1).is_square())
        else:
            #won't work for general extensions...
            return (self.valuation() % 2 == 0) and (self.unit_part().residue(3) == 1)

    def is_squarefree(self):
        r"""
        Return whether this element is squarefree, i.e., whether there exists
        no non-unit `g` such that `g^2` divides this element.

        EXAMPLES:

        The zero element is never squarefree::

            sage: K = Qp(2)
            sage: K.zero().is_squarefree()
            False

        In `p`-adic rings, only elements of valuation at most 1 are
        squarefree::

            sage: R = Zp(2)
            sage: R(1).is_squarefree()
            True
            sage: R(2).is_squarefree()
            True
            sage: R(4).is_squarefree()
            False

        This works only if the precision is known sufficiently well::

            sage: R(0,1).is_squarefree()
            Traceback (most recent call last):
            ...
            PrecisionError: element not known to sufficient precision to decide squarefreeness
            sage: R(0,2).is_squarefree()
            False
            sage: R(1,1).is_squarefree()
            True

        For fields we are not so strict about the precision and treat inexact
        zeros as the zero element::

            K(0,0).is_squarefree()
            False

        """
        if self.parent().is_field():
            if self.is_zero():
                return False
            return True
        else:
            v = self.valuation()
            if v >= 2:
                return False
            elif self.is_zero():
                raise PrecisionError("element not known to sufficient precision to decide squarefreeness")
            else:
                return True

    #def log_artin_hasse(self):
    #    raise NotImplementedError

    def multiplicative_order(self, prec = None):
        r"""
        Returns the multiplicative order of self, where self is
        considered to be one if it is one modulo `p^{\mbox{prec}}`.

        INPUT:

        - ``self`` -- a p-adic element
        - ``prec`` -- an integer

        OUTPUT:

        - integer -- the multiplicative order of self

        EXAMPLES::

            sage: K = Qp(5,20,'capped-rel')
            sage: K(-1).multiplicative_order(20)
            2
            sage: K(1).multiplicative_order(20)
            1
            sage: K(2).multiplicative_order(20)
            +Infinity
            sage: K(5).multiplicative_order(20)
            +Infinity
            sage: K(1/5).multiplicative_order(20)
            +Infinity
            sage: K.zeta().multiplicative_order(20)
            4

        Over unramified extensions::

            sage: L1.<a> = Qq(5^3)
            sage: c = L1.teichmuller(a)
            sage: c.multiplicative_order()
            124
            sage: c^124
            1 + O(5^20)

        Over totally ramified extensions::

            sage: L2.<pi> = Qp(5).extension(x^4 + 5*x^3 + 10*x^2 + 10*x + 5)
            sage: u = 1 + pi
            sage: u.multiplicative_order()
            5
            sage: v = L2.teichmuller(2)
            sage: v.multiplicative_order()
            4
            sage: (u*v).multiplicative_order()
            20

        TESTS::

            sage: R = Zp(5,20,'capped-rel')
            sage: R(-1).multiplicative_order(20)
            2
            sage: R(1).multiplicative_order(20)
            1
            sage: R(2).multiplicative_order(20)
            +Infinity
            sage: R(3).multiplicative_order(20)
            +Infinity
            sage: R(4).multiplicative_order(20)
            +Infinity
            sage: R(5).multiplicative_order(20)
            +Infinity
            sage: R(25).multiplicative_order(20)
            +Infinity
            sage: R.zeta().multiplicative_order(20)
            4
        """
        if prec is not None:
            self = self.add_bigoh(prec)
        if self == 0 or self.valuation() != 0:
            return infinity
        parent = self.parent()
        p = parent.prime()

        # Compute the multiplicative order outside p
        res = self.residue()
        order = res.multiplicative_order()
        self /= parent.teichmuller(self)
        if self == 1:
            return order

        # Compute multiplicative order at p
        e = parent.e()
        if not (p-1).divides(e):
            return infinity
        n = e.valuation(p)
        for _ in range(n+1):
            order *= p
            self = self**p
            if self == 1:
                return order
        return infinity

    def valuation(self, p = None):
        """
        Returns the valuation of this element.

        INPUT:

        - ``self`` -- a p-adic element
        - ``p`` -- a prime (default: None). If specified, will make sure that p==self.parent().prime()

        NOTE: The optional argument p is used for consistency with the valuation methods on integer and rational.

        OUTPUT:

        integer -- the valuation of self

        EXAMPLES::

            sage: R = Zp(17, 4,'capped-rel')
            sage: a = R(2*17^2)
            sage: a.valuation()
            2
            sage: R = Zp(5, 4,'capped-rel')
            sage: R(0).valuation()
            +Infinity

        TESTS::

            sage: R(1).valuation()
            0
            sage: R(2).valuation()
            0
            sage: R(5).valuation()
            1
            sage: R(10).valuation()
            1
            sage: R(25).valuation()
            2
            sage: R(50).valuation()
            2
            sage: R = Qp(17, 4)
            sage: a = R(2*17^2)
            sage: a.valuation()
            2
            sage: R = Qp(5, 4)
            sage: R(0).valuation()
            +Infinity
            sage: R(1).valuation()
            0
            sage: R(2).valuation()
            0
            sage: R(5).valuation()
            1
            sage: R(10).valuation()
            1
            sage: R(25).valuation()
            2
            sage: R(50).valuation()
            2
            sage: R(1/2).valuation()
            0
            sage: R(1/5).valuation()
            -1
            sage: R(1/10).valuation()
            -1
            sage: R(1/25).valuation()
            -2
            sage: R(1/50).valuation()
            -2

            sage: K.<a> = Qq(25)
            sage: K(0).valuation()
            +Infinity

            sage: R(1/50).valuation(5)
            -2
            sage: R(1/50).valuation(3)
            Traceback (most recent call last):
            ...
            ValueError: Ring (5-adic Field with capped relative precision 4) residue field of the wrong characteristic.
        """
        if not p is None and p != self.parent().prime():
            raise ValueError('Ring (%s) residue field of the wrong characteristic.' % self.parent())
        cdef long v = self.valuation_c()
        if v == maxordp:
            return infinity
        if v == -maxordp:
            return -infinity
        cdef Integer ans = PY_NEW(Integer)
        mpz_set_si(ans.value, v)
        return ans

    cdef long valuation_c(self):
        """
        This function is overridden in subclasses to provide an
        actual implementation of valuation.

        For exact zeros, ``maxordp`` is returned, rather than infinity.

        EXAMPLES:

        For example, the valuation function on pAdicCappedRelativeElements
        uses an overridden version of this function.

        ::

            sage: Zp(5)(5).valuation() #indirect doctest
            1
        """
        raise NotImplementedError

    cpdef val_unit(self):
        """
        Return ``(self.valuation(), self.unit_part())``. To be overridden in
        derived classes.

        EXAMPLES::

            sage: Zp(5,5)(5).val_unit()
            (1, 1 + O(5^5))
        """
        raise NotImplementedError

    def ordp(self, p = None):
        r"""
        Returns the valuation of self, normalized so that the valuation of `p` is 1

        INPUT:

        - ``self`` -- a p-adic element
        - ``p`` -- a prime (default: ``None``). If specified, will make sure that ``p == self.parent().prime()``

        NOTE: The optional argument p is used for consistency with the valuation methods on integer and rational.


        OUTPUT:

        integer -- the valuation of self, normalized so that the valuation of `p` is 1

        EXAMPLES::

            sage: R = Zp(5,20,'capped-rel')
            sage: R(0).ordp()
            +Infinity
            sage: R(1).ordp()
            0
            sage: R(2).ordp()
            0
            sage: R(5).ordp()
            1
            sage: R(10).ordp()
            1
            sage: R(25).ordp()
            2
            sage: R(50).ordp()
            2
            sage: R(1/2).ordp()
            0
        """
        return self.valuation(p) / self.parent().ramification_index()

    def rational_reconstruction(self):
        r"""
        Returns a rational approximation to this `p`-adic number

        This will raise an ArithmeticError if there are no valid
        approximations to the unit part with numerator and
        denominator bounded by ``sqrt(p^absprec / 2)``.

        .. SEEALSO::

            :meth:`_rational_`

        OUTPUT:

        rational -- an approximation to self

        EXAMPLES::

            sage: R = Zp(5,20,'capped-rel')
            sage: for i in range(11):
            ....:     for j in range(1,10):
            ....:         if j == 5:
            ....:             continue
            ....:         assert i/j == R(i/j).rational_reconstruction()
        """
        if self.is_zero(self.precision_absolute()):
            return Rational(0)
        p = self.parent().prime()
        alpha = self.unit_part().lift()
        m = Integer(p**self.precision_relative())
        from sage.arith.all import rational_reconstruction
        r = rational_reconstruction(alpha, m)
        return (Rational(p)**self.valuation())*r

    def _rational_(self):
        r"""
        Return a rational approximation to this `p`-adic number.

        If there is no good rational approximation to the unit part,
        will just return the integer approximation.

        EXAMPLES::

            sage: R = Zp(7,5)
            sage: QQ(R(125)) # indirect doctest
            125
        """
        try:
            return self.rational_reconstruction()
        except ArithmeticError:
            p = self.parent().prime()
            return Rational(p**self.valuation() * self.unit_part().lift())

    def _number_field_(self, K):
        r"""
        Return an element of K approximating this p-adic number.

        INPUT:

        - ``K`` -- a number field

        EXAMPLES::

            sage: R.<a> = Zq(125)
            sage: K = R.exact_field()
            sage: a._number_field_(K)
            a
        """
        Kbase = K.base_ring()
        if K.defining_polynomial() != self.parent().defining_polynomial(exact=True):
            # Might convert to K's base ring.
            return Kbase(self)
        L = [Kbase(c) for c in self.polynomial().list()]
        if len(L) < K.degree():
            L += [Kbase(0)] * (K.degree() - len(L))
        return K(L)

    def _log_generic(self, aprec, mina=0):
        r"""
        Return ``\log(self)`` for ``self`` equal to 1 in the residue field

        This is a helper method for :meth:`log`.

        INPUT:

        - ``aprec`` -- an integer, the precision to which the result is
          correct. ``aprec`` must not exceed the precision cap of the ring over
          which this element is defined.

        - ``mina`` -- an integer (default: 0), the series will check `n` up to
          this valuation (and beyond) to see if they can contribute to the
          series.

        ALGORITHM:

        The computation uses the series

        .. MATH::

            -\log(1-x)=\sum_{n=1}^\infty \frac{x^n}{n}.

        For the result to be correct to precision ``aprec``, we sum all terms
        for which the valuation of `x^n/n` is stricly smaller than ``aprec``.

        EXAMPLES::

            sage: r = Qp(5,prec=4)(6)
            sage: r._log_generic(2)
            5 + O(5^2)
            sage: r._log_generic(4)
            5 + 2*5^2 + 4*5^3 + O(5^4)
            sage: r._log_generic(100)
            5 + 2*5^2 + 4*5^3 + O(5^4)

            sage: r = Zp(5,prec=4,type='fixed-mod')(6)
            sage: r._log_generic(5)
            5 + 2*5^2 + 4*5^3 + O(5^4)

        Only implemented for elements congruent to 1 modulo the maximal ideal::

            sage: r = Zp(5,prec=4,type='fixed-mod')(2)
            sage: r._log_generic(5)
            Traceback (most recent call last):
            ...
            ValueError: Input value (=2 + O(5^4)) must be 1 in the residue field

        """
        x = 1-self
        R = self.parent()
        # to get the precision right over capped-absolute rings, we have to
        # work over the capped-relative fraction field
        if R.is_capped_absolute():
            R = R.fraction_field()
            x = R(x)

        alpha=x.valuation()
        if alpha<=0:
            raise ValueError('Input value (=%s) must be 1 in the residue field' % self)

        e=R.ramification_index()
        p=R.prime()

        # we sum all terms of the power series of log into total
        total=R.zero()

        # pre-compute x^p/p into x2p_p
        if mina == 0 and alpha*p - e > aprec:
            # The value of x^p/p is not needed in that case
            x2p_p = R(0)
        elif R.is_capped_relative():
            if p*alpha >= e:
                x2p_p = x**p/p
            else:
                # x^p/p has negative valuation, so we need to be much
                # more careful about precision.
                x = x.lift_to_precision()
                x2p_p = x**p/p
        else:
            xu=x.unit_part()
            pu=R(p).unit_part()
            x2p_p=((xu**p)*pu.inverse_of_unit())*R.uniformizer_pow(p*alpha-e)

        # To get result right to precision aprec, we need all terms for which
        # the valuation of x^n/n is strictly smaller than aprec.
        # If we rewrite n=u*p^a with u a p-adic unit, then these are the terms
        # for which u<(aprec+a*v(p))/(v(x)*p^a).
        # Two sum over these terms, we run two nested loops, the outer one
        # iterates over the possible values for a, the inner one iterates over
        # the possible values for u.
        upper_u = (aprec/alpha).floor()
        if mina > 0 or upper_u > 0:
            a=0
            p2a=1       # p^a
            x2pa = x    # x^(p^a)

            # In the unramified case, we can stop summing terms as soon as
            # there are no u for a given a to sum over. In the ramified case,
            # it can happen that for some initial a there are no such u but
            # later in the series there are such u again. mina can be set to
            # take care of this by summing at least to a=mina-1
            while True:
                # we compute the sum for the possible values for u using Horner's method
                inner_sum = R.zero()
                for u in xrange(upper_u,0,-1):
                    # We want u to be a p-adic unit
                    if u%p==0:
                        new_term = R.zero()
                    else:
                        new_term = ~R(u)

                    # This hack is to deal with rings that don't lift to fields
                    if u > 1 or x2p_p.is_zero():
                        inner_sum = (inner_sum+new_term)*x2pa
                    else:
                        inner_sum = (inner_sum+new_term)*(x2p_p**a)*(x**(p2a-a*p))

                total -= inner_sum

                # Now increase a and check if a new iteration of the loop is needed
                a += 1
                p2a = p2a*p
                upper_u = ((aprec+a*e)/(alpha*p2a)).floor()
                if a >= mina and upper_u <= 0: break

                # We perform this last operation after the test
                # because it is costly and may raise OverflowError
                x2pa = x2pa**p

        return total.add_bigoh(aprec)

    def _log_binary_splitting(self, aprec, mina=0):
        r"""
        Return ``\log(self)`` for ``self`` equal to 1 in the residue field

        This is a helper method for :meth:`log`. 
        It uses a fast binary splitting algorithm.

        INPUT:

        - ``aprec`` -- an integer, the precision to which the result is
          correct. ``aprec`` must not exceed the precision cap of the ring over
          which this element is defined.

        - ``mina`` -- an integer (default: 0), the series will check `n` up to
          this valuation (and beyond) to see if they can contribute to the
          series.

        NOTE::

            The function does not check that its argument ``self`` is 
            1 in the residue field. If this assumption is not fullfiled
            the behaviour of the function is not specified.

        ALGORITHM:

        1. Raise `u` to the power `p^v` for a suitable `v` in order
           to make it closer to 1. (`v` is chosen such that `p^v` is
           close to the precision.)

        2. Write

        .. MATH::

            u^{p-1} = \prod_{i=1}^\infty (1 - a_i p^{(v+1)*2^i})

        with `0 \leq a_i < p^{(v+1)*2^i}` and compute 
        `\log(1 - a_i p^{(v+1)*2^i})` using the standard Taylor expansion

        .. MATH::

            \log(1 - x) = -x - 1/2 x^2 - 1/3 x^3 - 1/4 x^4 - 1/5 x^5 - \cdots

        together with a binary splitting method.

        3. Divide the result by `p^v`

        The complexity of this algorithm is quasi-linear.

        EXAMPLES::

            sage: r = Qp(5,prec=4)(6)
            sage: r._log_binary_splitting(2)
            5 + O(5^2)
            sage: r._log_binary_splitting(4)
            5 + 2*5^2 + 4*5^3 + O(5^4)
            sage: r._log_binary_splitting(100)
            5 + 2*5^2 + 4*5^3 + O(5^4)

            sage: r = Zp(5,prec=4,type='fixed-mod')(6)
            sage: r._log_binary_splitting(5)
            5 + 2*5^2 + 4*5^3 + O(5^4)

        """
        raise NotImplementedError

    def log(self, p_branch=None, pi_branch=None, aprec=None, change_frac=False, algorithm=None):
        r"""
        Compute the `p`-adic logarithm of this element.

        The usual power series for the logarithm with values in the additive
        group of a `p`-adic ring only converges for 1-units (units congruent to
        1 modulo `p`).  However, there is a unique extension of the logarithm
        to a homomorphism defined on all the units: If `u = a \cdot v` is a
        unit with `v \equiv 1 \pmod{p}` and `a` a Teichmuller representative,
        then we define `log(u) = log(v)`.  This is the correct extension
        because the units `U` split as a product `U = V \times \langle w
        \rangle`, where `V` is the subgroup of 1-units and `w` is a fundamental
        root of unity.  The `\langle w \rangle` factor is torsion, so must go
        to 0 under any homomorphism to the fraction field, which is a torsion
        free group.

        INPUT:

        - ``p_branch`` -- an element in the base ring or its fraction
          field; the implementation will choose the branch of the
          logarithm which sends `p` to ``branch``.

        - ``pi_branch`` -- an element in the base ring or its fraction
          field; the implementation will choose the branch of the
          logarithm which sends the uniformizer to ``branch``.  You
          may specify at most one of ``p_branch`` and ``pi_branch``,
          and must specify one of them if this element is not a unit.

        - ``aprec`` -- an integer or ``None`` (default: ``None``) if not
          ``None``, then the result will only be correct to precision
          ``aprec``.

        - ``change_frac`` -- In general the codomain of the logarithm should be
          in the `p`-adic field, however, for most neighborhoods of 1, it lies
          in the ring of integers. This flag decides if the codomain should be
          the same as the input (default) or if it should change to the
          fraction field of the input.

        - ``algorithm`` -- ``generic``, ``binary_splitting`` or ``None`` (default)
          The generic algorithm evaluates naively the series defining the log,
          namely

          .. MATH::
 
              \log(1-x) = -x - 1/2 x^2 - 1/3 x^3 - 1/4 x^4 - 1/5 x^5 - \cdots

          Its binary complexity is quadratic with respect to the precision.

          The binary splitting algorithm is faster, it has a quasi-linear
          complexity.
          By default, we use the binary splitting if it is available. Otherwise
          we switch to the generic algorithm.

        NOTES:

        What some other systems do:

        - PARI: Seems to define the logarithm for units not congruent
          to 1 as we do.

        - MAGMA: Only implements logarithm for 1-units (as of version 2.19-2)

        .. TODO::

            There is a soft-linear time algorithm for logarithm described
            by Dan Berstein at
            http://cr.yp.to/lineartime/multapps-20041007.pdf

        EXAMPLES::

            sage: Z13 = Zp(13, 10)
            sage: a = Z13(14); a
            1 + 13 + O(13^10)
            sage: a.log()
            13 + 6*13^2 + 2*13^3 + 5*13^4 + 10*13^6 + 13^7 + 11*13^8 + 8*13^9 + O(13^10)

            sage: Q13 = Qp(13, 10)
            sage: a = Q13(14); a
            1 + 13 + O(13^10)
            sage: a.log()
            13 + 6*13^2 + 2*13^3 + 5*13^4 + 10*13^6 + 13^7 + 11*13^8 + 8*13^9 + O(13^10)

        Note that the relative precision decreases when we take log.
        Precisely the absolute precision on ``\log(a)`` agrees with the relative
        precision on ``a`` thanks to the relation ``d\log(a) = da/a``.

        The call `log(a)` works as well::

            sage: log(a)
            13 + 6*13^2 + 2*13^3 + 5*13^4 + 10*13^6 + 13^7 + 11*13^8 + 8*13^9 + O(13^10)
            sage: log(a) == a.log()
            True

        The logarithm is not only defined for 1-units::

            sage: R = Zp(5,10)
            sage: a = R(2)
            sage: a.log()
            2*5 + 3*5^2 + 2*5^3 + 4*5^4 + 2*5^6 + 2*5^7 + 4*5^8 + 2*5^9 + O(5^10)

        If you want to take the logarithm of a non-unit you must specify either
        ``p_branch`` or ``pi_branch``::

            sage: b = R(5)
            sage: b.log()
            Traceback (most recent call last):
            ...
            ValueError: You must specify a branch of the logarithm for non-units
            sage: b.log(p_branch=4)
            4 + O(5^10)
            sage: c = R(10)
            sage: c.log(p_branch=4)
            4 + 2*5 + 3*5^2 + 2*5^3 + 4*5^4 + 2*5^6 + 2*5^7 + 4*5^8 + 2*5^9 + O(5^10)

        The branch parameters are only relevant for elements of non-zero
        valuation::

            sage: a.log(p_branch=0)
            2*5 + 3*5^2 + 2*5^3 + 4*5^4 + 2*5^6 + 2*5^7 + 4*5^8 + 2*5^9 + O(5^10)
            sage: a.log(p_branch=1)
            2*5 + 3*5^2 + 2*5^3 + 4*5^4 + 2*5^6 + 2*5^7 + 4*5^8 + 2*5^9 + O(5^10)

        Logarithms can also be computed in extension fields. First, in an
        Eisenstein extension::

            sage: R = Zp(5,5)
            sage: S.<x> = ZZ[]
            sage: f = x^4 + 15*x^2 + 625*x - 5
            sage: W.<w> = R.ext(f)
            sage: z = 1 + w^2 + 4*w^7; z
            1 + w^2 + 4*w^7 + O(w^20)
            sage: z.log()
            w^2 + 2*w^4 + 3*w^6 + 4*w^7 + w^9 + 4*w^10 + 4*w^11 + 4*w^12 + 3*w^14 + w^15 + w^17 + 3*w^18 + 3*w^19 + O(w^20)

        In an extension, there will usually be a difference between
        specifying ``p_branch`` and ``pi_branch``::

            sage: b = W(5)
            sage: b.log()
            Traceback (most recent call last):
            ...
            ValueError: You must specify a branch of the logarithm for non-units
            sage: b.log(p_branch=0)
            O(w^20)
            sage: b.log(p_branch=w)
            w + O(w^20)
            sage: b.log(pi_branch=0)
            3*w^2 + 2*w^4 + 2*w^6 + 3*w^8 + 4*w^10 + w^13 + w^14 + 2*w^15 + 2*w^16 + w^18 + 4*w^19 + O(w^20)
            sage: b.unit_part().log()
            3*w^2 + 2*w^4 + 2*w^6 + 3*w^8 + 4*w^10 + w^13 + w^14 + 2*w^15 + 2*w^16 + w^18 + 4*w^19 + O(w^20)
            sage: y = w^2 * 4*w^7; y
            4*w^9 + O(w^29)
            sage: y.log(p_branch=0)
            2*w^2 + 2*w^4 + 2*w^6 + 2*w^8 + w^10 + w^12 + 4*w^13 + 4*w^14 + 3*w^15 + 4*w^16 + 4*w^17 + w^18 + 4*w^19 + O(w^20)
            sage: y.log(p_branch=w)
            w + 2*w^2 + 2*w^4 + 4*w^5 + 2*w^6 + 2*w^7 + 2*w^8 + 4*w^9 + w^10 + 3*w^11 + w^12 + 4*w^14 + 4*w^16 + 2*w^17 + w^19 + O(w^20)

        Check that log is multiplicative::

            sage: y.log(p_branch=0) + z.log() - (y*z).log(p_branch=0)
            O(w^20)

        Now an unramified example::

            sage: g = x^3 + 3*x + 3
            sage: A.<a> = R.ext(g)
            sage: b = 1 + 5*(1 + a^2) + 5^3*(3 + 2*a)
            sage: b.log()
            (a^2 + 1)*5 + (3*a^2 + 4*a + 2)*5^2 + (3*a^2 + 2*a)*5^3 + (3*a^2 + 2*a + 2)*5^4 + O(5^5)

        Check that log is multiplicative::

            sage: c = 3 + 5^2*(2 + 4*a)
            sage: b.log() + c.log() - (b*c).log()
            O(5^5)

        We illustrate the effect of the precision argument::

            sage: R = ZpCA(7,10)
            sage: x = R(41152263); x
            5 + 3*7^2 + 4*7^3 + 3*7^4 + 5*7^5 + 6*7^6 + 7^9 + O(7^10)
            sage: x.log(aprec = 5)
            7 + 3*7^2 + 4*7^3 + 3*7^4 + O(7^5)
            sage: x.log(aprec = 7)
            7 + 3*7^2 + 4*7^3 + 3*7^4 + 7^5 + 3*7^6 + O(7^7)
            sage: x.log()
            7 + 3*7^2 + 4*7^3 + 3*7^4 + 7^5 + 3*7^6 + 7^7 + 3*7^8 + 4*7^9 + O(7^10)

        The logarithm is not defined for zero::

            sage: R.zero().log()
            Traceback (most recent call last):
            ...
            ValueError: logarithm is not defined at zero

        For elements in a `p`-adic ring, the logarithm will be returned in the
        same ring::

            sage: x = R(2)
            sage: x.log().parent()
            7-adic Ring with capped absolute precision 10
            sage: x = R(14)
            sage: x.log(p_branch=0).parent()
            7-adic Ring with capped absolute precision 10

        This is not possible if the logarithm has negative valuation::

            sage: R = ZpCA(3,10)
            sage: S.<x> = R[]
            sage: f = x^3 - 3
            sage: W.<w> = R.ext(f)
            sage: w.log(p_branch=2)
            Traceback (most recent call last):
            ...
            ValueError: logarithm is not integral, use change_frac=True to obtain a result in the fraction field
            sage: w.log(p_branch=2, change_frac=True)
            2*w^-3 + O(w^24)

        TESTS:

        Check that the generic algorithm and the binary splitting algorithm
        returns the same answers::

            sage: p = 17
            sage: R = Zp(p)
            sage: a = 1 + p*R.random_element()
            sage: l1 = a.log(algorithm='generic')
            sage: l2 = a.log(algorithm='binary_splitting')
            sage: l1 == l2
            True
            sage: l1.precision_absolute() == l2.precision_absolute()
            True

        Check multiplicativity::

            sage: p = 11
            sage: R = Zp(p, prec=1000)

            sage: x = 1 + p*R.random_element()
            sage: y = 1 + p*R.random_element()
            sage: log(x*y) == log(x) + log(y)
            True

            sage: x = y = 0
            sage: while x == 0:
            ....:     x = R.random_element()
            sage: while y == 0:
            ....:     y = R.random_element()
            sage: branch = R.random_element()
            sage: (x*y).log(p_branch=branch) == x.log(p_branch=branch) + y.log(p_branch=branch)
            True

        Note that multiplicativity may fail in the fixed modulus setting
        due to rounding errors::

            sage: R = ZpFM(2, prec=5)
            sage: R(180).log(p_branch=0) == R(30).log(p_branch=0) + R(6).log(p_branch=0)
            False

        Check that log is the inverse of exp::

            sage: p = 11
            sage: R = Zp(p, prec=1000)
            sage: a = 1 + p*R.random_element()
            sage: exp(log(a)) == a
            True

            sage: a = p*R.random_element()
            sage: log(exp(a)) == a
            True

        Check that results are consistent over a range of precision::

            sage: max_prec = 40
            sage: p = 3
            sage: K = Zp(p, max_prec)
            sage: full_log = (K(1 + p)).log()
            sage: for prec in range(2, max_prec):
            ....:     ll1 = (K(1+p).add_bigoh(prec)).log()
            ....:     ll2 = K(1+p).log(prec)
            ....:     assert ll1 == full_log
            ....:     assert ll2 == full_log
            ....:     assert ll1.precision_absolute() == prec

        Check that ``aprec`` works for fixed-mod elements::

            sage: R = ZpFM(7,10)
            sage: x = R(41152263); x
            5 + 3*7^2 + 4*7^3 + 3*7^4 + 5*7^5 + 6*7^6 + 7^9 + O(7^10)
            sage: x.log(aprec = 5)
            7 + 3*7^2 + 4*7^3 + 3*7^4 + O(7^10)
            sage: x.log(aprec = 7)
            7 + 3*7^2 + 4*7^3 + 3*7^4 + 7^5 + 3*7^6 + O(7^10)
            sage: x.log()
            7 + 3*7^2 + 4*7^3 + 3*7^4 + 7^5 + 3*7^6 + 7^7 + 3*7^8 + 4*7^9 + O(7^10)

        Check that precision is computed correctly in highly ramified
        extensions::

            sage: S.<x> = ZZ[]
            sage: K = Qp(5,5)
            sage: f = x^625 - 5*x - 5
            sage: W.<w> = K.extension(f)
            sage: z = 1 - w^2 + O(w^11)
            sage: x = 1 - z
            sage: z.log().precision_absolute()
            -975
            sage: (x^5/5).precision_absolute()
            -570
            sage: (x^25/25).precision_absolute()
            -975
            sage: (x^125/125).precision_absolute()
            -775

            sage: z = 1 - w + O(w^2)
            sage: x = 1 - z
            sage: z.log().precision_absolute()
            -1625
            sage: (x^5/5).precision_absolute()
            -615
            sage: (x^25/25).precision_absolute()
            -1200
            sage: (x^125/125).precision_absolute()
            -1625
            sage: (x^625/625).precision_absolute()
            -1250

            sage: z.log().precision_relative()
            250

        Performances::

            sage: R = Zp(17, prec=10^6)
            sage: a = R.random_element()
            sage: b = a.log(p_branch=0)   # should be rather fast

        AUTHORS:

        - William Stein: initial version

        - David Harvey (2006-09-13): corrected subtle precision bug (need to
          take denominators into account! -- see :trac:`53`)

        - Genya Zaytman (2007-02-14): adapted to new `p`-adic class

        - Amnon Besser, Marc Masdeu (2012-02-21): complete rewrite, valid for
          generic `p`-adic rings.

        - Soroosh Yazdani (2013-02-1): Fixed a precision issue in
          :meth:`_log_generic`.  This should really fix the issue with
          divisions.

        - Julian Rueth (2013-02-14): Added doctests, some changes for
          capped-absolute implementations.

        - Xavier Caruso (2017-06): Added binary splitting type algorithms
          over Qp

        """
        if self.is_zero():
            raise ValueError('logarithm is not defined at zero')
        if p_branch is not None and pi_branch is not None:
            raise ValueError("You may only specify a branch of the logarithm in one way")
        R = self.parent()
        p = R.prime()
        q = p**R.f()

        if self.is_padic_unit():
            total = R.zero()
        else:
            if pi_branch is None:
                if p_branch is None:
                    raise ValueError("You must specify a branch of the logarithm for non-units")
                pi_branch = (p_branch - R._log_unit_part_p()) / R.e()
            total = self.valuation() * pi_branch
        y = self.unit_part()
        x = 1 - y

        if x.valuation()>0:
            denom=Integer(1)
        else:
            y=y**(q-1) # Is it better to multiply it by Teichmuller element?
            denom=Integer(q-1)
            x = 1 - y

        minaprec = y.precision_absolute()
        minn = 0
        e = R.e()
        if e != 1:
            xval = x.valuation()
            lamb = minaprec - xval
            if lamb > 0 and lamb*(p-1) <= e:
                # This is the precision region where the absolute
                # precision of the answer might be less than the
                # absolute precision of the input

                # kink is the number of times we multiply the relative
                # precision by p before starting to add e instead.
                kink = (e // (lamb * (p-1))).exact_log(p) + 1

                # deriv0 is within 1 of the n yielding the minimal
                # absolute precision
                deriv0 = (e / (minaprec * p.log(prec=53))).floor().exact_log(p)

                # These are the absolute precisions of x^(p^n) at potential minimum points
                L = [(minaprec * p**n - n * e, n) for n in [0, kink, deriv0, deriv0+1]]
                L.sort()
                minaprec = L[0][0]
                minn = L[0][1]

        if aprec is None or aprec > minaprec:
            aprec=minaprec

        if algorithm is None:
            try:
                # The binary splitting algorithm is supposed to be faster
                log_unit = y._log_binary_splitting(aprec, minn)
            except NotImplementedError:
                log_unit = y._log_generic(aprec, minn)
        elif algorithm == "generic":
            log_unit = y._log_generic(aprec, minn)
        elif algorithm == "binary_splitting":
            log_unit = y._log_binary_splitting(aprec, minn)
        else:
            raise ValueError("Algorithm must be either 'generic', 'binary_splitting' or None")

        retval = total + log_unit*R(denom).inverse_of_unit()
        if not change_frac:
            if retval.valuation() < 0 and not R.is_field():
                raise ValueError("logarithm is not integral, use change_frac=True to obtain a result in the fraction field")
            retval=R(retval)
        return retval.add_bigoh(aprec)


    def _exp_generic(self, aprec):
        r"""
        Compute the exponential power series of this element, using Horner's
        evaluation and only one division.

        This is a helper method for :meth:`exp`.

        INPUT:

        - ``aprec`` -- an integer, the precision to which to compute the
          exponential

        EXAMPLES::

            sage: R.<w> = Zq(7^2,5)
            sage: x = R(7*w)
            sage: x.exp(algorithm="generic")   # indirect doctest
            1 + w*7 + (4*w + 2)*7^2 + (w + 6)*7^3 + 5*7^4 + O(7^5)

        AUTHORS:

        - Genya Zaytman (2007-02-15)

        - Amnon Besser, Marc Masdeu (2012-02-23): Complete rewrite

        - Soroosh Yazdani (2013-02-01): Added the code for capped relative

        - Julian Rueth (2013-02-14): Rewrite to solve some precision problems
          in the capped-absolute case

        """
        R=self.parent()
        p=self.parent().prime()
        e=self.parent().ramification_index()
        x_unit=self.unit_part()
        p_unit=R(p).unit_part().lift_to_precision()
        x_val=self.valuation()

        # the valuation of n! is bounded by e*n/(p-1), therefore the valuation
        # of self^n/n! is bigger or equal to n*x_val - e*n/(p-1). So, we only
        # have to sum terms for which n does not exceed N
        N = (aprec // (x_val - e/(p-1))).floor()

        # We evaluate the exponential series:
        # First, we compute the value of x^N+N*x^(N-1)+...+x*N!+N! using
        # Horner's method. Then, we divide by N!.
        # This would only work for capped relative elements since for other
        # elements, we would lose too much precision in the multiplications
        # with natural numbers. Therefore, we emulate the behaviour of
        # capped-relative elements and keep track of the unit part and the
        # valuation separately.

        # the value of x^N+N*x^(N-1)+...+x*N!+N!
        series_unit,series_val = R.one(), 0

        # we compute the value of N! as we go through the loop
        nfactorial_unit,nfactorial_val = R.one(),0

        nmodp = N%p
        for n in range(N,0,-1):
            # multiply everything by x
            series_val += x_val
            series_unit *= x_unit

            # compute the new value of N*(N-1)*...
            if nmodp == 0:
                n_pval, n_punit = Integer(n).val_unit(p)
                nfactorial_unit *= R(n_punit) * p_unit**n_pval
                nfactorial_val += n_pval*e
                nmodp = p
            else:
                nfactorial_unit *= n
            nmodp -= 1

            # now add N*(N-1)*...
            common_val = min(nfactorial_val, series_val)
            series_unit = (series_unit<<(series_val-common_val)) + (nfactorial_unit<<(nfactorial_val-common_val))
            series_val = common_val

        # multiply the result by N!
        return series_unit*nfactorial_unit.inverse_of_unit()<<(series_val-nfactorial_val)

    def _exp_binary_splitting(self, aprec):
        """
        Compute the exponential power series of this element

        This is a helper method for :meth:`exp`.

        INPUT:

        - ``aprec`` -- an integer, the precision to which to compute the
          exponential

        NOTE::

            The function does not check that its argument ``self`` is 
            the disk of convergence of ``exp``. If this assumption is not 
            fullfiled the behaviour of the function is not specified.

        ALGORITHM:

        Write

        .. MATH::

            self = \sum_{i=1}^\infty a_i p^{2^i}

        with `0 \leq a_i < p^{2^i}` and compute 
        `\exp(a_i p^{2^i})` using the standard Taylor expansion

        .. MATH::

            \exp(x) = 1 + x + x^2/2 + x^3/6 + x^4/24 + \cdots

        together with a binary splitting method.

        The binary complexity of this algorithm is quasi-linear.

        EXAMPLES::

            sage: R = Zp(7,5)
            sage: x = R(7)
            sage: x.exp(algorithm="binary_splitting")   # indirect doctest
            1 + 7 + 4*7^2 + 2*7^3 + O(7^5)

        """
        raise NotImplementedError("The binary splitting algorithm is not implemented for the parent: %s" % self.parent())

    def _exp_newton(self, aprec, log_algorithm=None):
        """
        Compute the exponential power series of this element

        This is a helper method for :meth:`exp`.

        INPUT:

        - ``aprec`` -- an integer, the precision to which to compute the
          exponential

        - ``log_algorithm`` (default: None) -- the algorithm used for
          computing the logarithm. This attribute is passed to the log
          method. See :meth:`log` for more details about the possible
          algorithms.

        NOTE::

            The function does not check that its argument ``self`` is 
            the disk of convergence of ``exp``. If this assumption is not 
            fullfiled the behaviour of the function is not specified.

        ALGORITHM:

        Solve the equation `\log(x) = self` using the Newton scheme::

        .. MATH::

            x_{i+1} = x_i \cdot (1 + self - \log(x_i))

        The binary complexity of this algorithm is roughly the same
        than that of the computation of the logarithm.

        EXAMPLES::

            sage: R.<w> = Zq(7^2,5)
            sage: x = R(7*w)
            sage: x.exp(algorithm="newton")   # indirect doctest
            1 + w*7 + (4*w + 2)*7^2 + (w + 6)*7^3 + 5*7^4 + O(7^5)
        """
        R = self.parent()
        e = R.e()
        a = R(1,aprec)
        l = R(0,aprec)
        if R.prime() == 2:
            trunc = e + 1
            while trunc < aprec:
                trunc = 2*trunc - e
                b = (self-l).add_bigoh(trunc).lift_to_precision(aprec)
                a *= 1+b
                l += (1+b).log(aprec, algorithm=log_algorithm)
        else:
            trunc = 1
            while trunc < aprec:
                trunc = 2*trunc
                b = (self-l).add_bigoh(trunc).lift_to_precision(aprec)
                a *= 1+b
                l += (1+b).log(aprec, algorithm=log_algorithm)
        return a


    def exp(self, aprec = None, algorithm=None):
        r"""
        Compute the `p`-adic exponential of this element if the exponential
        series converges.

        INPUT:

        - ``aprec`` -- an integer or ``None`` (default: ``None``); if
          specified, computes only up to the indicated precision.

        - ``algorithm`` -- ``generic``, ``binary_splitting``, ``newton`` 
          or ``None`` (default)
          The generic algorithm evaluates naively the series defining the
          exponential, namely

          .. MATH::
 
              \exp(x) = 1 + x + x^2/2 + x^3/6 + x^4/24 + \cdots

          Its binary complexity is quadratic with respect to the precision.

          The binary splitting algorithm is faster, it has a quasi-linear
          complexity.

          The ``Newton`` algorithms solve the equation `\log(x) = self` using
          a Newton scheme. It runs roughly as fast as the computation of the
          logarithm.

          By default, we use the binary splitting if it is available. 
          If it is not, we use the Newton algorithm if a fast algorithm for
          computing the logarithm is available.
          Otherwise we switch to the generic algorithm.

        EXAMPLES:

        :meth:`log` and :meth:`exp` are inverse to each other::

            sage: Z13 = Zp(13, 10)
            sage: a = Z13(14); a
            1 + 13 + O(13^10)
            sage: a.log().exp()
            1 + 13 + O(13^10)

        An error occurs if this is called with an element for which the
        exponential series does not converge::

            sage: Z13.one().exp()
            Traceback (most recent call last):
            ...
            ValueError: Exponential does not converge for that input.

        The next few examples illustrate precision when computing `p`-adic
        exponentials::

            sage: R = Zp(5,10)
            sage: e = R(2*5 + 2*5**2 + 4*5**3 + 3*5**4 + 5**5 + 3*5**7 + 2*5**8 + 4*5**9).add_bigoh(10); e
            2*5 + 2*5^2 + 4*5^3 + 3*5^4 + 5^5 + 3*5^7 + 2*5^8 + 4*5^9 + O(5^10)
            sage: e.exp()*R.teichmuller(4)
            4 + 2*5 + 3*5^3 + O(5^10)

        ::

            sage: K = Qp(5,10)
            sage: e = K(2*5 + 2*5**2 + 4*5**3 + 3*5**4 + 5**5 + 3*5**7 + 2*5**8 + 4*5**9).add_bigoh(10); e
            2*5 + 2*5^2 + 4*5^3 + 3*5^4 + 5^5 + 3*5^7 + 2*5^8 + 4*5^9 + O(5^10)
            sage: e.exp()*K.teichmuller(4)
            4 + 2*5 + 3*5^3 + O(5^10)

        Logarithms and exponentials in extension fields. First, in an
        Eisenstein extension::

            sage: R = Zp(5,5)
            sage: S.<x> = R[]
            sage: f = x^4 + 15*x^2 + 625*x - 5
            sage: W.<w> = R.ext(f)
            sage: z = 1 + w^2 + 4*w^7; z
            1 + w^2 + 4*w^7 + O(w^20)
            sage: z.log().exp()
            1 + w^2 + 4*w^7 + O(w^20)

        Now an unramified example::

            sage: R = Zp(5,5)
            sage: S.<x> = R[]
            sage: g = x^3 + 3*x + 3
            sage: A.<a> = R.ext(g)
            sage: b = 1 + 5*(1 + a^2) + 5^3*(3 + 2*a); b
            1 + (a^2 + 1)*5 + (2*a + 3)*5^3 + O(5^5)
            sage: b.log().exp()
            1 + (a^2 + 1)*5 + (2*a + 3)*5^3 + O(5^5)

        TESTS:

        Check that results are consistent over a range of precision::

            sage: max_prec = 40
            sage: p = 3
            sage: K = Zp(p, max_prec)
            sage: full_exp = (K(p)).exp()
            sage: for prec in range(2, max_prec):
            ....:     ll = (K(p).add_bigoh(prec)).exp()
            ....:     assert ll == full_exp
            ....:     assert ll.precision_absolute() == prec
            sage: K = Qp(p, max_prec)
            sage: full_exp = (K(p)).exp()
            sage: for prec in range(2, max_prec):
            ....:     ll = (K(p).add_bigoh(prec)).exp()
            ....:     assert ll == full_exp
            ....:     assert ll.precision_absolute() == prec

        Check that this also works for capped-absolute implementations::

            sage: Z13 = ZpCA(13, 10)
            sage: a = Z13(14); a
            1 + 13 + O(13^10)
            sage: a.log().exp()
            1 + 13 + O(13^10)

            sage: R = ZpCA(5,5)
            sage: S.<x> = R[]
            sage: f = x^4 + 15*x^2 + 625*x - 5
            sage: W.<w> = R.ext(f)
            sage: z = 1 + w^2 + 4*w^7; z
            1 + w^2 + 4*w^7 + O(w^20)
            sage: z.log().exp()
            1 + w^2 + 4*w^7 + O(w^20)

        Check that this also works for fixed-mod implementations::

            sage: Z13 = ZpFM(13, 10)
            sage: a = Z13(14); a
            1 + 13 + O(13^10)
            sage: a.log().exp()
            1 + 13 + O(13^10)

            sage: R = ZpFM(5,5)
            sage: S.<x> = R[]
            sage: f = x^4 + 15*x^2 + 625*x - 5
            sage: W.<w> = R.ext(f)
            sage: z = 1 + w^2 + 4*w^7; z
            1 + w^2 + 4*w^7 + O(w^20)
            sage: z.log().exp()
            1 + w^2 + 4*w^7 + O(w^20)

        Some corner cases::

            sage: Z2 = Zp(2, 5)
            sage: Z2(2).exp()
            Traceback (most recent call last):
            ...
            ValueError: Exponential does not converge for that input.

            sage: S.<x> = Z2[]
            sage: W.<w> = Z2.ext(x^3-2)
            sage: (w^2).exp()
            Traceback (most recent call last):
            ...
            ValueError: Exponential does not converge for that input.
            sage: (w^3).exp()
            Traceback (most recent call last):
            ...
            ValueError: Exponential does not converge for that input.
            sage: (w^4).exp()
            1 + w^4 + w^5 + w^7 + w^9 + w^10 + w^14 + O(w^15)

        Check that all algorithms output the same result::

            sage: R = Zp(5,50)
            sage: a = 5 * R.random_element()
            sage: bg = a.exp(algorithm="generic")
            sage: bbs = a.exp(algorithm="binary_splitting")
            sage: bn = a.exp(algorithm="newton")
            sage: bg == bbs
            True
            sage: bg == bn
            True

        Performances::

            sage: R = Zp(17,10^6)
            sage: a = 17 * R.random_element()
            sage: b = a.exp()    # should be rather fast

        AUTHORS:

        - Genya Zaytman (2007-02-15)

        - Amnon Besser, Marc Masdeu (2012-02-23): Complete rewrite

        - Julian Rueth (2013-02-14): Added doctests, fixed some corner cases

        - Xavier Caruso (2017-06): Added binary splitting and Newton algorithms

        """
        p = self.parent().prime()

        if (p-1)*self.valuation() <= self.parent().ramification_index():
            raise ValueError('Exponential does not converge for that input.')

        # The optimal absolute precision on exp(self)
        # is the absolution precision on self
        maxprec = min(self.precision_absolute(), self.parent().precision_cap())
        if aprec is None or aprec > maxprec:
            aprec = maxprec

        if algorithm is None:
            try:
                ans = self._exp_binary_splitting(aprec)
            except NotImplementedError:
                try:
                    ans = self._exp_newton(aprec, log_algorithm='binary_splitting')
                except NotImplementedError:
                    ans = self._exp_generic(aprec)
        elif algorithm == 'generic':
            ans = self._exp_generic(aprec)
        elif algorithm == 'binary_splitting':
            ans = self._exp_binary_splitting(aprec)
        elif algorithm == 'newton':
            ans = self._exp_newton(aprec)
        return ans.add_bigoh(aprec)
        

    def square_root(self, extend=True, all=False, algorithm=None):
        r"""
        Return the square root of this `p`-adic number.

        INPUT:

        - ``self`` -- a `p`-adic element.

        - ``extend`` -- a boolean (default: ``True``); if ``True``, return a 
          square root in an extension if necessary; if ``False`` and no root 
          exists in the given ring or field, raise a ValueError.

        - ``all`` -- a boolean (default: ``False``); if ``True``, return a 
          list of all square roots.

        - ``algorithm`` -- ``"pari"``, ``"sage"`` or ``None`` (default: 
          ``None``); Sage provides an implementation for any extension of 
          `Q_p` whereas only square roots over `Q_p` is implemented in Pari;
          the default is ``"pari"`` if the ground field is `Q_p`, ``"sage"``
          otherwise.

        OUTPUT:

        The square root or the list of all square roots of this `p`-adic 
        number.

        NOTE:

        The square root is chosen (resp. the square roots are ordered) in
        a deterministic way.

        EXAMPLES::

            sage: R = Zp(3, 20)
            sage: R(0).square_root()
            0

            sage: R(1).square_root()
            1 + O(3^20)

            sage: R(2).square_root(extend=False)
            Traceback (most recent call last):
            ...
            ValueError: element is not a square

            sage: -R(4).square_root()
            2 + O(3^20)

            sage: R(9).square_root()
            3 + O(3^21)

        When `p = 2`, the precision of the square root is less
        than the input::

            sage: R2 = Zp(2, 20)
            sage: R2(1).square_root()
            1 + O(2^19)
            sage: R2(4).square_root()
            2 + O(2^20)

            sage: R.<t> = Zq(2^10, 10)
            sage: u = 1 + 8*t
            sage: u.square_root()
            1 + t*2^2 + t^2*2^3 + t^2*2^4 + (t^4 + t^3 + t^2)*2^5 + (t^4 + t^2)*2^6 + (t^5 + t^2)*2^7 + (t^6 + t^5 + t^4 + t^2)*2^8 + O(2^9)

            sage: R.<a> = Zp(2).extension(x^3 - 2)
            sage: u = R(1 + a^4 + a^5 + a^7 + a^8, 10); u
            1 + a^4 + a^5 + a^7 + a^8 + O(a^10)
            sage: v = u.square_root(); v
            1 + a^2 + a^4 + a^6 + O(a^7)

        However, observe that the precision increases to its original value 
        when we recompute the square of the square root::

            sage: v^2
            1 + a^4 + a^5 + a^7 + a^8 + O(a^10)

        If the input does not have enough precision in order to determine if
        the given element has a square root in the ground field, an error is 
        raised::

            sage: R(1, 6).square_root()
            Traceback (most recent call last):
            ...
            PrecisionError: not enough precision to be sure that this element has a square root

            sage: R(1, 7).square_root()
            1 + O(a^4)

            sage: R(1+a^6, 7).square_root(extend=False)
            Traceback (most recent call last):
            ...
            ValueError: element is not a square

        In particular, an error is raised when we try to compute the square
        root of an inexact

        TESTS::

            sage: R = Qp(5, 100)
            sage: c = R.random_element()
            sage: s = (c^2).square_root()
            sage: s == c or s == -c
            True

        """
        # We first check trivial cases and precision
        if self._is_exact_zero():
            return self
        parent = self.parent()
        if self.is_zero() or (parent.prime() == 2 and self.precision_relative() < 1 + 2*parent.e()):
            raise PrecisionError("not enough precision to be sure that this element has a square root")

        if algorithm is None:
            if parent.degree() == 1:
                algorithm = "pari"
            else:
                algorithm = "sage"

        if algorithm == "pari":
            from sage.libs.pari.all import PariError
            ans = None
            try:
                # use pari
                ans = parent(self.__pari__().sqrt())
            except PariError:
                # todo: should eventually change to return an element of
                # an extension field
                pass
        elif algorithm == "sage":
            ans = self._square_root()
        if ans is not None:
            if list(ans.expansion()) > list((-ans).expansion()):
                ans = -ans
            if all:
                return [ans, -ans]
            else:
                return ans
        if extend:
            raise NotImplementedError("extending using the sqrt function not yet implemented")
        elif all:
            return []
        else:
            raise ValueError("element is not a square")

    def _square_root(self):
        """
        Return the square root of this `p`-adic number
        or ``None`` if this number does not have a square root

        NOTE:

        This is the Sage implementation used in :meth:`square_root`.

        This method assumes that the input is given at relative precision
        at least 1 if `p > 2` and relative precision at least `2e + 1` if
        `p = 2` (where `e` is the absolute ramification index).
        This is the minimal precision to be sure whether this number has
        or has not a square root.

        TESTS::

            sage: Q2 = Qp(2,20,'capped-rel')
            sage: Q2(1)._square_root()
            1 + O(2^19)
            sage: Q2(4)._square_root()
            2 + O(2^20)

            sage: Q5 = Qp(5,20,'capped-rel')
            sage: Q5(1)._square_root()
            1 + O(5^20)
            sage: Q5(-1)._square_root() == Q5.teichmuller(2) or Q5(-1).square_root() == Q5.teichmuller(3)
            True

            sage: Z3 = Zp(3,20,'capped-abs')
            sage: Z3(1).square_root()
            1 + O(3^20)
            sage: Z3(4).square_root() in [ Z3(2), -Z3(2) ]
            True
            sage: Z3(9).square_root()
            3 + O(3^19)

            sage: Z2 = Zp(2,20,'capped-abs')
            sage: Z2(1).square_root()
            1 + O(2^19)
            sage: Z2(4).square_root()
            2 + O(2^18)
            sage: Z2(9).square_root() in [ Z2(3), -Z2(3) ]
            True
            sage: Z2(17).square_root()
            1 + 2^3 + 2^5 + 2^6 + 2^7 + 2^9 + 2^10 + 2^13 + 2^16 + 2^17 + O(2^19)

            sage: Z5 = Zp(5,20,'capped-abs')
            sage: Z5(1).square_root()
            1 + O(5^20)
            sage: Z5(-1).square_root() == Z5.teichmuller(2) or Z5(-1).square_root() == Z5.teichmuller(3)
            True
        """
        ring = self.parent()
        p = ring.prime()
        e = ring.e()

        # First, we check valuation and renormalize if needed
        val = self.valuation()
        if val % 2 == 1:
            return None
        a = self >> val
        prec = a.precision_absolute()

        # We compute the square root of 1/a in the residue field
        abar = a.residue()
        try:
            xbar = 1/abar.sqrt(extend=False)
        except ValueError:
            return None
        x = ring(xbar)
        curprec = 1

        # When p is 2, we lift sqrt(1/a) modulo 2*pi (pi = uniformizer)
        if p == 2:   # We assume here that the relative precision is at least 2*e + 1
            x = x.lift_to_precision(e+1)

            # We will need 1/a at higher precision
            ainv = ~(a.add_bigoh(2*e+1))

            # We lift modulo 2
            k = ring.residue_field()
            while curprec < e:   # curprec is the number of correct digits of x
                # recomputing x^2 is not necessary:
                # we can alternatively update it after each update of x
                # (which is theoretically a bit faster)
                b = (ainv - x**2) >> (2*curprec)
                if b == 0: break
                for i in range(e - curprec):
                    if i % 2 == 0:
                        try:
                            cbar = k(b.expansion(i)).sqrt(extend=False)
                        except ValueError:
                            return None
                        c = ring(cbar).lift_to_precision()
                        x += c << (curprec + i//2)
                    else:
                        if b.expansion(i) != 0:
                            return None
                curprec = (curprec + e + 1) // 2

            # We lift one step further
            from sage.rings.polynomial.polynomial_ring_constructor import PolynomialRing
            S = PolynomialRing(k, name='x')
            b = (ainv - x**2) >> (2*e)
            AS = S([ b.residue(), xbar*k(ring(2,e+1).expansion(e)), 1 ])
            roots = AS.roots()
            if len(roots) == 0:
                return None
            x += ring(roots[0][0]) << e

            # For Newton iteration, we redefine curprec
            # as (a lower bound on) valuation(a*x^2 - 1)
            curprec = 2*e + 1

        # We perform Newton iteration
        while curprec < prec:
            if p == 2:
                curprec -= e
            curprec <<= 1
            x = x.lift_to_precision(min(prec,curprec))
            x += x * (1 - a*x*x) / 2

        return (a*x) << (val // 2)


    def __abs__(self):
        """
        Return the `p`-adic absolute value of ``self``.

        This is normalized so that the absolute value of `p` is `1/p`.

        EXAMPLES::

            sage: abs(Qp(5)(15))
            1/5
            sage: abs(Qp(7)(0))
            0

        An unramified extension::

            sage: R = Zp(5,5)
            sage: P.<x> = PolynomialRing(R)
            sage: Z25.<u> = R.ext(x^2 - 3)
            sage: abs(u)
            1
            sage: abs(u^24-1)
            1/5

        A ramified extension::

            sage: W.<w> = R.ext(x^5 + 75*x^3 - 15*x^2 + 125*x - 5)
            sage: abs(w)
            0.724779663677696
            sage: abs(W(0))
            0.000000000000000
        """
        return self.abs()

    cpdef abs(self, prec=None):
        """
        Return the `p`-adic absolute value of ``self``.

        This is normalized so that the absolute value of `p` is `1/p`.

        INPUT:

        - ``prec`` -- Integer.  The precision of the real field in which
          the answer is returned.  If ``None``, returns a rational for
          absolutely unramified fields, or a real with 53 bits of
          precision for ramified fields.

        EXAMPLES::

            sage: a = Qp(5)(15); a.abs()
            1/5
            sage: a.abs(53)
            0.200000000000000
            sage: Qp(7)(0).abs()
            0
            sage: Qp(7)(0).abs(prec=20)
            0.00000

        An unramified extension::

            sage: R = Zp(5,5)
            sage: P.<x> = PolynomialRing(R)
            sage: Z25.<u> = R.ext(x^2 - 3)
            sage: u.abs()
            1
            sage: (u^24-1).abs()
            1/5

        A ramified extension::

            sage: W.<w> = R.ext(x^5 + 75*x^3 - 15*x^2 + 125*x - 5)
            sage: w.abs()
            0.724779663677696
            sage: W(0).abs()
            0.000000000000000
        """
        K = self.parent()
        if not prec and K.e() > 1:
            prec = 53
        if prec:
            from sage.rings.real_mpfr import RealField
            if self.is_zero():
                return RealField(prec).zero()
            return RealField(prec)(K.prime())**(-self.ordp())
        else:
            if self.is_zero():
                return Rational(0)
            return Rational(K.prime())**(-self.valuation())

    cpdef bint _is_base_elt(self, p) except -1:
        """
        Return ``True`` if this element is an element of Zp or Qp (rather than
        an extension).

        INPUT:

        - ``p`` -- a prime, which is compared with the parent of this element.

        EXAMPLES::

            sage: a = Zp(5)(3); a._is_base_elt(5)
            True
            sage: a._is_base_elt(17)
            False

        """
        raise NotImplementedError

    def _polylog_res_1(self, n):
        """
        Return `Li_n(`self`)` , the `n`th `p`-adic polylogarithm of ``self``, assuming that self is congruent to 1 mod p.
        This is an internal function, used by :meth:`polylog`.

        INPUT:

            - ``n`` -- a non-negative integer

        OUTPUT:

            - Li_n(self)

        EXAMPLES ::

            sage: Qp(2)(-1)._polylog_res_1(6) == 0
            True

        ::
            sage: Qp(5)(1)._polylog_res_1(1)
            Traceback (most recent call last):
            ...
            ValueError: Polylogarithm is not defined for 1.
        """
        from sage.rings.power_series_ring import PowerSeriesRing
        from sage.functions.other import ceil,floor
        from sage.rings.padics.factory import Qp
        from sage.misc.all import verbose

        if self == 1:
            raise ValueError('Polylogarithm is not defined for 1.')

        p = self.parent().prime()
        prec = self.precision_absolute()

        K = self.parent().fraction_field()
        z = K(self)

        hsl = max(prec / ((z - 1).valuation()) + 1, prec*(p == 2))
        N = floor(prec - n*(hsl - 1).log(p))

        verbose(hsl, level=3)

        def bound(m):
            return prec - m + Integer(1-2**(m-1)).valuation(p) - m*(hsl - 1).log(p)

        gsl = max([_findprec(1/(p-1), 1, _polylog_c(m,p) + bound(m), p) for m in range(2,n+1)])
        verbose(gsl, level=3)
        g = _compute_g(p, n, max([bound(m) + m*floor((gsl-1).log(p)) for m in range(2, n+1)]), gsl)
        verbose(g, level=3)
        S = PowerSeriesRing(K, default_prec = ceil(hsl), names='t')
        t = S.gen()
        log1plust = (1+t).log()
        log1plusti = 1

        G = (n+1)*[0]
        for i in range(n+1):
            G[i] = (log1plusti)/Integer(i).factorial()
            log1plusti *= log1plust

        verbose(G, level=3)

        H = (n+1)*[0]
        H[2] = -sum([((-t)**i)/Integer(i)**2 for i in range(1,hsl+2)])
        for i in range(2, n):
            H[i+1] = (H[i]/(1+t) + G[i]/t).integral()
            if (i + 1) % 2 == 1:
                if p != 2:
                    H[i+1] += (2**i*p**(i+1)*g[i+1](1/K(2)))/((1-2**i)*(p**(i+1) - 1))
                else:
                    H[i+1] += (2**i*H[i+1](K(-2)))/(1 - 2**(i+1))

        verbose(H, level=3)
        return (H[n](z - 1) - ((z.log(0))**(n-1)*(1 - z).log(0))/Integer(n-1).factorial()).add_bigoh(N)

    def polylog(self, n):
        """
        Return `Li_n(self)` , the `n`th `p`-adic polylogarithm of this element.

        INPUT:

            - ``n`` -- a non-negative integer

        OUTPUT:

            - `Li_n(self)`

        EXAMPLES:

        The `n`-th polylogarithm of `-1` is `0` for even `n` ::

            sage: Qp(13)(-1).polylog(6) == 0
            True

        We can check some identities, for example those mentioned in [DCW2016]_ ::

            sage: x = Qp(7, prec=30)(1/3)
            sage: (x^2).polylog(4) - 8*x.polylog(4) - 8*(-x).polylog(4) == 0
            True

        ::

            sage: x = Qp(5, prec=30)(4)
            sage: x.polylog(2) + (1/x).polylog(2) + x.log(0)**2/2 == 0
            True

        ::

            sage: x = Qp(11, prec=30)(2)
            sage: x.polylog(2) + (1-x).polylog(2) + x.log(0)**2*(1-x).log(0) == 0
            True

        `Li_1(z) = -\log(1-z)` for `|z| < 1` ::

            sage: Qp(5)(10).polylog(1) == -Qp(5)(1-10).log(0)
            True

        The polylogarithm of 1 is not defined ::

            sage: Qp(5)(1).polylog(1)
            Traceback (most recent call last):
            ...
            ValueError: Polylogarithm is not defined for 1.


        The polylogarithm of 0 is 0 ::

            sage: Qp(11)(0).polylog(7)
            0

        ALGORITHM:

        The algorithm of Besser-de Jeu, as described in [BdJ2008]_ is used.

        REFERENCES:

        .. [BdJ2008] Besser, Amnon, and Rob de Jeu. "Li^(p)-Service? An Algorithm
             for Computing p-Adic Polylogarithms." Mathematics of Computation
             (2008): 1105-1134.

        .. [DCW2016] Dan-Cohen, Ishai, and Stefan Wewers. "Mixed Tate motives and the
             unit equation." International Mathematics Research Notices
             2016.17 (2016): 5291-5354.

        AUTHORS:

        - Jennifer Balakrishnan - Initial implementation
        - Alex J. Best (2017-07-21) - Extended to other residue disks

        .. TODO::

            - Implement for extensions
            - Use the change method to create K from self.parent()


        """
        from sage.rings.power_series_ring import PowerSeriesRing
        from sage.rings.padics.factory import Qp
        from sage.misc.all import verbose
        from sage.functions.other import ceil,floor
        from sage.rings.infinity import PlusInfinity

        if self.parent().degree() != 1:
            raise NotImplementedError("Polylogarithms are not currently implemented for elements of extensions")
            # TODO implement this (possibly after the change method for padic generic elements is added).

        prec = self.precision_absolute()

        p = self.parent().prime()
        K = self.parent().fraction_field()

        z = K(self)
        n = Integer(n)

        if z.valuation() < 0:
            verbose("residue oo, using functional equation for reciprocal. %d %s"%(n,str(self)), level=2)
            return (-1)**(n+1)*(1/z).polylog(n)-(z.log(0)**n)/K(n.factorial())

        zeta = K.teichmuller(z)

        # Which residue disk are we in?
        if zeta == 0:
            if z.precision_absolute() == PlusInfinity():
                return K(0)
            verbose("residue 0, using series. %d %s"%(n,str(self)), level=2)
            M = ceil((prec/z.valuation()).log(p))
            N = prec - n*M
            ret = K(0)
            for m in range(M + 1):
                zpm = z**(p**m)
                ret += p**(-m*n)*sum(zpm**k/Integer(k)**n for k in
                        range(1, _findprec(p**m*z.valuation(), 0, N + n*m, p)) if k % p != 0)

            return ret.add_bigoh(N)

        if zeta == 1:
            if z == 1:
                raise ValueError("Polylogarithm is not defined for 1.")
            verbose("residue 1, using _polylog_res_1. %d %s"%(n,str(self)), level=2)
            return self._polylog_res_1(n)

        # Set up precision bounds
        tsl = prec / (z - zeta).valuation() + 1
        N = floor(prec - n*(tsl - 1).log(p))
        gsl = max([_findprec(1/(p-1), 1, prec - m + _polylog_c(m,p) - m*(tsl - 1).log(p), p) for m in range(1,n+1)])

        gtr = _compute_g(p, n, prec + n*(gsl - 1).log(p), gsl)

        K = Qp(p, prec)

        # Residue disk around zeta
        verbose("general case. %d %s"%(n, str(self)), level=2)
        Li_i_zeta = [0] + [p**i/(p**i-1)*gtr[i](1/(1-zeta)) for i in range(1,n+1)]

        T = PowerSeriesRing(K, default_prec=ceil(tsl), names='t')
        t = T.gen()
        F = (n+1)*[0]
        F[0] = (zeta+t)/(1-zeta-t)
        for i in range(n):
            F[i+1] = Li_i_zeta[i+1] + (F[i]/(zeta + t)).integral()

        return (F[n](z - zeta)).add_bigoh(N)


# Module functions used by polylog
def _polylog_c(n, p):
    """
    Return c(n, p) = p/(p-1) - (n-1)/log(p) + (n-1)*log(n*(p-1)/log(p),p) + log(2*p*(p-1)*n/log(p), p)
    as defined in Prop 6.1 of [BdJ2008]_ which is used as a precision bound.
    This is an internal function, used by :meth:`polylog`.

    EXAMPLES::

        sage: sage.rings.padics.padic_generic_element._polylog_c(1, 2)
        log(4/log(2))/log(2) + 2

    REFERENCES:

    Prop. 6.1 of

        .. [BdJ2008] Besser, Amnon, and Rob de Jeu. "Li^(p)-Service? An Algorithm
             for Computing p-Adic Polylogarithms." Mathematics of Computation
             (2008): 1105-1134.

    """
    return p/(p-1) - (n-1)/p.log() + (n-1)*(n*(p-1)/p.log()).log(p) + (2*p*(p-1)*n/p.log()).log(p)

def _findprec(c_1, c_2, c_3, p):
    """
    Return an integer k such that c_1*k - c_2*log_p(k) > c_3.
    This is an internal function, used by :meth:`polylog`.

    INPUT:

    - `c_1`, `c_2`, `c_3` - positive integers
    - `p` - prime

    OUTPUT:

    ``sl`` such that `kc_1 - c_2 \log_p(k) > c_3` for all `k \ge sl`

    EXAMPLES::

        sage: sage.rings.padics.padic_generic_element._findprec(1, 1, 2, 2)
        5
        sage: 5*1 - 5*log(1, 2) > 2
        True

    REFERENCES:

    Remark 7.11 of

        .. [BdJ2008] Besser, Amnon, and Rob de Jeu. "Li^(p)-Service? An Algorithm
             for Computing p-Adic Polylogarithms." Mathematics of Computation
             (2008): 1105-1134.
    """
    from sage.functions.other import ceil
    k = Integer(max(ceil(c_2/c_1), 2))
    while True:
        if c_1*k - c_2*k.log(p) > c_3:
            return k
        k += 1

def _compute_g(p, n, prec, terms):
    """
    Return the list of power series `g_i = \int(-g_{i-1}/(v-v^2))` used in the computation of polylogarithms.
    This is an internal function, used by :meth:`polylog`.

    EXAMPLES::

        sage: sage.rings.padics.padic_generic_element._compute_g(7, 3, 3, 3)[0]
        (O(7^3))*v^2 + (1 + O(7^3))*v + (O(7^3))

    """
    from sage.rings.power_series_ring import PowerSeriesRing
    from sage.functions.other import ceil
    from sage.rings.padics.factory import Qp

    # Compute the sequence of power series g
    R = PowerSeriesRing(Qp(p, ceil(prec)), default_prec=terms, names='v')
    v = R.gen()
    g = (n+1)*[0]
    g[0] = v - 1 - ((v-1)**p)/(v**p-(v-1)**p)
    for i in range(n):
        g[i+1] = -(g[i]/(v-v**2)).integral()
    return [x.truncate(terms) for x in g]
