"""
Univariate Polynomial Base Class

AUTHORS:

-  William Stein: first version.

-  Martin Albrecht: Added singular coercion.

-  Robert Bradshaw: Move Polynomial_generic_dense to Cython.

-  Miguel Marco: Implemented resultant in the case where PARI fails.

-  Simon King: Use a faster way of conversion from the base ring.

-  Julian Rueth (2012-05-25,2014-05-09): Fixed is_squarefree() for imperfect
   fields, fixed division without remainder over QQbar; added ``_cache_key``
   for polynomials with unhashable coefficients

-  Simon King (2013-10): Implement copying of :class:`PolynomialBaseringInjection`.

-  Kiran Kedlaya (2016-03): Added root counting.

TESTS::

    sage: R.<x> = ZZ[]
    sage: f = x^5 + 2*x^2 + (-1)
    sage: f == loads(dumps(f))
    True

    sage: PolynomialRing(ZZ,'x').objgen()
    (Univariate Polynomial Ring in x over Integer Ring, x)
"""

#*****************************************************************************
#       Copyright (C) 2007 William Stein <wstein@gmail.com>
#
#  Distributed under the terms of the GNU General Public License (GPL)
#  as published by the Free Software Foundation; either version 2 of
#  the License, or (at your option) any later version.
#                  http://www.gnu.org/licenses/
#*****************************************************************************
from __future__ import print_function

cdef is_FractionField, is_RealField, is_ComplexField
cdef ZZ, QQ, RR, CC, RDF, CDF

cimport cython
from cpython.number cimport PyNumber_TrueDivide

import operator, copy, re

import sage.rings.rational
import sage.rings.integer
import polynomial_ring
import sage.rings.integer_ring
import sage.rings.rational_field
import sage.rings.finite_rings.integer_mod_ring
import sage.rings.complex_field
import sage.rings.fraction_field_element
import sage.rings.infinity as infinity
from sage.misc.sage_eval import sage_eval
from sage.misc.latex import latex
from sage.misc.long cimport pyobject_to_long
from sage.structure.factorization import Factorization
from sage.structure.element import coerce_binop

from sage.interfaces.singular import singular as singular_default, is_SingularElement
from sage.libs.all import pari, pari_gen, PariError

from sage.rings.real_mpfr import RealField, is_RealField, RR

from sage.rings.complex_field import is_ComplexField, ComplexField
CC = ComplexField()

from sage.rings.real_double import is_RealDoubleField, RDF
from sage.rings.complex_double import is_ComplexDoubleField, CDF
from sage.rings.real_mpfi import is_RealIntervalField

from sage.structure.element import generic_power
from sage.structure.element cimport (parent, have_same_parent,
        Element, RingElement, coercion_model)

from sage.rings.rational_field import QQ, is_RationalField
from sage.rings.integer_ring import ZZ, is_IntegerRing
from sage.rings.integer cimport Integer, smallInteger
from sage.libs.gmp.mpz cimport *
from sage.rings.fraction_field import is_FractionField
from sage.rings.padics.generic_nodes import is_pAdicRing, is_pAdicField

from sage.structure.category_object cimport normalize_names

from sage.misc.derivative import multi_derivative

from sage.arith.all import (sort_complex_numbers_for_display,
        power_mod, lcm, is_prime)

import polynomial_fateman

from sage.rings.ideal import is_Ideal
from sage.rings.polynomial.polynomial_ring_constructor import PolynomialRing
from sage.rings.polynomial.polynomial_ring import is_PolynomialRing
from sage.rings.polynomial.multi_polynomial_ring import is_MPolynomialRing
from sage.misc.cachefunc import cached_function

from sage.categories.map cimport Map
from sage.categories.morphism cimport Morphism

from sage.misc.superseded import deprecation

cpdef is_Polynomial(f):
    """
    Return True if f is of type univariate polynomial.

    INPUT:


    -  ``f`` - an object


    EXAMPLES::

        sage: from sage.rings.polynomial.polynomial_element import is_Polynomial
        sage: R.<x> = ZZ[]
        sage: is_Polynomial(x^3 + x + 1)
        True
        sage: S.<y> = R[]
        sage: f = y^3 + x*y -3*x; f
        y^3 + x*y - 3*x
        sage: is_Polynomial(f)
        True

    However this function does not return True for genuine multivariate
    polynomial type objects or symbolic polynomials, since those are
    not of the same data type as univariate polynomials::

        sage: R.<x,y> = QQ[]
        sage: f = y^3 + x*y -3*x; f
        y^3 + x*y - 3*x
        sage: is_Polynomial(f)
        False
        sage: var('x,y')
        (x, y)
        sage: f = y^3 + x*y -3*x; f
        y^3 + x*y - 3*x
        sage: is_Polynomial(f)
        False
    """
    return isinstance(f, Polynomial)

from polynomial_compiled cimport CompiledPolynomialFunction

from polydict import ETuple

cdef object is_AlgebraicRealField
cdef object is_AlgebraicField
cdef object is_AlgebraicField_common
cdef object NumberField_quadratic
cdef object is_ComplexIntervalField

cdef void late_import():
    # A hack to avoid circular imports.
    global is_AlgebraicRealField
    global is_AlgebraicField
    global is_AlgebraicField_common
    global NumberField_quadratic
    global is_ComplexIntervalField

    if is_AlgebraicRealField is not None:
        return

    import sage.rings.qqbar
    is_AlgebraicRealField = sage.rings.qqbar.is_AlgebraicRealField
    is_AlgebraicField = sage.rings.qqbar.is_AlgebraicField
    is_AlgebraicField_common = sage.rings.qqbar.is_AlgebraicField_common
    import sage.rings.number_field.number_field
    NumberField_quadratic = sage.rings.number_field.number_field.NumberField_quadratic
    import sage.rings.complex_interval_field
    is_ComplexIntervalField = sage.rings.complex_interval_field.is_ComplexIntervalField


cdef class Polynomial(CommutativeAlgebraElement):
    """
    A polynomial.

    EXAMPLE::

        sage: R.<y> = QQ['y']
        sage: S.<x> = R['x']
        sage: S
        Univariate Polynomial Ring in x over Univariate Polynomial Ring in y
        over Rational Field
        sage: f = x*y; f
        y*x
        sage: type(f)
        <type 'sage.rings.polynomial.polynomial_element.Polynomial_generic_dense'>
        sage: p = (y+1)^10; p(1)
        1024

    .. automethod:: _add_
    .. automethod:: _sub_
    .. automethod:: _lmul_
    .. automethod:: _rmul_
    .. automethod:: _mul_
    .. automethod:: _mul_trunc_
    """

    def __init__(self, parent, is_gen = False, construct=False):
        """
        The following examples illustrate creation of elements of
        polynomial rings, and some basic arithmetic.

        First we make a polynomial over the integers and do some
        arithmetic::

            sage: R.<x> = ZZ[]
            sage: f = x^5 + 2*x^2 + (-1); f
            x^5 + 2*x^2 - 1
            sage: f^2
            x^10 + 4*x^7 - 2*x^5 + 4*x^4 - 4*x^2 + 1

        Next we do arithmetic in a sparse polynomial ring over the
        integers::

            sage: R.<x> = ZZ[ ]; R
            Univariate Polynomial Ring in x over Integer Ring
            sage: S.<Z> = R[ ]; S
            Univariate Polynomial Ring in Z over Univariate Polynomial Ring in x over Integer Ring
            sage: f = Z^3 + (x^2-2*x+1)*Z - 3; f
            Z^3 + (x^2 - 2*x + 1)*Z - 3
            sage: f*f
            Z^6 + (2*x^2 - 4*x + 2)*Z^4 - 6*Z^3 + (x^4 - 4*x^3 + 6*x^2 - 4*x + 1)*Z^2 + (-6*x^2 + 12*x - 6)*Z + 9
            sage: f^3 == f*f*f
            True
        """
        CommutativeAlgebraElement.__init__(self, parent)
        self._is_gen = is_gen

    def _dict_to_list(self, x, zero):
          if len(x) == 0:
              return []
          n = max(x.keys())
          if isinstance(n, tuple): # a mpoly dict
              n = n[0]
              v = [zero] * (n+1)
              for i, z in x.iteritems():
                  v[i[0]] = z
          else:
              v = [zero] * (n+1)
              for i, z in x.iteritems():
                  v[i] = z
          return v

    cpdef _add_(self, right):
        r"""
        Add two polynomials.

        EXAMPLES::

            sage: R = ZZ['x']
            sage: p = R([1,2,3,4])
            sage: q = R([4,-3,2,-1])
            sage: p + q    # indirect doctest
            3*x^3 + 5*x^2 - x + 5
        """
        cdef Py_ssize_t i, min
        cdef list x = self.list()
        cdef list y = right.list()

        if len(x) > len(y):
            min = len(y)
            high = x[min:]
        elif len(x) < len(y):
            min = len(x)
            high = y[min:]
        else:
            min = len(x)
            high = []

        low = [x[i] + y[i] for i in range(min)]
        return self._parent(low + high)

    cpdef _neg_(self):
        return self._parent([-x for x in self.list()])

    cpdef bint is_zero(self):
        r"""
        Test whether this polynomial is zero.

        EXAMPLES::

            sage: R = GF(2)['x']['y']
            sage: R([0,1]).is_zero()
            False
            sage: R([0]).is_zero()
            True
            sage: R([-1]).is_zero()
            False
        """
        return self.degree() < 0

    cpdef bint is_one(self):
        r"""
        Test whether this polynomial is 1.

        EXAMPLES::

            sage: R.<x> = QQ[]
            sage: (x-3).is_one()
            False
            sage: R(1).is_one()
            True

            sage: R2.<y> = R[]
            sage: R2(x).is_one()
            False
            sage: R2(1).is_one()
            True
            sage: R2(-1).is_one()
            False
        """
        return self.degree() == 0 and self[0].is_one()

    def plot(self, xmin=None, xmax=None, *args, **kwds):
        """
        Return a plot of this polynomial.

        INPUT:


        -  ``xmin`` - float

        -  ``xmax`` - float

        -  ``*args, **kwds`` - passed to either plot or
           point


        OUTPUT: returns a graphic object.

        EXAMPLES::

            sage: x = polygen(GF(389))
            sage: plot(x^2 + 1, rgbcolor=(0,0,1))
            Graphics object consisting of 1 graphics primitive
            sage: x = polygen(QQ)
            sage: plot(x^2 + 1, rgbcolor=(1,0,0))
            Graphics object consisting of 1 graphics primitive
        """
        R = self.base_ring()
        from sage.plot.all import plot, point, line
        if R.characteristic() == 0:
            if xmin is None and xmax is None:
                (xmin, xmax) = (-1,1)
            elif xmin is None or xmax is None:
                raise AttributeError("must give both plot endpoints")
            return plot(self.__call__, (xmin, xmax), *args, **kwds)
        else:
            if R.is_finite():
                v = list(R)
                v.sort()
                w = dict([(v[i],i) for i in range(len(v))])
                z = [(i, w[self(v[i])]) for i in range(len(v))]
                return point(z, *args, **kwds)
        raise NotImplementedError("plotting of polynomials over %s not implemented"%R)

    cpdef _lmul_(self, RingElement left):
        """
        Multiply self on the left by a scalar.

        EXAMPLE::

            sage: R.<x> = ZZ[]
            sage: f = (x^3 + x + 5)
            sage: f._lmul_(7)
            7*x^3 + 7*x + 35
            sage: 7*f
            7*x^3 + 7*x + 35
        """
        # todo -- should multiply individual coefficients??
        #         that could be in derived class.
        #         Note that we are guaranteed that right is in the base ring, so this could be fast.
        if left == 0:
            return self.parent().zero()
        return self.parent()(left) * self

    cpdef _rmul_(self, RingElement right):
        """
        Multiply self on the right by a scalar.

        EXAMPLE::

            sage: R.<x> = ZZ[]
            sage: f = (x^3 + x + 5)
            sage: f._rmul_(7)
            7*x^3 + 7*x + 35
            sage: f*7
            7*x^3 + 7*x + 35
        """
        # todo -- Should multiply individual coefficients??
        #         that could be in derived class.
        #         Note that we are guaranteed that right is in the base ring, so this could be fast.
        if right == 0:
            return self.parent().zero()
        return self * self.parent()(right)

    def subs(self, *x, **kwds):
        r"""
        Identical to self(\*x).

        See the docstring for ``self.__call__``.

        EXAMPLES::

            sage: R.<x> = QQ[]
            sage: f = x^3 + x - 3
            sage: f.subs(x=5)
            127
            sage: f.subs(5)
            127
            sage: f.subs({x:2})
            7
            sage: f.subs({})
            x^3 + x - 3
            sage: f.subs({'x':2})
            Traceback (most recent call last):
            ...
            TypeError: keys do not match self's parent
        """
        if len(x) == 1 and isinstance(x[0], dict):
            g = self.parent().gen()
            if g in x[0]:
                return self(x[0][g])
            elif len(x[0]) > 0:
                raise TypeError("keys do not match self's parent")
            return self
        return self(*x, **kwds)
    substitute = subs

    def __call__(self, *args, **kwds):
        """
        Evaluate this polynomial.

        INPUT:

        - ``*args`` -- ring elements, need not be in the coefficient ring of
            the polynomial. The **first** positional argument is substituted
            for the polynomial's indeterminate. Remaining arguments, if any,
            are used **from left to right** to evaluate the coefficients.
        - ``**kwds`` -- variable name-value pairs.

        OUTPUT:

        The value of the polynomial at the point specified by the arguments.

        ALGORITHM:

        By default, use Horner's method or create a
        :class:`~sage.rings.polynomial.polynomial_compiled.CompiledPolynomialFunction`
        depending on the polynomial's degree.

        Element classes may define a method called `_evaluate_polynomial` to
        provide a specific evaluation algorithm for a given argument type.

        EXAMPLES::

            sage: R.<x> = QQ[]
            sage: f = x/2 - 5
            sage: f(3)
            -7/2
            sage: R.<x> = ZZ[]
            sage: f = (x-1)^5
            sage: f(2/3)
            -1/243

        We evaluate a polynomial over a quaternion algebra::

            sage: A.<i,j,k> = QuaternionAlgebra(QQ, -1,-1)
            sage: R.<w> = PolynomialRing(A,sparse=True)
            sage: f = i*j*w^5 - 13*i*w^2 + (i+j)*w + i
            sage: f(i+j+1)
            24 + 26*i - 10*j - 25*k
            sage: w = i+j+1; i*j*w^5 - 13*i*w^2 + (i+j)*w + i
            24 + 26*i - 10*j - 25*k

        The parent ring of the answer always "starts" with the parent of
        the object at which we are evaluating. Thus, e.g., if we input a
        matrix, we are guaranteed to get a matrix out, though the base ring
        of that matrix may change depending on the base of the polynomial
        ring. ::

            sage: R.<x> = QQ[]
            sage: f = R(2/3)
            sage: a = matrix(ZZ,2)
            sage: b = f(a); b
            [2/3   0]
            [  0 2/3]
            sage: b.parent()
            Full MatrixSpace of 2 by 2 dense matrices over Rational Field
            sage: f = R(1)
            sage: b = f(a); b
            [1 0]
            [0 1]
            sage: b.parent()
            Full MatrixSpace of 2 by 2 dense matrices over Rational Field

        ::

            sage: R.<w> = GF(17)[]
            sage: f = w^3 + 3*w +2
            sage: f(5)
            6
            sage: f(w=5)
            6
            sage: f(x=10)   # x isn't mentioned
            w^3 + 3*w + 2

        Nested polynomial ring elements can be called like multivariate
        polynomials. Note the order of the arguments::

            sage: R.<x> = QQ[]; S.<y> = R[]
            sage: f = x+y*x+y^2
            sage: f.parent()
            Univariate Polynomial Ring in y over Univariate Polynomial Ring in x over Rational Field
            sage: f(2)
            3*x + 4
            sage: f(2,4)
            16
            sage: f(y=2,x=4)
            16
            sage: f(2,x=4)
            16
            sage: f(2,x=4,z=5)
            16
            sage: f(2,4, z=10)
            16
            sage: f(y=x)
            2*x^2 + x
            sage: f(x=y)
            2*y^2 + y

        Also observe that ``f(y0, x0)`` means ``f(x=x0)(y=y0)``, not
        ``f(y=y0)(x=x0)``. The two expressions may take different values::

            sage: f(y, x)
            y^2 + x*y + x
            sage: f(y)(x)
            2*x^2 + x

        Polynomial ring elements can also, like multivariate
        polynomials, be called with an argument that is a list or
        tuple containing the values to be substituted, though it is
        perhaps more natural to just unpack the list::

            sage: f([2]) # calling with a list
            3*x + 4
            sage: f((2,)) # calling with a tuple
            3*x + 4
            sage: f(*[2]) # unpacking the list to call normally
            3*x + 4

        The following results in an element of the symbolic ring. ::

            sage: f(x=sqrt(2))
            (y + sqrt(2))*y + sqrt(2)

        ::

            sage: R.<t> = PowerSeriesRing(QQ, 't'); S.<x> = R[]
            sage: f = 1 + x*t^2 + 3*x*t^4
            sage: f(2)
            1 + 2*t^2 + 6*t^4
            sage: f(2, 1/2)
            15/8

        Some special cases are optimized. ::

            sage: R.<x> = PolynomialRing(QQ, sparse=True)
            sage: f = x^3-2*x
            sage: f(x) is f
            True
            sage: f(1/x)
            (-2*x^2 + 1)/x^3

            sage: f = x^100 + 3
            sage: f(0)
            3
            sage: parent(f(0))
            Rational Field
            sage: parent(f(Qp(5)(0)))
            5-adic Field with capped relative precision 20

        TESTS:

        The following shows that :trac:`2360` is indeed fixed. ::

            sage: R.<x,y> = ZZ[]
            sage: P.<a> = ZZ[]
            sage: e = [x^2,y^3]
            sage: f = 6*a^4
            sage: f(x)
            6*x^4
            sage: f(e)
            Traceback (most recent call last):
            ...
            TypeError: Wrong number of arguments
            sage: f(x)
            6*x^4

        The following shows that :trac:`9006` is also fixed. ::

            sage: f = ZZ['x'](1000000 * [1])
            sage: f(1)
            1000000

        The following test came up in :trac:`9051`::

            sage: Cif = ComplexIntervalField(64)
            sage: R.<x> = Cif[]
            sage: f = 2*x-1
            sage: jj = Cif(RIF(0,2))
            sage: f(jj).center(), f(jj).diameter()
            (1.00000000000000000, 4.00000000000000000)

        The following failed before the patch to :trac:`3979`

        ::

            sage: R.<x> = ZZ[]
            sage: S.<y> = R[]
            sage: g = x*y + 1
            sage: g(x=3)
            3*y + 1

        ::

            sage: Pol_x.<x> = QQ[]
            sage: Pol_xy.<y> = Pol_x[]
            sage: pol = 1000*x^2*y^2 + 100*y + 10*x + 1

            sage: pol(y, 0)
            100*y + 1

            sage: pol(~y, 0)
            (y + 100)/y

            sage: pol(y=x, x=1)
            1000*x^2 + 100*x + 11

            sage: zero = Pol_xy(0)
            sage: zero(1).parent()
            Univariate Polynomial Ring in x over Rational Field

            sage: zero = QQ['x'](0)
            sage: a = matrix(ZZ, [[1]])
            sage: zero(a).parent()
            Full MatrixSpace of 1 by 1 dense matrices over Rational Field

            sage: pol(y, x).parent() is pol(x, y).parent() is pol(y, y).parent() is Pol_xy
            True

            sage: pol(x, x).parent()
            Univariate Polynomial Ring in x over Rational Field

            sage: one = Pol_xy(1)
            sage: one(1, 1.).parent()
            Real Field with 53 bits of precision

            sage: zero = GF(2)['x'](0)
            sage: zero(1.).parent() # should raise an error
            Traceback (most recent call last):
            TypeError: unsupported operand parent(s) for '+': ...

            sage: pol(x, y, x=1)
            Traceback (most recent call last):
            ...
            TypeError: Wrong number of arguments

        AUTHORS:

        -  David Joyner (2005-04-10)

        -  William Stein (2006-01-22): change so parent is determined by the
           arithmetic

        -  William Stein (2007-03-24): fix parent being determined in the
           constant case!

        -  Robert Bradshaw (2007-04-09): add support for nested calling

        -  Tom Boothby (2007-05-01): evaluation done by
           CompiledPolynomialFunction

        -  William Stein (2007-06-03): add support for keyword arguments.

        -  Francis Clarke (2012-08-26): fix keyword substitution in the
           leading coefficient.
        """
        cdef long i
        cdef long d = self.degree()
        cdef Polynomial pol

        # Isolate the variable we are interested in, check remaining arguments

        a = kwds.pop(self.variable_name(), None)
        if args:
            if a is not None:
                raise TypeError("unsupported mix of keyword and positional arguments")
            if isinstance(args[0], (list, tuple)):
                if len(args) > 1:
                    raise TypeError("invalid arguments")
                args = args[0]
            a, args = args[0], args[1:]
        if a is None:
            a = self._parent.gen()

        cst = self[0]
        eval_coeffs = False
        if args or kwds:
            try:
                # Note that we may be calling a different implementation that
                # is more permissive about its arguments than we are.
                cst = cst(*args, **kwds)
                eval_coeffs = True
            except TypeError:
                if args: # bwd compat: nonsense *keyword* arguments are okay
                    raise TypeError("Wrong number of arguments")

        # Handle optimized special cases. The is_exact() clause should not be
        # necessary, but power series and perhaps other inexact rings use
        # is_zero() in the sense of "is zero up to the precision to which it is
        # known".

        if d <= 0 or (isinstance(a, Element) and a.parent().is_exact()
                      and a.is_zero()):
            return cst + parent(a)(0)

        # Evaluate the coefficients

        if eval_coeffs:
            pol = self.map_coefficients(lambda c: c(*args, **kwds),
                                        new_base_ring=cst.parent())
        else:
            pol = self

        # Evaluate the resulting univariate polynomial

        if parent(a) is pol._parent and a.is_gen():
            return pol

        try:
            return a._evaluate_polynomial(pol)
        except (AttributeError, NotImplementedError):
            pass

        if pol._compiled is None:
            if d < 4 or d > 50000:
                result = pol[d]
                for i in xrange(d - 1, -1, -1):
                    result = result * a + pol[i]
                return result
            pol._compiled = CompiledPolynomialFunction(pol.list())

        return pol._compiled.eval(a)

    def _compile(self):
        # For testing
        self._compiled = CompiledPolynomialFunction(self.list())
        return self._compiled

    def _get_compiled(self):
        # For testing
        return self._compiled

    def _fast_float_(self, *vars):
        """
        Returns a quickly-evaluating function on floats.

        EXAMPLE::

            sage: R.<t> = QQ[]
            sage: f = t^3-t
            sage: ff = f._fast_float_()
            sage: ff(10)
            990.0

        Horner's method is used::

            sage: f = (t+10)^3; f
            t^3 + 30*t^2 + 300*t + 1000
            sage: list(f._fast_float_())
            ['load 0', 'push 30.0', 'add', 'load 0', 'mul', 'push 300.0', 'add', 'load 0', 'mul', 'push 1000.0', 'add']

        TESTS::

            sage: f = t + 2 - t
            sage: ff = f._fast_float_()
            sage: ff(3)
            2.0
            sage: list(f._fast_float_())
            ['push 2.0']

            sage: f = t - t
            sage: ff = f._fast_float_()
            sage: ff(3)
            0.0
            sage: list(f._fast_float_())
            ['push 0.0']
        """
        from sage.ext.fast_eval import fast_float_arg, fast_float_constant
        var = self._parent._names[0]
        if len(vars) == 0:
            x = fast_float_arg(0)
        elif var in vars:
            x = fast_float_arg(list(vars).index(var))
        else:
            raise ValueError("free variable: %s" % var)
        cdef int i, d = self.degree()
        expr = x
        coeff = self[d]
        if d <= 0:
            return fast_float_constant(coeff)
        if coeff != 1:
            expr *= fast_float_constant(coeff)
        for i from d > i >= 0:
            coeff = self[i]
            if coeff:
                expr += fast_float_constant(coeff)
            if i > 0:
                expr *= x
        return expr

    def _fast_callable_(self, etb):
        r"""
        Given an ExpressionTreeBuilder, return an Expression representing
        this value.

        EXAMPLES::

            sage: from sage.ext.fast_callable import ExpressionTreeBuilder
            sage: etb = ExpressionTreeBuilder(vars=['t'])
            sage: R.<t> = QQ[]
            sage: v = R.random_element(6); v
            -t^6 - 12*t^5 + 1/2*t^4 - 1/95*t^3 - 1/2*t^2 - 4
            sage: v._fast_callable_(etb)
            add(mul(mul(add(mul(add(mul(add(mul(add(mul(v_0, -1), -12), v_0), 1/2), v_0), -1/95), v_0), -1/2), v_0), v_0), -4)

        TESTS::

            sage: R(2)._fast_callable_(etb)
            2
            sage: R(0)._fast_callable_(etb)
            0
            sage: fast_callable(R(2))(3)
            2
        """
        x = etb.var(self.variable_name())
        expr = x
        cdef int i, d = self.degree()
        coeff = self[d]
        # We handle polynomial rings like QQ['x']['y']; that gives us some
        # slowdown.  Optimize away some of that:
        if len(etb._vars) == 1:
            # OK, we're in the (very common) univariate case.
            coeff_maker = etb.constant
        else:
            # There may be variables in our coefficients...
            coeff_maker = etb.make
        if d <= 0:
            return coeff_maker(coeff)
        if coeff != 1:
            expr *= coeff_maker(coeff)
        for i from d > i >= 0:
            coeff = self[i]
            if coeff:
                expr += coeff_maker(coeff)
            if i > 0:
                expr *= x
        return expr

    cpdef int _cmp_(self, other) except -2:
        """
        Compare the two polynomials self and other.

        We order polynomials first by degree (but treating 0 as having
        degree 0), then in dictionary order starting with the
        coefficient of largest degree.

        EXAMPLES::

            sage: R.<x> = QQ['x']
            sage: 3*x^3  + 5 > 10*x^2 + 19
            True
            sage: x^2 - 2*x - 1 < x^2 - 1
            True
            sage: x^2 - 2*x - 1 > x^2 - 1
            False
            sage: x^3 - 3 > 393939393
            True

        Test comparison with zero (:trac:`18633`)::

            sage: 0 < R(1)
            True
            sage: R(-1) < 0
            True
            sage: -x < 0
            False
            sage: R(0) == R(0)
            True
        """
        cdef Py_ssize_t d1 = self.degree()
        cdef Py_ssize_t d2 = other.degree()

        # Special case constant polynomials
        if d1 <= 0 and d2 <= 0:
            return cmp(self[0], other[0])

        # For different degrees, compare the degree
        if d1 != d2:
            if d1 < d2:
                return -1
            else:
                return 1

        cdef Py_ssize_t i
        cdef int c
        for i in reversed(range(d1+1)):
            c = cmp(self[i], other[i])
            if c: return c
        return 0

    def __nonzero__(self):
        """
        EXAMPLES::

            sage: P = PolynomialRing(ZZ,'x')(0)
            sage: bool(P)
            False
            sage: P = PolynomialRing(ZZ, 'x')([1,2,3])
            sage: bool(P)
            True
        """
        return self.degree() >= 0

    def __getitem__(self, n):
        r"""
        Return the `n`-th coefficient of ``self``.

        .. WARNING::

            If `P` is a polynomial of degree `d`, then ``P[i]``
            returns `0` when `i < 0` or `i > d`.  This behaviour
            intentionally differs from that of lists: if `L` is a list
            of length `n`, then Python defines ``L[-i] = L[n - i]``
            for `0 < i \le n``.  The definition used here is more
            meaningful for polynomials, since it can be extended
            immediately to Laurent series, for example.

        EXAMPLES:

        We illustrate the difference between polynomials and lists
        when negative indices are involved::

            sage: R.<x> = QQ[]
            sage: f = x + 2
            sage: f[-1]
            0
            sage: list(f)[-1]
            1

        Slices can be used to truncate polynomials::

            sage: pol = R(range(8)); pol
            7*x^7 + 6*x^6 + 5*x^5 + 4*x^4 + 3*x^3 + 2*x^2 + x
            sage: pol[:6]
            5*x^5 + 4*x^4 + 3*x^3 + 2*x^2 + x

        Any other kind of slicing is deprecated or an error, see
        :trac:`18940`::

            sage: f[1:3]
            doctest:...: DeprecationWarning: polynomial slicing with a start index is deprecated, use list() and slice the resulting list instead
            See http://trac.sagemath.org/18940 for details.
            x
            sage: f[1:3:2]
            Traceback (most recent call last):
            ...
            NotImplementedError: polynomial slicing with a step is not defined
        """
        cdef Py_ssize_t d = self.degree() + 1
        if isinstance(n, slice):
            start, stop, step = n.start, n.stop, n.step
            if step is not None:
                raise NotImplementedError("polynomial slicing with a step is not defined")
            if start is None:
                start = 0
            else:
                if start < 0:
                    start = 0
                from sage.misc.superseded import deprecation
                deprecation(18940, "polynomial slicing with a start index is deprecated, use list() and slice the resulting list instead")
            if stop is None or stop > d:
                stop = d
            values = ([self.base_ring().zero()] * start
                      + [self.get_unsafe(i) for i in xrange(start, stop)])
            return self.parent()(values)

        cdef long k = pyobject_to_long(n)
        if k < 0 or k >= d:
            return self.base_ring().zero()
        return self.get_unsafe(k)

    cdef get_unsafe(self, Py_ssize_t i):
        """
        Return the `i`-th coefficient of ``self``.

        Used as building block for a generic :meth:`__getitem__`.
        """
        raise NotImplementedError

    def __iter__(self):
        """
        EXAMPLE::

            sage: P = PolynomialRing(ZZ, 'x')([1,2,3])
            sage: [y for y in iter(P)]
            [1, 2, 3]
        """
        return iter(self.list())

    def _cache_key(self):
        """
        Return a hashable key which identifies this element.

        EXAMPLES::

            sage: K.<u> = Qq(4)
            sage: R.<x> = K[]
            sage: f = x
            sage: hash(f)
            Traceback (most recent call last):
            ...
            TypeError: unhashable type: 'sage.rings.padics.qadic_flint_CR.qAdicCappedRelativeElement'
            sage: f._cache_key()
            (Univariate Polynomial Ring in x over Unramified Extension of 2-adic Field with capped relative precision 20 in u defined by (1 + O(2^20))*x^2 + (1 + O(2^20))*x + (1 + O(2^20)),
             0,
             1 + O(2^20))
            sage: @cached_function
            ....: def foo(t): return t
            ....:
            sage: foo(x)
            (1 + O(2^20))*x
        """
        return (self._parent,) + tuple(self)

    def __hash__(self):
        return self._hash_c()

    cdef long _hash_c(self) except -1:
        """
        This hash incorporates the variable name in an effort to respect
        the obvious inclusions into multi-variable polynomial rings.

        The tuple algorithm is borrowed from
        http://effbot.org/zone/python-hash.htm.

        EXAMPLES::

            sage: R.<x>=ZZ[]
            sage: hash(R(1))==hash(1)  # respect inclusions of the integers
            True
            sage: hash(R.0)==hash(FractionField(R).0)  # respect inclusions into the fraction field
            True
            sage: R.<x>=QQ[]
            sage: hash(R(1/2))==hash(1/2)  # respect inclusions of the rationals
            True
            sage: hash(R.0)==hash(FractionField(R).0)  # respect inclusions into the fraction field
            True
            sage: R.<x>=IntegerModRing(11)[]
            sage: hash(R.0)==hash(FractionField(R).0)  # respect inclusions into the fraction field
            True

        TESTS:

        Verify that :trac:`16251` has been resolved, i.e., polynomials with
        unhashable coefficients are unhashable::

            sage: K.<a> = Qq(9)
            sage: R.<t> = K[]
            sage: hash(t)
            Traceback (most recent call last):
            ...
            TypeError: unhashable type: 'sage.rings.padics.qadic_flint_CR.qAdicCappedRelativeElement'

        """
        cdef long result = 0 # store it in a c-int and just let the overflowing additions wrap
        cdef long result_mon
        cdef long c_hash
        cdef long var_name_hash
        cdef int i
        for i from 0<= i <= self.degree():
            if i == 1:
                # we delay the hashing until now to not waste it on a constant poly
                var_name_hash = hash(self._parent._names[0])
            # I'm assuming (incorrectly) that hashes of zero indicate that the element is 0.
            # This assumption is not true, but I think it is true enough for the purposes and it
            # it allows us to write fast code that omits terms with 0 coefficients.  This is
            # important if we want to maintain the '==' relationship with sparse polys.
            c_hash = hash(self[i])
            if c_hash != 0:
                if i == 0:
                    result += c_hash
                else:
                    # Hash (self[i], generator, i) as a tuple according to the algorithm.
                    result_mon = c_hash
                    result_mon = (1000003 * result_mon) ^ var_name_hash
                    result_mon = (1000003 * result_mon) ^ i
                    result += result_mon
        if result == -1:
            return -2
        return result

    def __float__(self):
        """
        EXAMPLE::

            sage: P = PolynomialRing(ZZ, 'x')([1])
            sage: float(P)
            1.0
        """
        if self.degree() > 0:
            raise TypeError("cannot coerce nonconstant polynomial to float")
        return float(self[0])

    def __int__(self):
        """
        EXAMPLE::

            sage: P = PolynomialRing(ZZ, 'x')([3])
            sage: int(P)
            3
        """
        if self.degree() > 0:
            raise TypeError("cannot coerce nonconstant polynomial to int")
        return int(self[0])

    def _im_gens_(self, codomain, im_gens):
        """
        EXAMPLES::

            sage: R.<x> = ZZ[]
            sage: H = Hom(R, QQ); H
            Set of Homomorphisms from Univariate Polynomial Ring in x over Integer Ring to Rational Field
            sage: f = H([5]); f
            Ring morphism:
              From: Univariate Polynomial Ring in x over Integer Ring
              To:   Rational Field
              Defn: x |--> 5
            sage: f(x)
            5
            sage: f(x^2 + 3)
            28
        """
        a = im_gens[0]
        P = a.parent()
        d = self.degree()
        result = P._coerce_(self[d])
        i = d - 1
        while i >= 0:
            result = result * a + P._coerce_(self[i])
            i -= 1
        return result

    def _integer_(self, ZZ):
        r"""
        EXAMPLES::

            sage: k = GF(47)
            sage: R.<x> = PolynomialRing(k)
            sage: ZZ(R(45))
            45
            sage: ZZ(3*x + 45)
            Traceback (most recent call last):
            ...
            TypeError: cannot coerce nonconstant polynomial
        """
        if self.degree() > 0:
            raise TypeError("cannot coerce nonconstant polynomial")
        return ZZ(self[0])

    def _rational_(self):
        r"""
        EXAMPLES::

            sage: R.<x> = PolynomialRing(QQ)
            sage: QQ(R(45/4))
            45/4
            sage: QQ(3*x + 45)
            Traceback (most recent call last):
            ...
            TypeError: not a constant polynomial
        """
        if self.degree() > 0:
            raise TypeError("not a constant polynomial")
        return sage.rings.rational.Rational(self[0])

    def _symbolic_(self, R):
        """
        EXAMPLES::

            sage: R.<x> = QQ[]
            sage: f = x^3 + x
            sage: g = f._symbolic_(SR); g
            x^3 + x
            sage: g(x=2)
            10

            sage: g = SR(f)
            sage: g(x=2)
            10

        The polynomial does not have to be over a field of
        characteristic 0::

            sage: R.<w> = GF(7)[]
            sage: f = SR(2*w^3 + 1); f
            2*w^3 + 1
            sage: f.variables()
            (w,)
        """
        d = dict([(repr(g), R.var(g)) for g in self.parent().gens()])
        return self.subs(**d)

    def __invert__(self):
        """
        EXAMPLES::

            sage: R.<x> = QQ[]
            sage: f = x - 90283
            sage: f.__invert__()
            1/(x - 90283)
            sage: ~f
            1/(x - 90283)
        """
        return self.parent().one()/self

    def inverse_of_unit(self):
        """
        EXAMPLES::

            sage: R.<x> = QQ[]
            sage: f = x - 90283
            sage: f.inverse_of_unit()
            Traceback (most recent call last):
            ...
            ValueError: self is not a unit.
            sage: f = R(-90283); g = f.inverse_of_unit(); g
            -1/90283
            sage: parent(g)
            Univariate Polynomial Ring in x over Rational Field
        """
        if self.degree() > 0:
            if not self.is_unit():
                raise ValueError("self is not a unit.")
            else:
                raise NotImplementedError("polynomial inversion over non-integral domains not implemented")
        return self.parent()(~(self[0]))

    def inverse_mod(a, m):
        """
        Inverts the polynomial a with respect to m, or raises a ValueError
        if no such inverse exists. The parameter m may be either a single
        polynomial or an ideal (for consistency with inverse_mod in other
        rings).

        .. SEEALSO::

            If you are only interested in the inverse modulo a monomial `x^k`
            then you might use the specialized method
            :meth:`inverse_series_trunc` which is much faster.

        EXAMPLES::

            sage: S.<t> = QQ[]
            sage: f = inverse_mod(t^2 + 1, t^3 + 1); f
            -1/2*t^2 - 1/2*t + 1/2
            sage: f * (t^2 + 1) % (t^3 + 1)
            1
            sage: f = t.inverse_mod((t+1)^7); f
            -t^6 - 7*t^5 - 21*t^4 - 35*t^3 - 35*t^2 - 21*t - 7
            sage: (f * t) + (t+1)^7
            1
            sage: t.inverse_mod(S.ideal((t + 1)^7)) == f
            True

        This also works over inexact rings, but note that due to rounding
        error the product may not always exactly equal the constant
        polynomial 1 and have extra terms with coefficients close to zero. ::

            sage: R.<x> = RDF[]
            sage: epsilon = RDF(1).ulp()*50   # Allow an error of up to 50 ulp
            sage: f = inverse_mod(x^2 + 1, x^5 + x + 1); f  # abs tol 1e-14
            0.4*x^4 - 0.2*x^3 - 0.4*x^2 + 0.2*x + 0.8
            sage: poly = f * (x^2 + 1) % (x^5 + x + 1)
            sage: # Remove noisy zero terms:
            sage: parent(poly)([ 0.0 if abs(c)<=epsilon else c for c in poly.coefficients(sparse=False) ])
            1.0
            sage: f = inverse_mod(x^3 - x + 1, x - 2); f
            0.14285714285714285
            sage: f * (x^3 - x + 1) % (x - 2)
            1.0
            sage: g = 5*x^3+x-7; m = x^4-12*x+13; f = inverse_mod(g, m); f
            -0.0319636125...*x^3 - 0.0383269759...*x^2 - 0.0463050900...*x + 0.346479687...
            sage: poly = f*g % m
            sage: # Remove noisy zero terms:
            sage: parent(poly)([ 0.0 if abs(c)<=epsilon else c for c in poly.coefficients(sparse=False) ])  # abs tol 1e-14
            1.0000000000000004

        ALGORITHM: Solve the system as + mt = 1, returning s as the inverse
        of a mod m.

        Uses the Euclidean algorithm for exact rings, and solves a linear
        system for the coefficients of s and t for inexact rings (as the
        Euclidean algorithm may not converge in that case).

        AUTHORS:

        - Robert Bradshaw (2007-05-31)
        """
        from sage.rings.ideal import is_Ideal
        if is_Ideal(m):
            v = m.gens_reduced()
            if len(v) > 1:
                raise NotImplementedError("Don't know how to invert modulo non-principal ideal %s" % m)
            m = v[0]
        if m.degree() == 1 and m[1].is_unit():
            # a(x) mod (x-r) = a(r)
            r = -m[0]
            if not m[1].is_one():
                r *= m.base_ring()(~m[1])
            u = a(r)
            if u.is_unit():
                return a.parent()(~u)
        if a.parent().is_exact():
            # use xgcd
            g, s, _ = a.xgcd(m)
            if g == 1:
                return s
            elif g.is_unit():
                return g.inverse_of_unit() * s
            else:
                raise ValueError("Impossible inverse modulo")
        else:
            # xgcd may not converge for inexact rings.
            # Instead solve for the coefficients of
            # s (degree n-1) and t (degree n-2) in
            #               as + mt = 1
            # as a linear system.
            from sage.matrix.constructor import matrix
            from sage.modules.free_module_element import vector
            a %= m
            n = m.degree()
            R = a.parent().base_ring()
            M = matrix(R, 2*n-1)
            # a_i s_j x^{i+j} terms
            for i in range(n):
                for j in range(n):
                    M[i+j, j] = a[i]
            # m_i t_j x^{i+j} terms
            for i in range(n+1):
                for j in range(n-1):
                    M[i+j, j+n] = m[i]
            v = vector(R, [R.one()] + [R.zero()]*(2*n-2)) # the constant polynomial 1
            if M.is_invertible():
                x = M.solve_right(v) # there has to be a better way to solve
                return a.parent()(list(x)[0:n])
            else:
                raise ValueError("Impossible inverse modulo")

    cpdef Polynomial inverse_series_trunc(self, long prec):
        r"""
        Return a polynomial approximation of precision ``prec`` of the inverse
        series of this polynomial.

        .. SEEALSO::

            The method :meth:`inverse_mod` allows more generally to invert this
            polynomial with respect to any ideal.

        EXAMPLES::

            sage: x = polygen(ZZ)
            sage: s = (1+x).inverse_series_trunc(5)
            sage: s
            x^4 - x^3 + x^2 - x + 1
            sage: s * (1+x)
            x^5 + 1

        Note that the constant coefficient needs to be a unit::

            sage: ZZx.<x> = ZZ[]
            sage: ZZxy.<y> = ZZx[]
            sage: (1+x + y**2).inverse_series_trunc(4)
            Traceback (most recent call last):
            ...
            ValueError: constant term x + 1 is not a unit
            sage: (1+x + y**2).change_ring(ZZx.fraction_field()).inverse_series_trunc(4)
            (-1/(x^2 + 2*x + 1))*y^2 + 1/(x + 1)

        The method works over any polynomial ring::

            sage: R = Zmod(4)
            sage: Rx.<x> = R[]
            sage: Rxy.<y> = Rx[]

            sage: p = 1 + (1+2*x)*y + x**2*y**4
            sage: q = p.inverse_series_trunc(10)
            sage: (p*q).truncate(11)
            (2*x^4 + 3*x^2 + 3)*y^10 + 1

        Even noncommutative ones::

            sage: M = MatrixSpace(ZZ,2)
            sage: x = polygen(M)
            sage: p = M([1,2,3,4])*x^3 + M([-1,0,0,1])*x^2 + M([1,3,-1,0])*x + M.one()
            sage: q = p.inverse_series_trunc(5)
            sage: (p*q).truncate(5) == M.one()
            True
            sage: q = p.inverse_series_trunc(13)
            sage: (p*q).truncate(13) == M.one()
            True

        TESTS::

            sage: x = polygen(ZZ['a','b'])
            sage: (x+1).inverse_series_trunc(0)
            Traceback (most recent call last):
            ...
            ValueError: the precision must be positive, got 0

        AUTHORS:

        - David Harvey (2006-09-09): Newton's method implementation for power
          series

        - Vincent Delecroix (2014-2015): move the implementation directly in
          polynomial
        """
        if prec <= 0:
            raise ValueError("the precision must be positive, got {}".format(prec))

        if not self[0].is_unit():
            raise ValueError("constant term {} is not a unit".format(self[0]))

        R = self._parent
        A = R.base_ring()
        try:
            first_coeff = self[0].inverse_of_unit()
        except AttributeError:
            first_coeff = A(~self[0])

        current = R(first_coeff)
        for next_prec in sage.misc.misc.newton_method_sizes(prec)[1:]:
            z = current._mul_trunc_(self, next_prec)._mul_trunc_(current, next_prec)
            current = current + current - z
        return current

    def __long__(self):
        """
        EXAMPLES::

            sage: R.<x> = ZZ[]
            sage: f = x - 902384
            sage: long(f)
            Traceback (most recent call last):
            ...
            TypeError: cannot coerce nonconstant polynomial to long
            sage: long(R(939392920202))
            939392920202L
        """
        if self.degree() > 0:
            raise TypeError("cannot coerce nonconstant polynomial to long")
        return long(self[0])

    cpdef _mul_(self, right):
        """
        EXAMPLES::

            sage: R.<x> = ZZ[]
            sage: (x - 4)*(x^2 - 8*x + 16)
            x^3 - 12*x^2 + 48*x - 64
            sage: C.<t> = PowerSeriesRing(ZZ)
            sage: D.<s> = PolynomialRing(C)
            sage: z = (1 + O(t)) + t*s^2
            sage: z*z
            t^2*s^4 + (2*t + O(t^2))*s^2 + 1 + O(t)

            ## More examples from trac 2943, added by Kiran S. Kedlaya 2 Dec 09
            sage: C.<t> = PowerSeriesRing(Integers())
            sage: D.<s> = PolynomialRing(C)
            sage: z = 1 + (t + O(t^2))*s + (t^2 + O(t^3))*s^2
            sage: z*z
            (t^4 + O(t^5))*s^4 + (2*t^3 + O(t^4))*s^3 + (3*t^2 + O(t^3))*s^2 + (2*t + O(t^2))*s + 1
        """
        if not self or not right:
            return self._parent.zero()

        if self._parent.is_exact():
            return self._mul_karatsuba(right)
        else:
            return self._mul_generic(right)

    def _mul_trunc(self, right, n):
        r"""
        Deprecated alias of :meth:`_mul_trunc_`

        EXAMPLES::

            sage: R.<x> = QQ[]
            sage: x._mul_trunc(x, 1)
            doctest:...: DeprecationWarning: _mul_trunc is deprecated, use
            _mul_trunc_ instead
            See http://trac.sagemath.org/18420 for details.
            0
        """
        deprecation(18420, "_mul_trunc is deprecated, use _mul_trunc_ instead")
        return self._mul_trunc_(right, n)

    cpdef Polynomial _mul_trunc_(self, Polynomial right, long n):
        r"""
        Return the truncated multiplication of two polynomials up to ``n``.

        This is the default implementation that does the multiplication and then
        truncate! There are custom implementations in several subclasses:

        - :meth:`on dense polynomial over integers (via FLINT) <sage.rings.polynomial.polynomial_integer_dense_flint.Polynomial_integer_dense_flint._mul_trunc_>`

        - :meth:`on dense polynomial over Z/nZ (via FLINT)
          <sage.rings.polynomial.polynomial_zmod_flint.Polynomial_zmod_flint._mul_trunc_>`

        - :meth:`on dense rational polynomial (via FLINT)
          <sage.rings.polynomial.polynomial_rational_flint.Polynomial_rational_flint._mul_trunc_>`

        - :meth:`on dense polynomial on Z/nZ (via NTL)
          <sage.rings.polynomial.polynomial_modn_dense_ntl.Polynomial_dense_modn_ntl_zz._mul_trunc_>`

        EXAMPLES::

            sage: R = QQ['x']['y']
            sage: y = R.gen()
            sage: x = R.base_ring().gen()
            sage: p1 = 1 - x*y + 2*y**3
            sage: p2 = -1/3 + y**5
            sage: p1._mul_trunc_(p2, 5)
            -2/3*y^3 + 1/3*x*y - 1/3

        .. TODO::

            implement a generic truncated Karatsuba and use it here.
        """
        return (self.truncate(n) * right.truncate(n)).truncate(n)

    def multiplication_trunc(self, other, n):
        r"""
        Truncated multiplication

        EXAMPLES::

            sage: R.<x> = ZZ[]
            sage: (x^10 + 5*x^5 + x^2 - 3).multiplication_trunc(x^7 - 3*x^3 + 1, 11)
            x^10 + x^9 - 15*x^8 - 3*x^7 + 2*x^5 + 9*x^3 + x^2 - 3

        Check that coercion is working::

            sage: R2 = QQ['x']
            sage: x2 = R2.gen()
            sage: p1 = (x^3 + 1).multiplication_trunc(x2^3 - 2, 5); p1
            -x^3 - 2
            sage: p2 = (x2^3 + 1).multiplication_trunc(x^3 - 2, 5); p2
            -x^3 - 2
            sage: parent(p1) == parent(p2) == R2
            True
        """
        if not have_same_parent(self, other):
            self, other = coercion_model.canonical_coercion(self, other)
        return self._mul_trunc_(other, pyobject_to_long(n))

    def square(self):
        """
        Returns the square of this polynomial.

        TODO:

        - This is just a placeholder; for now it just uses ordinary
          multiplication. But generally speaking, squaring is faster than
          ordinary multiplication, and it's frequently used, so subclasses
          may choose to provide a specialised squaring routine.

        - Perhaps this even belongs at a lower level? RingElement or
          something?

        AUTHORS:

        - David Harvey (2006-09-09)

        EXAMPLES::

            sage: R.<x> = QQ[]
            sage: f = x^3 + 1
            sage: f.square()
            x^6 + 2*x^3 + 1
            sage: f*f
            x^6 + 2*x^3 + 1
        """
        return self * self

    def squarefree_decomposition(self):
        """
        Return the square-free decomposition of this polynomial.  This is a
        partial factorization into square-free, coprime polynomials.

        EXAMPLES::

            sage: x = polygen(QQ)
            sage: p = 37 * (x-1)^3 * (x-2)^3 * (x-1/3)^7 * (x-3/7)
            sage: p.squarefree_decomposition()
            (37*x - 111/7) * (x^2 - 3*x + 2)^3 * (x - 1/3)^7
            sage: p = 37 * (x-2/3)^2
            sage: p.squarefree_decomposition()
            (37) * (x - 2/3)^2
            sage: x = polygen(GF(3))
            sage: x.squarefree_decomposition()
            x
            sage: f = QQbar['x'](1)
            sage: f.squarefree_decomposition()
            1

        """
        if self.degree() < 0:
            raise ValueError("square-free decomposition not defined for zero polynomial")
        if hasattr(self.base_ring(),'_squarefree_decomposition_univariate_polynomial'):
            return self.base_ring()._squarefree_decomposition_univariate_polynomial(self)
        raise NotImplementedError("square-free decomposition not implemented for this polynomial")

    def is_nth_power(self, n):
        """
        Return whether this polynomial is an ``n``-th power in the polynomial ring.

        INPUT:

        - ``n`` -- an integer

        EXAMPLES::

            sage: R.<x> = GF(3)[]
            sage: x.is_nth_power(1)
            True
            sage: x.is_nth_power(2)
            False
            sage: (x^3).is_nth_power(3)
            True
            sage: R(2).is_nth_power(-3)
            True

        """
        n = ZZ(n)
        if n == 0:
            return self.is_one()
        if n < 0:
            return self.is_unit() and (~(self[0])).is_nth_power(-n)
        return all([n.divides(e) for e in self.exponents()]) and all([c.is_nth_power(n) for c in self.coefficients()])

    def nth_root(self, n):
        """
        Return a polynomial ``a`` such that this polynomial equals ``a^n``.

        INPUT:

        - ``n`` -- an integer

        EXAMPLES::

            sage: R.<x> = GF(3)[]
            sage: x.nth_root(1)
            x
            sage: x.nth_root(2)
            Traceback (most recent call last):
            ...
            ValueError: element is not an n-th power.
            sage: (x^3).nth_root(3)
            x
            sage: R(2).nth_root(-3)
            2


        """
        if not self.is_nth_power(n):
            raise ValueError("element is not an n-th power.")

        if n < 0:
            return self.parent()(self[0].nth_root(-n))
        if n == 0:
            return self.parent().one()
        return self.parent()([c.nth_root(n) for c in self.coeffs()[::n]])

    def pth_root(self):
        p = self.parent().characteristic()
        if p==0:
            raise ValueError
        return self.nth_root(p)


    def is_square(self, root=False):
        """
        Returns whether or not polynomial is square. If the optional
        argument ``root`` is set to ``True``, then also returns the square root
        (or ``None``, if the polynomial is not square).

        INPUT:

        -  ``root`` - whether or not to also return a square
           root (default: ``False``)

        OUTPUT:

        -  ``bool`` - whether or not a square

        -  ``root`` - (optional) an actual square root if
           found, and ``None`` otherwise.

        EXAMPLES::

            sage: R.<x> = PolynomialRing(QQ)
            sage: (x^2 + 2*x + 1).is_square()
            True
            sage: (x^4 + 2*x^3 - x^2 - 2*x + 1).is_square(root=True)
            (True, x^2 + x - 1)

            sage: f = 12*(x+1)^2 * (x+3)^2
            sage: f.is_square()
            False
            sage: f.is_square(root=True)
            (False, None)

            sage: h = f/3; h
            4*x^4 + 32*x^3 + 88*x^2 + 96*x + 36
            sage: h.is_square(root=True)
            (True, 2*x^2 + 8*x + 6)

            sage: S.<y> = PolynomialRing(RR)
            sage: g = 12*(y+1)^2 * (y+3)^2

            sage: g.is_square()
            True

        TESTS:

        Make sure :trac:`9093` is fixed::

            sage: R(1).is_square()
            True
            sage: R(4/9).is_square(root=True)
            (True, 2/3)
            sage: R(-1/3).is_square()
            False
            sage: R(0).is_square()
            True
        """
        if self.is_zero():
            return (True, self) if root else True

        try:
            f = self.squarefree_decomposition()
        except NotImplementedError:
            f = self.factor()

        u = self.parent().base_ring()(f.unit())

        if all(a[1] % 2 == 0 for a in f) and u.is_square():
            g = u.sqrt()
            for a in f:
                g *= a[0] ** (a[1] / 2)
            return (True, g) if root else True
        else:
            return (False, None) if root else False

    def any_root(self, ring=None, degree=None, assume_squarefree=False):
        """
        Return a root of this polynomial in the given ring.

        INPUT:

        - ``ring`` -- The ring in which a root is sought.  By default
          this is the coefficient ring.

        - ``degree`` (None or nonzero integer) -- Used for polynomials
          over finite fields.  Returns a root of degree
          ``abs(degree)`` over the ground field.  If negative, also
          assumes that all factors of this polynomial are of degree
          ``abs(degree)``.  If None, returns a root of minimal degree
          contained within the given ring.

        - ``assume_squarefree`` (bool) -- Used for polynomials over
          finite fields.  If True, this polynomial is assumed to be
          squarefree.

        EXAMPLES::

            sage: R.<x> = GF(11)[]
            sage: f = 7*x^7 + 8*x^6 + 4*x^5 + x^4 + 6*x^3 + 10*x^2 + 8*x + 5
            sage: f.any_root()
            2
            sage: f.factor()
            (7) * (x + 9) * (x^6 + 10*x^4 + 6*x^3 + 5*x^2 + 2*x + 2)
            sage: f = x^6 + 10*x^4 + 6*x^3 + 5*x^2 + 2*x + 2
            sage: f.any_root(GF(11^6, 'a'))
            a^5 + a^4 + 7*a^3 + 2*a^2 + 10*a
            sage: sorted(f.roots(GF(11^6, 'a')))
            [(10*a^5 + 2*a^4 + 8*a^3 + 9*a^2 + a, 1), (a^5 + a^4 + 7*a^3 + 2*a^2 + 10*a, 1), (9*a^5 + 5*a^4 + 10*a^3 + 8*a^2 + 3*a + 1, 1), (2*a^5 + 8*a^4 + 3*a^3 + 6*a + 2, 1), (a^5 + 3*a^4 + 8*a^3 + 2*a^2 + 3*a + 4, 1), (10*a^5 + 3*a^4 + 8*a^3 + a^2 + 10*a + 4, 1)]
            sage: f.any_root(GF(11^6, 'a'))
            a^5 + a^4 + 7*a^3 + 2*a^2 + 10*a

            sage: g = (x-1)*(x^2 + 3*x + 9) * (x^5 + 5*x^4 + 8*x^3 + 5*x^2 + 3*x + 5)
            sage: g.any_root(ring=GF(11^10, 'b'), degree=1)
            1
            sage: g.any_root(ring=GF(11^10, 'b'), degree=2)
            5*b^9 + 4*b^7 + 4*b^6 + 8*b^5 + 10*b^2 + 10*b + 5
            sage: g.any_root(ring=GF(11^10, 'b'), degree=5)
            5*b^9 + b^8 + 3*b^7 + 2*b^6 + b^5 + 4*b^4 + 3*b^3 + 7*b^2 + 10*b

        TESTS::

            sage: R.<x> = GF(5)[]
            sage: K.<a> = GF(5^12)
            sage: for _ in range(40):
            ....:     f = R.random_element(degree=4)
            ....:     assert f(f.any_root(K)) == 0

        Check that our Cantor-Zassenhaus implementation does not loop
        over finite fields of even characteristic (see :trac:`16162`)::

            sage: K.<a> = GF(2**8)
            sage: x = polygen(K)
            sage: (x**2+x+1).any_root() # used to loop
            Traceback (most recent call last):
            ...
            ValueError: no roots A 1
            sage: (x**2+a+1).any_root()
            a^7 + a^2

        Also check that such computations can be interrupted::

            sage: K.<a> = GF(2^8)
            sage: x = polygen(K)
            sage: pol = x^1000000 + x + a
            sage: alarm(0.5); pol.any_root()
            Traceback (most recent call last):
            ...
            AlarmInterrupt

        Check root computation over large finite fields::

            sage: K.<a> = GF(2**50)
            sage: x = polygen(K)
            sage: (x**10+x+a).any_root()
            a^49 + a^47 + a^44 + a^42 + a^41 + a^39 + a^38 + a^37 + a^36 + a^34 + a^33 + a^29 + a^27 + a^26 + a^25 + a^23 + a^18 + a^13 + a^7 + a^5 + a^4 + a^3 + a^2 + a
            sage: K.<a> = GF(2**150)
            sage: x = polygen(K)
            sage: (x**10+x+a).any_root()
            a^149 + a^148 + a^146 + a^144 + a^143 + a^140 + a^138 + a^136 + a^134 + a^132 + a^131 + a^130 + a^129 + a^127 + a^123 + a^120 + a^118 + a^114 + a^113 + a^112 + a^111 + a^108 + a^104 + a^103 + a^102 + a^99 + a^98 + a^94 + a^91 + a^90 + a^88 + a^79 + a^78 + a^75 + a^73 + a^72 + a^67 + a^65 + a^64 + a^63 + a^62 + a^61 + a^59 + a^57 + a^52 + a^50 + a^48 + a^47 + a^46 + a^45 + a^43 + a^41 + a^39 + a^37 + a^34 + a^31 + a^29 + a^27 + a^25 + a^23 + a^22 + a^20 + a^18 + a^16 + a^14 + a^11 + a^10 + a^8 + a^6 + a^5 + a^4 + a + 1
        """
        if self.base_ring().is_finite() and self.base_ring().is_field():
            if self.degree() < 0:
                return ring(0)
            if self.degree() == 0:
                raise ValueError("no roots A %s" % self)
            if not assume_squarefree:
                SFD = self.squarefree_decomposition()
                SFD.sort()
                for f, e in SFD:
                    try:
                        return f.any_root(ring, degree, True)
                    except ValueError:
                        pass
            if self.degree() == 1 and (degree is None or degree == 1):
                if ring is None:
                    return -self[0]/self[1]
                else:
                    return ring(-self[0]/self[1])
            q = self.base_ring().order()
            if ring is None:
                allowed_deg_mult = Integer(1)
            else:
                if not (self.base_ring().is_field() and self.base_ring().is_finite()):
                    raise NotImplementedError
                if ring.characteristic() != self.base_ring().characteristic():
                    raise ValueError("ring must be an extension of the base ring")
                if not (ring.is_field() and ring.is_finite()):
                    raise NotImplementedError
                allowed_deg_mult = Integer(ring.factored_order()[0][1]) # generally it will be the quotient of this by the degree of the base ring.
            if degree is None:
                x = self.parent().gen()
                if allowed_deg_mult == 1:
                    xq = pow(x,q,self)
                    self = self.gcd(xq-x)
                    degree = -1
                    if self.degree() == 0:
                        raise ValueError("no roots B %s" % self)
                else:
                    xq = x
                    d = Integer(0)
                    while True:
                        # one pass for roots that actually lie within ring.
                        e = self.degree()
                        if 2*d+2 > e:
                            # this polynomial has no factors dividing allowed_deg_mult
                            if allowed_deg_mult % e == 0:
                                degree = -e
                            break
                        while d < allowed_deg_mult:
                            d = d+1
                            xq = pow(xq,q,self)
                            if d.divides(allowed_deg_mult):
                                break
                        A = self.gcd(xq-x)
                        if A != 1:
                            self = A
                            degree = -d
                            break
                        if d == allowed_deg_mult:
                            break
                    if degree is None:
                        if allowed_deg_mult == 1:
                            raise ValueError("no roots C %s" % self)
                        xq = x
                        d = Integer(0)
                        while True:
                            # now another for roots that will lie in an extension.
                            e = self.degree()
                            if 2*d+2 > e:
                                # this polynomial is irreducible.
                                degree = -e
                                break
                            while True:
                                # we waste a little effort here in computing the xq again.
                                d = d+1
                                xq = pow(xq,q,self)
                                if allowed_deg_mult.divides(d):
                                    break
                            A = self.gcd(xq-x)
                            if A != 1:
                                self = A
                                degree = -d
                                break
            if degree == 0:
                raise ValueError("degree should be nonzero")
            R = self.parent()
            x = R.gen()
            if degree > 0:
                xq = x
                d = 0
                while True:
                    e = self.degree()
                    if 2*d > e:
                        if degree != e:
                            raise ValueError("no roots D %s" % self)
                        break
                    d = d+1
                    xq = pow(xq,q,self)
                    if d == degree:
                        break
                    A = self.gcd(xq-x)
                    if A != 1:
                        self = self // A
                if d == degree:
                    self = self.gcd(xq-x)
                    if self.degree() == 0:
                        raise ValueError("no roots E %s" % self)
            else:
                degree = -degree
            if ring is None:
                if degree == 1:
                    ring = self.base_ring()
                else:
                    ring = self.base_ring().extension(degree) # this won't work yet.
            # now self has only roots of degree ``degree``.
            # for now, we only implement the Cantor-Zassenhaus split
            k = self.degree() // degree
            if k == 1:
                try:
                    return self.roots(ring, multiplicities=False)[0] # is there something better to do here?
                except IndexError:
                    raise ValueError("no roots F %s" % self)
            if q % 2 == 0:
                while True:
                    T = R.random_element(2*degree-1)
                    if T == 0:
                        continue
                    T = T.monic()
                    C = T
                    for i in range(degree-1):
                        C = T + pow(C,q,self)
                    h = self.gcd(C)
                    hd = h.degree()
                    if hd != 0 or hd != self.degree():
                        if 2*hd <= self.degree():
                            return h.any_root(ring, -degree, True)
                        else:
                            return (self//h).any_root(ring, -degree, True)
            else:
                while True:
                    T = R.random_element(2*degree-1)
                    if T == 0:
                        continue
                    T = T.monic()
                    h = self.gcd(pow(T, Integer((q**degree-1)/2), self)-1)
                    hd = h.degree()
                    if hd != 0 and hd != self.degree():
                        if 2*hd <= self.degree():
                            return h.any_root(ring, -degree, True)
                        else:
                            return (self//h).any_root(ring, -degree, True)
        else:
            return self.roots(ring=ring, multiplicities=False)[0]


    def __truediv__(self, right):
        """
        EXAMPLES::

            sage: x = QQ['x'].0
            sage: f = (x^3 + 5)/3; f
            1/3*x^3 + 5/3
            sage: f.parent()
            Univariate Polynomial Ring in x over Rational Field

        If we do the same over `\ZZ` the result is in the
        polynomial ring over `\QQ`.

        ::

            sage: x  = ZZ['x'].0
            sage: f = (x^3 + 5)/3; f
            1/3*x^3 + 5/3
            sage: f.parent()
            Univariate Polynomial Ring in x over Rational Field

        Divides can make elements of the fraction field::

            sage: R.<x> = QQ['x']
            sage: f = x^3 + 5
            sage: g = R(3)
            sage: h = f/g; h
            1/3*x^3 + 5/3
            sage: h.parent()
            Fraction Field of Univariate Polynomial Ring in x over Rational Field

        This is another example over a non-prime finite field (submitted by
        a student of Jon Hanke). It illustrates cancellation between the
        numerator and denominator over a non-prime finite field.

        ::

            sage: R.<x> = PolynomialRing(GF(5^2, 'a'), 'x')
            sage: f = x^3 + 4*x
            sage: f / (x - 1)
            x^2 + x

        Be careful about coercions (this used to be broken)::

            sage: R.<x> = ZZ['x']
            sage: f = x / Mod(2,5); f
            3*x
            sage: f.parent()
            Univariate Polynomial Ring in x over Ring of integers modulo 5

        TESTS:

        Check that :trac:`12217` is fixed::

            sage: P.<x> = GF(5)[]
            sage: x/0
            Traceback (most recent call last):
            ...
            ZeroDivisionError: Inverse does not exist.

            sage: P.<x> = GF(25, 'a')[]
            sage: x/5
            Traceback (most recent call last):
            ...
            ZeroDivisionError: division by zero in Finite Field in a of size 5^2
        """
        try:
            if not isinstance(right, Element) or right.parent() != self.parent():
                R = self.parent().base_ring()
                x = R._coerce_(right)
                return self * ~x
        except (TypeError, ValueError):
            pass
        return RingElement.__div__(self, right)

    def __div__(self, other):
        return PyNumber_TrueDivide(self, other)

    def __pow__(self, right, modulus):
        """
        EXAMPLES::

            sage: x = polygen(QQ['u']['v'])
            sage: f = x - 1
            sage: f._pow(3)
            x^3 - 3*x^2 + 3*x - 1
            sage: f^3
            x^3 - 3*x^2 + 3*x - 1

            sage: R = PolynomialRing(GF(2), 'x')
            sage: f = R(x^9 + x^7 + x^6 + x^5 + x^4 + x^2 + x)
            sage: h = R(x^10 + x^7 + x^6 + x^5 + x^4 + x^3 + x^2 + 1)
            sage: pow(f, 2, h)
            x^9 + x^8 + x^7 + x^5 + x^3

        TESTS::

            sage: x = polygen(QQ['u']['v'])
            sage: x^(1/2)
            Traceback (most recent call last):
            ...
            TypeError: non-integral exponents not supported

        ::

            sage: x^x
            Traceback (most recent call last):
            ...
            TypeError: non-integral exponents not supported

        ::

            sage: k = GF(5)
            sage: D.<x> = k[]
            sage: l.<x> = k.extension(x^2 + 2)
            sage: R.<t> = l[]
            sage: f = t^4 + (2*x - 1)*t^3 + (2*x + 1)*t^2 + 3
            sage: h = t^4 - x*t^3 + (3*x + 1)*t^2 + 2*t + 2*x - 1
            sage: pow(f, 2, h)
            3*t^3 + (2*x + 3)*t^2 + (2*x + 2)*t + 2*x + 2
            sage: pow(f, 10**7, h)
            4*x*t^3 + 2*x*t^2 + 4*x*t + 4

        Check that :trac:`18457` is fixed::

            sage: R.<x> = PolynomialRing(GF(5), sparse=True)
            sage: (1+x)^(5^10) # used to hang forever
            x^9765625 + 1
            sage: S.<t> = GF(3)[]
            sage: R1.<x> = PolynomialRing(S, sparse=True)
            sage: (1+x+t)^(3^10)
            x^59049 + t^59049 + 1
            sage: R2.<x> = PolynomialRing(S, sparse=False)
            sage: (1+x+t)^(3^10)
            x^59049 + t^59049 + 1

        Check that the algorithm used is indeed correct::

            sage: from sage.structure.element import generic_power
            sage: R1 = PolynomialRing(GF(8,'a'), 'x')
            sage: R2 = PolynomialRing(GF(9,'b'), 'x', sparse=True)
            sage: R3 = PolynomialRing(R2, 'y')
            sage: R4 = PolynomialRing(R1, 'y', sparse=True)
            sage: for d in range(20,40): # long time
            ....:     for R in [R1, R2, R3, R3]:
            ....:         a = R.random_element()
            ....:         assert a^d == generic_power(a,d)

        Test the powering modulo ``x^n`` (calling :meth:`power_trunc`)::

            sage: R.<x> = GF(3)[]
            sage: pow(x + 1, 51, x^7)
            x^6 + 2*x^3 + 1

            sage: S.<y> = QQ[]
            sage: R.<x> = S[]
            sage: pow(y*x+1, 51, x^7)
            18009460*y^6*x^6 + 2349060*y^5*x^5 + ... + 51*y*x + 1
        """
        if type(right) is not Integer:
            try:
                right = Integer(right)
            except TypeError:
                raise TypeError("non-integral exponents not supported")

        if self.degree() <= 0:
            return self.parent()(self[0]**right)
        if right < 0:
            return (~self)**(-right)
        if modulus:
            if right > 0 and \
               parent(modulus) == self.parent() and \
               modulus.number_of_terms() == 1 and \
               modulus.leading_coefficient().is_one():
                return self.power_trunc(right, modulus.degree())
            return power_mod(self, right, modulus)
        if (<Polynomial>self).is_gen():   # special case x**n should be faster!
            P = self.parent()
            R = P.base_ring()
            if P.is_sparse():
                v = {right:R.one()}
            else:
                v = [R.zero()]*right + [R.one()]
            return self.parent()(v, check=False)
        if right > 20: # no gain below
            p = self.parent().characteristic()
            if p > 0 and p <= right and (self.base_ring() in sage.categories.integral_domains.IntegralDomains() or p.is_prime()):
                x = self.parent().gen()
                one = self.parent().one()
                ret = one
                e = 1
                q = right
                sparse = self.parent().is_sparse()
                if sparse:
                    d = self.dict()
                else:
                    c = self.list()
                while q > 0:
                    q, r = q.quo_rem(p)
                    if r != 0:
                        if sparse:
                            tmp = self.parent()({e*k : d[k]**e for k in d})
                        else:
                            tmp = [0] * (e * len(c) - e + 1)
                            for i in range(len(c)):
                                tmp[e*i] = c[i]**e
                            tmp = self.parent()(tmp)
                        ret *= generic_power(tmp, r, one=one)
                    e *= p
                return ret

        return generic_power(self,right)

    def power_trunc(self, n, prec):
        r"""
        Truncated ``n``-th power of this polynomial up to precision ``prec``

        INPUT:

        - ``n`` -- (non-negative integer) power to be taken

        - ``prec`` -- (integer) the precision

        EXAMPLES::

            sage: R.<x> = ZZ[]
            sage: (3*x^2 - 2*x + 1).power_trunc(5, 8)
            -1800*x^7 + 1590*x^6 - 1052*x^5 + 530*x^4 - 200*x^3 + 55*x^2 - 10*x + 1
            sage: ((3*x^2 - 2*x + 1)^5).truncate(8)
            -1800*x^7 + 1590*x^6 - 1052*x^5 + 530*x^4 - 200*x^3 + 55*x^2 - 10*x + 1

            sage: S.<y> = R[]
            sage: (x+y).power_trunc(5,5)
            5*x*y^4 + 10*x^2*y^3 + 10*x^3*y^2 + 5*x^4*y + x^5
            sage: ((x+y)^5).truncate(5)
            5*x*y^4 + 10*x^2*y^3 + 10*x^3*y^2 + 5*x^4*y + x^5

            sage: R.<x> = GF(3)[]
            sage: p = x^2 - x + 1
            sage: q = p.power_trunc(80, 20)
            sage: q
            x^19 + x^18 + ... + 2*x^4 + 2*x^3 + x + 1
            sage: (p^80).truncate(20) == q
            True

            sage: R.<x> = GF(7)[]
            sage: p = (x^2 + x + 1).power_trunc(2^100, 100)
            sage: p
            2*x^99 + x^98 + x^95 + 2*x^94 + ... + 3*x^2 + 2*x + 1

            sage: for i in range(100):
            ....:    q1 = (x^2 + x + 1).power_trunc(2^100 + i, 100)
            ....:    q2 = p * (x^2 + x + 1).power_trunc(i, 100)
            ....:    q2 = q2.truncate(100)
            ....:    assert q1 == q2, "i = {}".format(i)

        TESTS::

            sage: x = polygen(QQ)
            sage: (3*x-5).power_trunc(2^200, 0)
            0
            sage: x.power_trunc(-1, 10)
            Traceback (most recent call last):
            ...
            ValueError: n must be a non-negative integer
            sage: R.<y> = QQ['x']
            sage: y.power_trunc(2**32-1, 2)
            0
            sage: y.power_trunc(2**64-1, 2)
            0
        """
        cdef Integer ZZn = ZZ(n)
        if mpz_fits_ulong_p(ZZn.value):
            return self._power_trunc(mpz_get_ui(ZZn.value), prec)
        return generic_power_trunc(self, ZZn, pyobject_to_long(prec))

    cpdef Polynomial _power_trunc(self, unsigned long n, long prec):
        r"""
        Truncated ``n``-th power of this polynomial up to precision ``prec``

        This method is overriden for certain subclasses when a library function
        is available.

        INPUT:

        - ``n`` -- (non-negative integer) power to be taken

        - ``prec`` -- (integer) the precision

        TESTS::

            sage: R.<x> = QQ['y'][]
            sage: for p in [R.one(), x, x+1, x-1, x^2 - 1]:
            ....:     for n in range(0, 20):
            ....:         for prec in [1, 2, 3, 10]:
            ....:             assert p._power_trunc(n, prec) == (p**n).truncate(prec)
        """
        return generic_power_trunc(self, Integer(n), prec)

    def _pow(self, right):
        # TODO: fit __pow__ into the arithmetic structure
        if self.degree() <= 0:
            return self.parent()(self[0]**right)
        if right < 0:
            return (~self)**(-right)
        if (<Polynomial>self) == self.parent().gen():   # special case x**n should be faster!
            v = [0]*right + [1]
            return self.parent()(v, check=True)
        return generic_power(self, right)

    def _repr(self, name=None):
        """
        Return the string representation of this polynomial.

        INPUT:

        - ``name`` - None or a string; used for printing the variable.

        EXAMPLES::

            sage: S.<t> = QQ[]
            sage: R.<x> = S[]
            sage: f = (1 - t^3)*x^3 - t^2*x^2 - x + 1
            sage: f._repr()
            '(-t^3 + 1)*x^3 - t^2*x^2 - x + 1'
            sage: f._repr('z')
            '(-t^3 + 1)*z^3 - t^2*z^2 - z + 1'
            sage: P.<y> = RR[]
            sage: y, -y
            (y, -y)
        """
        s = " "
        m = self.degree() + 1
        if name is None:
            name = self.parent().variable_name()
        atomic_repr = self.parent().base_ring()._repr_option('element_is_atomic')
        coeffs = self.list()
        for n in reversed(xrange(m)):
            x = coeffs[n]
            if x:
                if n != m-1:
                    s += " + "
                x = y = repr(x)
                if y.find("-") == 0:
                    y = y[1:]
                if not atomic_repr and n > 0 and (y.find("+") != -1 or y.find("-") != -1):
                    x = "(%s)"%x
                if n > 1:
                    var = "*%s^%s"%(name,n)
                elif n==1:
                    var = "*%s"%name
                else:
                    var = ""
                s += "%s%s"%(x,var)
        s = s.replace(" + -", " - ")
        s = re.sub(r' 1(\.0+)?\*',' ', s)
        s = re.sub(r' -1(\.0+)?\*',' -', s)
        if s == " ":
            return "0"
        return s[1:]

    def _repr_(self):
        r"""
        Return string representation of this polynomial.

        EXAMPLES::

            sage: R.<x> = PolynomialRing(QQ, implementation="FLINT")
            sage: f = x^3+2/3*x^2 - 5/3
            sage: f._repr_()
            'x^3 + 2/3*x^2 - 5/3'
            sage: f.rename('vaughn')
            Traceback (most recent call last):
            ...
            NotImplementedError: object does not support renaming: x^3 + 2/3*x^2 - 5/3
        """
        return self._repr()

    def _latex_(self, name=None):
        r"""
        Return the latex representation of this polynomial.

        EXAMPLES:

        A fairly simple example over `\QQ`.

        ::

            sage: C3.<omega> = CyclotomicField(3)
            sage: R.<X> = C3[]
            sage: f = X^3 - omega*X
            sage: latex(f)
            X^{3} - \omega X
            sage: R.<x> = RDF[]
            sage: latex(x+2)
            x + 2.0

        The following illustrates the fix of :trac:`2586`::

            sage: latex(ZZ['alpha']['b']([0, ZZ['alpha'].0]))
            \alpha b

        The following illustrates a (non-intentional) superfluity of parentheses

            sage: K.<I>=QuadraticField(-1)
            sage: R.<x>=K[]
            sage: latex(I*x^2-I*x)
            \left(\sqrt{-1}\right) x^{2} + \left(-\sqrt{-1}\right) x
        """
        s = " "
        coeffs = self.list()
        m = len(coeffs)
        if name is None:
            name = self.parent().latex_variable_names()[0]
        atomic_repr = self.parent().base_ring()._repr_option('element_is_atomic')
        for n in reversed(xrange(m)):
            x = coeffs[n]
            x = y = latex(x)
            if x != '0':
                if n != m-1:
                    s += " + "
                if y.find("-") == 0:
                    y = y[1:]
                if not atomic_repr and n > 0 and (y.find("+") != -1 or y.find("-") != -1):
                    x = "\\left(%s\\right)"%x
                if n > 1:
                    var = "|%s^{%s}"%(name,n)
                elif n==1:
                    var = "|%s"%name
                else:
                    var = ""
                s += "%s %s"%(x,var)
        s = s.replace(" + -", " - ")
        s = re.sub(" 1(\.0+)? \|"," ", s)
        s = re.sub(" -1(\.0+)? \|", " -", s)
        s = s.replace("|","")
        if s==" ":
            return "0"
        return s[1:].lstrip().rstrip()

    def _sage_input_(self, sib, coerced):
        r"""
        Produce an expression which will reproduce this value when
        evaluated.

        EXAMPLES::

            sage: K.<x> = ZZ[]
            sage: sage_input(K(0), verify=True)
            # Verified
            ZZ['x'](0)
            sage: sage_input(K(-54321), preparse=False, verify=True)
            # Verified
            ZZ['x'](-54321)
            sage: sage_input(x, verify=True)
            # Verified
            R.<x> = ZZ[]
            x
            sage: sage_input(x, preparse=False)
            R = ZZ['x']
            x = R.gen()
            x
            sage: sage_input((3*x-2)^3, verify=True)
            # Verified
            R.<x> = ZZ[]
            27*x^3 - 54*x^2 + 36*x - 8
            sage: L.<y> = K[]
            sage: sage_input(L(0), verify=True)
            # Verified
            ZZ['x']['y'](0)
            sage: sage_input((x+y+1)^2, verify=True)
            # Verified
            R1.<x> = ZZ[]
            R2.<y> = R1[]
            y^2 + (2*x + 2)*y + (x^2 + 2*x + 1)
            sage: sage_input(RR(pi) * polygen(RR), verify=True)
            # Verified
            R.<x> = RR[]
            3.1415926535897931*x
            sage: sage_input(polygen(GF(7)) + 12, verify=True)
            # Verified
            R.<x> = GF(7)[]
            x + 5
            sage: from sage.misc.sage_input import SageInputBuilder
            sage: K(0)._sage_input_(SageInputBuilder(), True)
            {atomic:0}
            sage: (x^2 - 1)._sage_input_(SageInputBuilder(), False)
            {binop:- {binop:** {gen:x {constr_parent: {subscr: {atomic:ZZ}[{atomic:'x'}]} with gens: ('x',)}} {atomic:2}} {atomic:1}}
        """
        if self.degree() > 0:
            gen = sib.gen(self.parent())
            coeffs = self.list()
            terms = []
            for i in range(len(coeffs)-1, -1, -1):
                if i > 0:
                    if i > 1:
                        gen_pow = gen**sib.int(i)
                    else:
                        gen_pow = gen
                    terms.append(sib.prod((sib(coeffs[i], True), gen_pow), simplify=True))
                else:
                    terms.append(sib(coeffs[i], True))
            return sib.sum(terms, simplify=True)
        elif coerced:
            return sib(self.constant_coefficient(), True)
        else:
            return sib(self.parent())(sib(self.constant_coefficient(), True))

    def __setitem__(self, n, value):
        """
        Set the n-th coefficient of this polynomial. This always raises an
        IndexError, since in Sage polynomials are immutable.

        INPUT:


        -  ``n`` - an integer

        -  ``value`` - value to set the n-th coefficient to


        OUTPUT: an IndexError is always raised.

        EXAMPLES::

            sage: R.<x> = ZZ[]
            sage: f = x^3 + x + 1
            sage: f[2] = 3
            Traceback (most recent call last):
            ...
            IndexError: polynomials are immutable
        """
        raise IndexError("polynomials are immutable")

    cpdef _floordiv_(self, right):
        """
        Quotient of division of self by other. This is denoted //.

        If self = quotient \* right + remainder, this function returns
        quotient.

        EXAMPLES::

            sage: R.<x> = ZZ[]
            sage: f = x^3 + x + 1
            sage: g = f*(x^2-2) + x
            sage: g.__floordiv__(f)
            x^2 - 2
            sage: g//f
            x^2 - 2
        """
        Q, _ = self.quo_rem(right)
        return Q

    def __mod__(self, other):
        """
        Remainder of division of self by other.

        EXAMPLES::

            sage: R.<x> = ZZ[]
            sage: x % (x+1)
            -1
            sage: (x^3 + x - 1) % (x^2 - 1)
            2*x - 1
        """
        _, R = self.quo_rem(other)
        return R

    def mod(self, other):
        """
        Remainder of division of self by other.

        EXAMPLES::

            sage: R.<x> = ZZ[]
            sage: x % (x+1)
            -1
            sage: (x^3 + x - 1) % (x^2 - 1)
            2*x - 1
        """
        return self % other

    def _quo_rem_naive(self, right):
        """
        Naive quotient with remainder operating on padic polynomials as their coefficient lists
        """
        if right == 0:
            raise ZeroDivisionError, "cannot divide by a polynomial indistinguishable from 0"
        P = self.parent()
        F = list(self); G = list(right);
        fdeg = self.degree()
        gdeg = right.degree()
        Q = [0 for i in range(fdeg-gdeg+1)]
        j=1
        while fdeg >= gdeg:
            a = F[-j]
            if a!=0:
                for i in range(fdeg-gdeg,fdeg+1):
                    F[i] -= a * G[i-(fdeg-gdeg)]
                Q[fdeg-gdeg] += a
            j+=1; fdeg-=1;
        ret = P(Q), P(F)
        assert ret[0]*right + P(F) == self
        return ret

    def _quo_rem_hensel(self, right):
        if right.is_zero():
            raise ZeroDivisionError("cannot divide by a polynomial indistinguishable from 0.")
        if not right.leading_coefficient().is_unit():
            raise ValueError("Hensel quotient with remainder only applicable for polynomials with invertible leading coefficient.")

        if right.degree() > self.degree():
            return self.parent().zero(),self
        elif right.degree() == self.degree():
            q = self.parent()( self.leading_coefficient()*right.leading_coefficient().inverse_of_unit() )
        else:
            def reverse(poly):
                x = list(reversed(poly.list()))
                while x and x[-1].is_zero(): x.pop()
                return poly.parent()(x)

            f = reverse(self)
            g = reverse(right)
            h = self.parent()(right.leading_coefficient().inverse_of_unit())
            s = h

            k = 1
            while k < self.degree() - right.degree() + 1:
                e = self.parent().one() - g*h
                h = (h + s*e).truncate(2*k)
                d = (s*g - 1).truncate(2*k)
                s = (s*(1-d)).truncate(2*k)
                k <<= 1

            #from sage.misc.all import save
            #save((self,right,f,g,h),"/tmp/sr")
            h = h#.truncate(self.degree() - right.degree() + 1)
            #assert (h*g).truncate(self.degree() - right.degree() + 1).is_one()
            q = (f*h).truncate(self.degree() - right.degree() + 1)
            q = q.truncate(q.degree()+1)
            q = reverse(q)
            q <<= (self.degree() - right.degree() - q.degree())

        r = self - right*q
        r = r.truncate(r.degree()+1)

        # check correctness of the output
        assert r.degree() < right.degree() and q*right + r == self, "incorrect quo_rem: %s =?= %s * %s + %s = %s"%(self,right,q,r,q*right + r)
        return q, r

    def _is_atomic(self):
        """
        EXAMPLES::

            sage: R.<x> = QQ[]
            sage: S.<y> = R[]
            sage: S(x+2)
            x + 2
            sage: S(x+2)._is_atomic()
            False
            sage: S(x)._is_atomic()
            True
        """
        return (self.degree() == self.valuation() and
                self.leading_coefficient()._is_atomic())

    def _mul_generic(self, right):
        """
        Compute the product of self and right using the classical quadratic
        algorithm. This method is the default for inexact rings.

        For two polynomials of degree n and m this method needs
        (m+1)*(n+1) products and n*m additions

        EXAMPLES::

            sage: K.<x> = QQ[]
            sage: f = 1+3*x+4*x^2+x^3
            sage: g = x^2+3*x^5
            sage: f._mul_generic(g)
            3*x^8 + 12*x^7 + 9*x^6 + 4*x^5 + 4*x^4 + 3*x^3 + x^2

        Show the product in the symbolic ring::

            sage: L = SR['x']
            sage: var('a0,a1,b0,b1')
            (a0, a1, b0, b1)
            sage: L([a0,a1])._mul_generic(L([b0,b1]))
            a1*b1*x^2 + (a1*b0 + a0*b1)*x + a0*b0

        A non-commutative example::

            sage: A.<i,j,k> = QuaternionAlgebra(QQ, -1,-1)
            sage: R.<w> = PolynomialRing(A)
            sage: f = i*w + j
            sage: g = k*w + 1
            sage: f._mul_generic(g)
            -j*w^2 + 2*i*w + j
            sage: g._mul_generic(f)
            j*w^2 + j


        TESTS::

            sage: K.<x> = QQ[]
            sage: f = K(0)
            sage: g = K.random_element(10)
            sage: f._mul_generic(g)
            0
            sage: g._mul_generic(f)
            0
            sage: f._mul_generic(K(0))
            0
            sage: g._mul_generic(g) - g._mul_karatsuba(g)
            0
            sage: h = K(QQ.random_element(100,100))
            sage: f._mul_generic(h)
            0
            sage: K([h*c for c in g.list()]) - g._mul_generic(h)
            0
            sage: g._mul_generic(h) - K([h*c for c in g.list()])
            0
        """
        if self is right:
            return self._square_generic()
        x = self.list()
        y = right.list()
        return self._parent(do_schoolbook_product(x,y))

    def _square_generic(self):
        x = self.list()
        cdef Py_ssize_t i, j
        cdef Py_ssize_t d = len(x)-1
        zero = self._parent.base_ring().zero()
        two = self._parent.base_ring()(2)
        coeffs = [zero] * (2 * d + 1)
        for i from 0 <= i <= d:
            coeffs[2*i] = x[i] * x[i]
            for j from 0 <= j < i:
                coeffs[i+j] += two * x[i] * x[j]
        return self._parent(coeffs)

    def _mul_fateman(self, right):
        r"""
        Returns the product of two polynomials using Kronecker's trick to
        do the multiplication. This could be used over a generic base
        ring.

        .. note::

           -  Since this is implemented in interpreted Python, it could be
              hugely sped up by reimplementing it in Pyrex.

           -  Over the reals there is precision loss, at least in the current
              implementation.


        INPUT:

        -  ``self`` - Polynomial

        -  ``right`` - Polynomial (over same base ring as
           self)


        OUTPUT: Polynomial - The product self\*right.

        ALGORITHM: Based on a paper by R. Fateman

        http://www.cs.berkeley.edu/~fateman/papers/polysbyGMP.pdf

        The idea is to encode dense univariate polynomials as big integers,
        instead of sequences of coefficients. The paper argues that because
        integer multiplication is so cheap, that encoding 2 polynomials to
        big numbers and then decoding the result might be faster than
        popular multiplication algorithms. This seems true when the degree
        is larger than 200.

        EXAMPLES::

            sage: S.<y> = PolynomialRing(RR)
            sage: f = y^10 - 1.393493*y + 0.3
            sage: f._mul_karatsuba(f,0)
            y^20 - 2.78698600000000*y^11 + 0.600000000000000*y^10 + 1.11022302462516e-16*y^8 - 1.11022302462516e-16*y^6 - 1.11022302462516e-16*y^3 + 1.94182274104900*y^2 - 0.836095800000000*y + 0.0900000000000000
            sage: f._mul_fateman(f)
            y^20 - 2.78698600000000*y^11 + 0.600000000000000*y^10 + 1.94182274104900*y^2 - 0.836095800000000*y + 0.0900000000000000

        Advantages:


        -  Faster than Karatsuba over `\QQ` and
           `\ZZ` (but much slower still than calling NTL's
           optimized C++ implementation, which is the default over
           `\ZZ`)

        -  Potentially less complicated.


        Drawbacks:


        -  Slower over R when the degree of both of polynomials is less
           than 250 (roughly).

        -  Over R, results may not be as accurate as the Karatsuba case.
           This is because we represent coefficients of polynomials over R as
           fractions, then convert them back to floating-point numbers.


        AUTHORS:

        - Didier Deshommes (2006-05-25)
        """
        return self.parent()(polynomial_fateman._mul_fateman_mul(self,right))

    def _mul_karatsuba(self, right, K_threshold = None):
        r"""
        Compute the product of two polynomials using the Karatsuba divide
        and conquer multiplication algorithm. This is only used over a
        generic base ring. (Special libraries like Flint are used, e.g., for
        the integers and rationals, which are much faster.)

        INPUT:

          - ``self`` - Polynomial
          - ``right`` - Polynomial (over same base ring as self)
          - ``K_threshold`` - (optional) Integer. A threshold to fall back to
          schoolbook algorithm. In the recursion, if one of the polynomials is
          of degree less that K_threshold then the classic quadratic polynomial
          is used.

        OUTPUT: Polynomial - The product self\*right.

        ALGORITHM: The basic idea is to use that

        .. math::

            (aX + b) (cX + d) = acX^2 + ((a+b)(c+d)-ac-bd)X + bd


        where ac=a\*c and bd=b\*d, which requires three multiplications
        instead of the naive four. Given f and g of arbitrary degree bigger
        than one, let e be min(deg(f),deg(g))/2. Write

        .. math::

            f = a X^e + b   \text{ and }   g = c X^e + d


        and use the identity

        .. math::

            (aX^e + b) (cX^e + d) = ac X^{2e} +((a+b)(c+d) - ac - bd)X^e + bd


        to recursively compute `fg`.

        If `self` is a polynomial of degree n and `right` is a polynomial of
        degree m with n < m, then we interpret `right` as

        ..math::

            g0 + g1*x^n +g2*x^{2n} + ... + gq*x^{nq}

        where `gi` are polynomials of degree <= n. We then compute each product
        `gi*right` with Karatsuba multiplication and reconstruct `self*right`
        from the partial products.

        The theoretical complexity for multiplying two polynomials of the same
        degree n is O(n^log(3,2)). Through testing of polynomials of degree up
        to 5000 we get that the number of operations for two polynomials of
        degree up to n-1 is bounded by:

        7.53*n**1.59 additions and 1.46*n**1.59 products on the base ring.

        For polynomials of degree m-1 and n-1 with m<n the number of operations
        is bounded by:

        8.11*m**0.59*n additions and 1.56*m**0.59*n products.

        (The bound might be worse for larger degrees.)

        EXAMPLES::

            sage: K.<x> = QQ[]
            sage: f = 1+3*x+4*x^2+x^3
            sage: g = x^2+3*x^5
            sage: f._mul_karatsuba(g,0)
            3*x^8 + 12*x^7 + 9*x^6 + 4*x^5 + 4*x^4 + 3*x^3 + x^2
            sage: f._mul_karatsuba(g,2)
            3*x^8 + 12*x^7 + 9*x^6 + 4*x^5 + 4*x^4 + 3*x^3 + x^2

        Show the product in the symbolic ring::

            sage: L = SR['x']
            sage: var('a0,a1,b0,b1')
            (a0, a1, b0, b1)
            sage: L([a0,a1])._mul_karatsuba(L([b0,b1]),0)
            a1*b1*x^2 + ((a0 + a1)*(b0 + b1) - a0*b0 - a1*b1)*x + a0*b0
            sage: L([a0,a1])._mul_karatsuba(L([b0,b1]),2)
            a1*b1*x^2 + (a1*b0 + a0*b1)*x + a0*b0

        A noncommutative example::

            sage: A.<i,j,k> = QuaternionAlgebra(QQ, -1,-1)
            sage: R.<w> = PolynomialRing(A)
            sage: f = i*w + j
            sage: g = k*w + 1
            sage: f._mul_karatsuba(g,0)
            -j*w^2 + 2*i*w + j
            sage: g._mul_karatsuba(f,0)
            j*w^2 + j

        TESTS::

            sage: K.<x> = QQ[]
            sage: f = K(0)
            sage: g = K.random_element(10)
            sage: f._mul_karatsuba(g,0)
            0
            sage: g._mul_karatsuba(f,0)
            0
            sage: f._mul_karatsuba(K(0),0)
            0
            sage: g._mul_generic(g) - g._mul_karatsuba(g,0)
            0
            sage: h = K(QQ.random_element(100,100))
            sage: f._mul_karatsuba(h)
            0
            sage: K([h*c for c in g.list()]) - g._mul_generic(h)
            0
            sage: g._mul_karatsuba(h) - K([h*c for c in g.list()])
            0

        Random tests for noncommutative rings::

            sage: A.<i,j,k> = QuaternionAlgebra(QQ, -1,-1)
            sage: R.<w> = PolynomialRing(A)
            sage: f = R.random_element(randint(10,100))
            sage: g = R.random_element(randint(10,100))
            sage: f._mul_generic(g) == f._mul_karatsuba(g,0)
            True
            sage: f._mul_generic(g) == f._mul_karatsuba(g,16)
            True
            sage: g = R.random_element(0)
            sage: f._mul_karatsuba(g,0) == f._mul_generic(g)
            True
            sage: g._mul_karatsuba(f,0) == g._mul_generic(f)
            True

        Polynomials over matrices::

            sage: K = PolynomialRing(MatrixSpace(QQ,2),'x')
            sage: f = K.random_element(randint(5,10))
            sage: g = K.random_element(randint(5,10))
            sage: h1 = f._mul_generic(g)
            sage: h2 = f._mul_karatsuba(g,randint(0,10))
            sage: h1 == h2
            True
        """
        if self.is_zero():
            return self
        elif right.is_zero():
            return right
        f = self.list()
        g = right.list()
        n = len(f)
        m = len(g)
        if n == 1:
            c = f[0]
            return self._parent([c*a for a in g])
        if m == 1:
            c = g[0]
            return self._parent([a*c for a in f])
        if K_threshold is None:
            K_threshold = self._parent._Karatsuba_threshold
        if n <= K_threshold or m <= K_threshold:
            return self._parent(do_schoolbook_product(f,g))
        if n == m:
            return self._parent(do_karatsuba(f,g, K_threshold, 0, 0, n))
        return self._parent(do_karatsuba_different_size(f,g, K_threshold))

    def base_ring(self):
        """
        Return the base ring of the parent of self.

        EXAMPLES::

            sage: R.<x> = ZZ[]
            sage: x.base_ring()
            Integer Ring
            sage: (2*x+3).base_ring()
            Integer Ring
        """
        return self.parent().base_ring()

    cpdef base_extend(self, R):
        """
        Return a copy of this polynomial but with coefficients in R, if
        there is a natural map from coefficient ring of self to R.

        EXAMPLES::

            sage: R.<x> = QQ[]
            sage: f = x^3 - 17*x + 3
            sage: f.base_extend(GF(7))
            Traceback (most recent call last):
            ...
            TypeError: no such base extension
            sage: f.change_ring(GF(7))
            x^3 + 4*x + 3
        """
        S = self.parent().base_extend(R)
        return S(self)

    def change_variable_name(self, var):
        """
        Return a new polynomial over the same base ring but in a different
        variable.

        EXAMPLES::

            sage: x = polygen(QQ,'x')
            sage: f = -2/7*x^3 + (2/3)*x - 19/993; f
            -2/7*x^3 + 2/3*x - 19/993
            sage: f.change_variable_name('theta')
            -2/7*theta^3 + 2/3*theta - 19/993
        """
        R = self.parent().base_ring()[var]
        return R(self.list())

    def change_ring(self, R):
        """
        Return a copy of this polynomial but with coefficients in ``R``, if at
        all possible.

        INPUT:

        - ``R`` - a ring or morphism.

        EXAMPLES::

            sage: K.<z> = CyclotomicField(3)
            sage: f = K.defining_polynomial()
            sage: f.change_ring(GF(7))
            x^2 + x + 1

        ::

            sage: K.<z> = CyclotomicField(3)
            sage: R.<x> = K[]
            sage: f = x^2 + z
            sage: f.change_ring(K.embeddings(CC)[0])
            x^2 - 0.500000000000000 - 0.866025403784439*I
        """
        if isinstance(R, Morphism):
            # we're given a hom of the base ring extend to a poly hom
            if R.domain() == self.base_ring():
                R = self.parent().hom(R, self.parent().change_ring(R.codomain()))
            return R(self)
        else:
            return self.parent().change_ring(R)(self)

    def _mpoly_dict_recursive(self, variables=None, base_ring=None):
        """
        Return a dict of coefficient entries suitable for construction of a
        MPolynomial_polydict with the given variables.

        EXAMPLES::

            sage: R.<x> = ZZ[]
            sage: R(0)._mpoly_dict_recursive()
            {}
            sage: f = 7*x^5 + x^2 - 2*x - 3
            sage: f._mpoly_dict_recursive()
            {(0,): -3, (1,): -2, (2,): 1, (5,): 7}
        """
        if not self:
            return {}

        var = self.parent().variable_name()
        if variables is None:
            variables = self.parent().variable_names_recursive()
        if not var in variables:
            x = base_ring(self) if base_ring else self
            const_ix = ETuple((0,)*len(variables))
            return { const_ix: x }

        prev_variables = variables[:list(variables).index(var)]
        const_ix = ETuple((0,)*len(prev_variables))
        mpolys = None

        if len(prev_variables) > 0:
            try:
                mpolys = [a._mpoly_dict_recursive(prev_variables, base_ring) for a in self]
            except AttributeError as msg:
                pass

        if mpolys is None:
            if base_ring is not None and base_ring is not self.base_ring():
                mpolys = [{const_ix:base_ring(a)} if a else {} for a in self]
            else:
                mpolys = [{const_ix:a} if a else {} for a in self]

        D = {}
        leftovers = (0,) * (len(variables) - len(prev_variables) - 1)
        for k in range(len(mpolys)):
            for i,a in mpolys[k].iteritems():
                j = ETuple((k,) + leftovers)
                D[i + j] = a

        return D

    def __copy__(self):
        """
        Return a "copy" of self. This is just self, since in Sage
        polynomials are immutable this just returns self again.

        EXAMPLES:

        We create the polynomial `f=x+3`, then note that
        the copy is just the same polynomial again, which is fine since
        polynomials are immutable.

        ::

            sage: x = ZZ['x'].0
            sage: f = x + 3
            sage: g = copy(f)
            sage: g is f
            True
        """
        return self

    def degree(self, gen=None):
        """
        Return the degree of this polynomial. The zero polynomial has
        degree -1.

        EXAMPLES::

            sage: x = ZZ['x'].0
            sage: f = x^93 + 2*x + 1
            sage: f.degree()
            93
            sage: x = PolynomialRing(QQ, 'x', sparse=True).0
            sage: f = x^100000
            sage: f.degree()
            100000

        ::

            sage: x = QQ['x'].0
            sage: f = 2006*x^2006 - x^2 + 3
            sage: f.degree()
            2006
            sage: f = 0*x
            sage: f.degree()
            -1
            sage: f = x + 33
            sage: f.degree()
            1

        AUTHORS:

        - Naqi Jaffery (2006-01-24): examples
        """
        raise NotImplementedError

    def euclidean_degree(self):
        r"""
        Return the degree of this element as an element of a euclidean domain.

        If this polynomial is defined over a field, this is simply its :meth:`degree`.

        EXAMPLES::

            sage: R.<x> = QQ[]
            sage: x.euclidean_degree()
            1
            sage: R.<x> = ZZ[]
            sage: x.euclidean_degree()
            Traceback (most recent call last):
            ...
            NotImplementedError

        """
        from sage.categories.fields import Fields
        if self.base_ring() in Fields():
            return self.degree()
        raise NotImplementedError

    def denominator(self):
        """
        Return a denominator of self.

        First, the lcm of the denominators of the entries of self
        is computed and returned. If this computation fails, the
        unit of the parent of self is returned.

        Note that some subclasses may implement their own
        denominator function. For example, see
        :class:`sage.rings.polynomial.polynomial_rational_flint.Polynomial_rational_flint`

        .. warning::

           This is not the denominator of the rational function
           defined by self, which would always be 1 since self is a
           polynomial.

        EXAMPLES:

        First we compute the denominator of a polynomial with
        integer coefficients, which is of course 1.

        ::

            sage: R.<x> = ZZ[]
            sage: f = x^3 + 17*x + 1
            sage: f.denominator()
            1

        Next we compute the denominator of a polynomial with rational
        coefficients.

        ::

            sage: R.<x> = PolynomialRing(QQ)
            sage: f = (1/17)*x^19 - (2/3)*x + 1/3; f
            1/17*x^19 - 2/3*x + 1/3
            sage: f.denominator()
            51

        Finally, we try to compute the denominator of a polynomial with
        coefficients in the real numbers, which is a ring whose elements do
        not have a denominator method.

        ::

            sage: R.<x> = RR[]
            sage: f = x + RR('0.3'); f
            x + 0.300000000000000
            sage: f.denominator()
            1.00000000000000

        Check that the denominator is an element over the base whenever the base
        has no denominator function. This closes #9063.

        ::

            sage: R.<a> = GF(5)[]
            sage: x = R(0)
            sage: x.denominator()
            1
            sage: type(x.denominator())
            <type 'sage.rings.finite_rings.integer_mod.IntegerMod_int'>
            sage: isinstance(x.numerator() / x.denominator(), Polynomial)
            True
            sage: isinstance(x.numerator() / R(1), Polynomial)
            False

        TESTS:

        Check that :trac:`18518` is fixed::

            sage: R.<x> = PolynomialRing(QQ, sparse=True)
            sage: p = x^(2^100) - 1/2
            sage: p.denominator()
            2
        """

        if self.degree() == -1:
            return self.base_ring().one()
        x = self.coefficients()
        try:
            d = x[0].denominator()
            for y in x:
                d = d.lcm(y.denominator())
            return d
        except(AttributeError):
            return self.base_ring().one()

    def numerator(self):
        """
        Return a numerator of self computed as self * self.denominator()

        Note that some subclases may implement its own numerator
        function. For example, see
        :class:`sage.rings.polynomial.polynomial_rational_flint.Polynomial_rational_flint`

        .. warning::

          This is not the numerator of the rational function
          defined by self, which would always be self since self is a
          polynomial.

        EXAMPLES:

        First we compute the numerator of a polynomial with
        integer coefficients, which is of course self.

        ::

            sage: R.<x> = ZZ[]
            sage: f = x^3 + 17*x + 1
            sage: f.numerator()
            x^3 + 17*x + 1
            sage: f == f.numerator()
            True

        Next we compute the numerator of a polynomial with rational
        coefficients.

        ::

            sage: R.<x> = PolynomialRing(QQ)
            sage: f = (1/17)*x^19 - (2/3)*x + 1/3; f
            1/17*x^19 - 2/3*x + 1/3
            sage: f.numerator()
            3*x^19 - 34*x + 17
            sage: f == f.numerator()
            False

        We try to compute the denominator of a polynomial with
        coefficients in the real numbers, which is a ring whose elements do
        not have a denominator method.

        ::

            sage: R.<x> = RR[]
            sage: f = x + RR('0.3'); f
            x + 0.300000000000000
            sage: f.numerator()
            x + 0.300000000000000

        We check that the computation the numerator and denominator
        are valid

        ::

            sage: K=NumberField(symbolic_expression('x^3+2'),'a')['s,t']['x']
            sage: f=K.random_element()
            sage: f.numerator() / f.denominator() == f
            True
            sage: R=RR['x']
            sage: f=R.random_element()
            sage: f.numerator() / f.denominator() == f
            True
        """
        return self * self.denominator()

    def derivative(self, *args):
        r"""
        The formal derivative of this polynomial, with respect to variables
        supplied in args.

        Multiple variables and iteration counts may be supplied; see
        documentation for the global derivative() function for more
        details.

        .. seealso::

           :meth:`_derivative`

        EXAMPLES::

            sage: R.<x> = PolynomialRing(QQ)
            sage: g = -x^4 + x^2/2 - x
            sage: g.derivative()
            -4*x^3 + x - 1
            sage: g.derivative(x)
            -4*x^3 + x - 1
            sage: g.derivative(x, x)
            -12*x^2 + 1
            sage: g.derivative(x, 2)
            -12*x^2 + 1

        ::

            sage: R.<t> = PolynomialRing(ZZ)
            sage: S.<x> = PolynomialRing(R)
            sage: f = t^3*x^2 + t^4*x^3
            sage: f.derivative()
            3*t^4*x^2 + 2*t^3*x
            sage: f.derivative(x)
            3*t^4*x^2 + 2*t^3*x
            sage: f.derivative(t)
            4*t^3*x^3 + 3*t^2*x^2
        """
        return multi_derivative(self, args)

    # add .diff(), .differentiate() as aliases for .derivative()
    diff = differentiate = derivative

    def _derivative(self, var=None):
        r"""
        Return the formal derivative of this polynomial with respect to the
        variable var.

        If var is the generator of this polynomial ring (or the default
        value None), this is the usual formal derivative.

        Otherwise, _derivative(var) is called recursively for each of the
        coefficients of this polynomial.

        .. seealso::

           :meth:`derivative`

        EXAMPLES::

            sage: R.<x> = ZZ[]
            sage: R(0)._derivative()
            0
            sage: parent(R(0)._derivative())
            Univariate Polynomial Ring in x over Integer Ring

        ::

            sage: f = 7*x^5 + x^2 - 2*x - 3
            sage: f._derivative()
            35*x^4 + 2*x - 2
            sage: f._derivative(None)
            35*x^4 + 2*x - 2
            sage: f._derivative(x)
            35*x^4 + 2*x - 2

        In the following example, it doesn't recognise 2\*x as the
        generator, so it tries to differentiate each of the coefficients
        with respect to 2\*x, which doesn't work because the integer
        coefficients don't have a _derivative() method::

            sage: f._derivative(2*x)
            Traceback (most recent call last):
            ...
            AttributeError: 'sage.rings.integer.Integer' object has no attribute '_derivative'

        Examples illustrating recursive behaviour::

            sage: R.<x> = ZZ[]
            sage: S.<y> = PolynomialRing(R)
            sage: f = x^3 + y^3
            sage: f._derivative()
            3*y^2
            sage: f._derivative(y)
            3*y^2
            sage: f._derivative(x)
            3*x^2

        ::

            sage: R = ZZ['x']
            sage: S = R.fraction_field(); x = S.gen()
            sage: R(1).derivative(R(x))
            0
        """
        if var is not None and var != self._parent.gen():
            # call _derivative() recursively on coefficients
            return self._parent([coeff._derivative(var) for coeff in self.list()])

        # compute formal derivative with respect to generator
        if self.is_zero():
            return self
        cdef Py_ssize_t n, degree = self.degree()
        if degree == 0:
            return self.parent().zero()
        coeffs = self.list()
        return self._parent([n*coeffs[n] for n from 1 <= n <= degree])

    def integral(self,var=None):
        """
        Return the integral of this polynomial.

        By default, the integration variable is the variable of the
        polynomial.

        Otherwise, the integration variable is the optional parameter ``var``

        .. NOTE::

            The integral is always chosen so that the constant term is 0.

        EXAMPLES::

            sage: R.<x> = ZZ[]
            sage: R(0).integral()
            0
            sage: f = R(2).integral(); f
            2*x

        Note that the integral lives over the fraction field of the
        scalar coefficients::

            sage: f.parent()
            Univariate Polynomial Ring in x over Rational Field
            sage: R(0).integral().parent()
            Univariate Polynomial Ring in x over Rational Field

            sage: f = x^3 + x - 2
            sage: g = f.integral(); g
            1/4*x^4 + 1/2*x^2 - 2*x
            sage: g.parent()
            Univariate Polynomial Ring in x over Rational Field

        This shows that the issue at :trac:`7711` is resolved::

            sage: P.<x,z> = PolynomialRing(GF(2147483647))
            sage: Q.<y> = PolynomialRing(P)
            sage: p=x+y+z
            sage: p.integral()
            -1073741823*y^2 + (x + z)*y

            sage: P.<x,z> = PolynomialRing(GF(next_prime(2147483647)))
            sage: Q.<y> = PolynomialRing(P)
            sage: p=x+y+z
            sage: p.integral()
            1073741830*y^2 + (x + z)*y

        A truly convoluted example::

            sage: A.<a1, a2> = PolynomialRing(ZZ)
            sage: B.<b> = PolynomialRing(A)
            sage: C.<c> = PowerSeriesRing(B)
            sage: R.<x> = PolynomialRing(C)
            sage: f = a2*x^2 + c*x - a1*b
            sage: f.parent()
            Univariate Polynomial Ring in x over Power Series Ring in c
            over Univariate Polynomial Ring in b over Multivariate Polynomial
            Ring in a1, a2 over Integer Ring
            sage: f.integral()
            1/3*a2*x^3 + 1/2*c*x^2 - a1*b*x
            sage: f.integral().parent()
            Univariate Polynomial Ring in x over Power Series Ring in c
            over Univariate Polynomial Ring in b over Multivariate Polynomial
            Ring in a1, a2 over Rational Field
            sage: g = 3*a2*x^2 + 2*c*x - a1*b
            sage: g.integral()
            a2*x^3 + c*x^2 - a1*b*x
            sage: g.integral().parent()
            Univariate Polynomial Ring in x over Power Series Ring in c
            over Univariate Polynomial Ring in b over Multivariate Polynomial
            Ring in a1, a2 over Rational Field

        Integration with respect to a variable in the base ring::

            sage: R.<x> = QQ[]
            sage: t = PolynomialRing(R,'t').gen()
            sage: f = x*t +5*t^2
            sage: f.integral(x)
            5*x*t^2 + 1/2*x^2*t

        TESTS:

        Check that :trac:`18600` is fixed::

            sage: Sx.<x> = ZZ[]
            sage: Sxy.<y> = Sx[]
            sage: Sxyz.<z> = Sxy[]
            sage: p = 1 + x*y + x*z + y*z^2
            sage: q = p.integral()
            sage: q
            1/3*y*z^3 + 1/2*x*z^2 + (x*y + 1)*z
            sage: q.parent()
            Univariate Polynomial Ring in z over Univariate Polynomial Ring in y
            over Univariate Polynomial Ring in x over Rational Field
            sage: q.derivative() == p
            True
            sage: p.integral(y)
            1/2*y^2*z^2 + x*y*z + 1/2*x*y^2 + y
            sage: p.integral(y).derivative(y) == p
            True
            sage: p.integral(x).derivative(x) == p
            True

        Check that it works with non-integral domains (:trac:`18600`)::

            sage: x = polygen(Zmod(4))
            sage: p = x**4 + 1
            sage: p.integral()
            x^5 + x
            sage: p.integral().derivative() == p
            True
        """
        R = self._parent

        # TODO:
        # calling the coercion model bin_op is much more accurate than using the
        # true division (which is bypassed by polynomials). But it does not work
        # in all cases!!
        cm = coercion_model
        try:
            S = cm.bin_op(R.one(), ZZ.one(), operator.div).parent()
            Q = S.base_ring()
        except TypeError:
            Q = (R.base_ring().one()/ZZ.one()).parent()
            S = R.change_ring(Q)
        if var is not None and var != R.gen():
            # call integral() recursively on coefficients
            return S([coeff.integral(var) for coeff in self])
        cdef Py_ssize_t n
        zero = Q.zero()
        p = [zero] + [cm.bin_op(Q(self[n]), n+1, operator.div) if self[n] else zero for n in range(self.degree()+1)]
        return S(p)

    def dict(self):
        """
        Return a sparse dictionary representation of this univariate
        polynomial.

        EXAMPLES::

            sage: R.<x> = QQ[]
            sage: f = x^3 + -1/7*x + 13
            sage: f.dict()
            {0: 13, 1: -1/7, 3: 1}
        """
        X = {}
        Y = self.list()
        for i in xrange(len(Y)):
            c = Y[i]
            if c:
                X[i] = c
        return X

    def factor(self, **kwargs):
        r"""
        Return the factorization of ``self`` over its base ring.

        INPUT:

        - ``kwargs`` -- any keyword arguments are passed to the method
          ``_factor_univariate_polynomial()`` of the base ring if it
          defines such a method.

        OUTPUT:

        - A factorization of ``self`` over its parent into a unit and
          irreducible factors.  If the parent is a polynomial ring
          over a field, these factors are monic.

        EXAMPLES:

        Factorization is implemented over various rings. Over `\QQ`::

            sage: x = QQ['x'].0
            sage: f = (x^3 - 1)^2
            sage: f.factor()
            (x - 1)^2 * (x^2 + x + 1)^2

        Since `\QQ` is a field, the irreducible factors are monic::

            sage: f = 10*x^5 - 1
            sage: f.factor()
            (10) * (x^5 - 1/10)
            sage: f = 10*x^5 - 10
            sage: f.factor()
            (10) * (x - 1) * (x^4 + x^3 + x^2 + x + 1)

        Over `\ZZ` the irreducible factors need not be monic::

            sage: x = ZZ['x'].0
            sage: f = 10*x^5 - 1
            sage: f.factor()
            10*x^5 - 1

        We factor a non-monic polynomial over a finite field of 25
        elements::

            sage: k.<a> = GF(25)
            sage: R.<x> = k[]
            sage: f = 2*x^10 + 2*x + 2*a
            sage: F = f.factor(); F
            (2) * (x + a + 2) * (x^2 + 3*x + 4*a + 4) * (x^2 + (a + 1)*x + a + 2) * (x^5 + (3*a + 4)*x^4 + (3*a + 3)*x^3 + 2*a*x^2 + (3*a + 1)*x + 3*a + 1)

        Notice that the unit factor is included when we multiply `F`
        back out::

            sage: expand(F)
            2*x^10 + 2*x + 2*a

        A new ring.  In the example below, we set the special method
        ``_factor_univariate_polynomial()`` in the base ring which is
        called to factor univariate polynomials.  This facility can be
        used to easily extend polynomial factorization to work over
        new rings you introduce::

             sage: R.<x> = PolynomialRing(IntegerModRing(4),implementation="NTL")
             sage: (x^2).factor()
             Traceback (most recent call last):
             ...
             NotImplementedError: factorization of polynomials over rings with composite characteristic is not implemented
             sage: R.base_ring()._factor_univariate_polynomial = lambda f: f.change_ring(ZZ).factor()
             sage: (x^2).factor()
             x^2
             sage: del R.base_ring()._factor_univariate_polynomial # clean up

        Arbitrary precision real and complex factorization::

            sage: R.<x> = RealField(100)[]
            sage: F = factor(x^2-3); F
            (x - 1.7320508075688772935274463415) * (x + 1.7320508075688772935274463415)
            sage: expand(F)
            x^2 - 3.0000000000000000000000000000
            sage: factor(x^2 + 1)
            x^2 + 1.0000000000000000000000000000

            sage: R.<x> = ComplexField(100)[]
            sage: F = factor(x^2+3); F
            (x - 1.7320508075688772935274463415*I) * (x + 1.7320508075688772935274463415*I)
            sage: expand(F)
            x^2 + 3.0000000000000000000000000000
            sage: factor(x^2+1)
            (x - I) * (x + I)
            sage: f = R(I) * (x^2 + 1) ; f
            I*x^2 + I
            sage: F = factor(f); F
            (1.0000000000000000000000000000*I) * (x - I) * (x + I)
            sage: expand(F)
            I*x^2 + I

        Over a number field::

            sage: K.<z> = CyclotomicField(15)
            sage: x = polygen(K)
            sage: ((x^3 + z*x + 1)^3*(x - z)).factor()
            (x - z) * (x^3 + z*x + 1)^3
            sage: cyclotomic_polynomial(12).change_ring(K).factor()
            (x^2 - z^5 - 1) * (x^2 + z^5)
            sage: ((x^3 + z*x + 1)^3*(x/(z+2) - 1/3)).factor()
            (-1/331*z^7 + 3/331*z^6 - 6/331*z^5 + 11/331*z^4 - 21/331*z^3 + 41/331*z^2 - 82/331*z + 165/331) * (x - 1/3*z - 2/3) * (x^3 + z*x + 1)^3

        Over a relative number field::

            sage: x = polygen(QQ)
            sage: K.<z> = CyclotomicField(3)
            sage: L.<a> = K.extension(x^3 - 2)
            sage: t = polygen(L, 't')
            sage: f = (t^3 + t + a)*(t^5 + t + z); f
            t^8 + t^6 + a*t^5 + t^4 + z*t^3 + t^2 + (a + z)*t + z*a
            sage: f.factor()
            (t^3 + t + a) * (t^5 + t + z)

        Over the real double field::

            sage: R.<x> = RDF[]
            sage: (-2*x^2 - 1).factor()
            (-2.0) * (x^2 + 0.5000000000000001)
            sage: (-2*x^2 - 1).factor().expand()
            -2.0*x^2 - 1.0000000000000002
            sage: f = (x - 1)^3
            sage: f.factor()  # abs tol 2e-5
            (x - 1.0000065719436413) * (x^2 - 1.9999934280563585*x + 0.9999934280995487)

        The above output is incorrect because it relies on the
        :meth:`.roots` method, which does not detect that all the roots
        are real::

            sage: f.roots()  # abs tol 2e-5
            [(1.0000065719436413, 1)]

        Over the complex double field the factors are approximate and
        therefore occur with multiplicity 1::

            sage: R.<x> = CDF[]
            sage: f = (x^2 + 2*R(I))^3
            sage: F = f.factor()
            sage: F  # abs tol 3e-5
            (x - 1.0000138879287663 + 1.0000013435286879*I) * (x - 0.9999942196864997 + 0.9999873009803959*I) * (x - 0.9999918923847313 + 1.0000113554909125*I) * (x + 0.9999908759550227 - 1.0000069659624138*I) * (x + 0.9999985293216753 - 0.9999886153831807*I) * (x + 1.0000105947233 - 1.0000044186544053*I)
            sage: [f(t[0][0]).abs() for t in F] # abs tol 1e-13
            [1.979365054e-14, 1.97936298566e-14, 1.97936990747e-14, 3.6812407475e-14, 3.65211563729e-14, 3.65220890052e-14]

        Factoring polynomials over `\ZZ/n\ZZ` for
        composite `n` is not implemented::

            sage: R.<x> = PolynomialRing(Integers(35))
            sage: f = (x^2+2*x+2)*(x^2+3*x+9)
            sage: f.factor()
            Traceback (most recent call last):
            ...
            NotImplementedError: factorization of polynomials over rings with composite characteristic is not implemented

        Factoring polynomials over the algebraic numbers (see
        :trac:`8544`)::

            sage: R.<x> = QQbar[]
            sage: (x^8-1).factor()
            (x - 1) * (x - 0.7071067811865475? - 0.7071067811865475?*I) * (x - 0.7071067811865475? + 0.7071067811865475?*I) * (x - I) * (x + I) * (x + 0.7071067811865475? - 0.7071067811865475?*I) * (x + 0.7071067811865475? + 0.7071067811865475?*I) * (x + 1)

        Factoring polynomials over the algebraic reals (see
        :trac:`8544`)::

            sage: R.<x> = AA[]
            sage: (x^8+1).factor()
            (x^2 - 1.847759065022574?*x + 1.000000000000000?) * (x^2 - 0.7653668647301795?*x + 1.000000000000000?) * (x^2 + 0.7653668647301795?*x + 1.000000000000000?) * (x^2 + 1.847759065022574?*x + 1.000000000000000?)

        TESTS:

        This came up in :trac:`7088`::

            sage: R.<x>=PolynomialRing(ZZ)
            sage: f = 12*x^10 + x^9 + 432*x^3 + 9011
            sage: g = 13*x^11 + 89*x^3 + 1
            sage: F = f^2 * g^3
            sage: F = f^2 * g^3; F.factor()
            (12*x^10 + x^9 + 432*x^3 + 9011)^2 * (13*x^11 + 89*x^3 + 1)^3
            sage: F = f^2 * g^3 * 7; F.factor()
            7 * (12*x^10 + x^9 + 432*x^3 + 9011)^2 * (13*x^11 + 89*x^3 + 1)^3

        This example came up in :trac:`7097`::

            sage: x = polygen(QQ)
            sage: f = 8*x^9 + 42*x^6 + 6*x^3 - 1
            sage: g = x^24 - 12*x^23 + 72*x^22 - 286*x^21 + 849*x^20 - 2022*x^19 + 4034*x^18 - 6894*x^17 + 10182*x^16 - 13048*x^15 + 14532*x^14 - 13974*x^13 + 11365*x^12 - 7578*x^11 + 4038*x^10 - 1766*x^9 + 762*x^8 - 408*x^7 + 236*x^6 - 126*x^5 + 69*x^4 - 38*x^3 + 18*x^2 - 6*x + 1
            sage: assert g.is_irreducible()
            sage: K.<a> = NumberField(g)
            sage: len(f.roots(K))
            9
            sage: f.factor()
            (8) * (x^3 + 1/4) * (x^6 + 5*x^3 - 1/2)
            sage: f.change_ring(K).factor()
            (8) * (x - 3260097/3158212*a^22 + 35861067/3158212*a^21 - 197810817/3158212*a^20 + 722970825/3158212*a^19 - 1980508347/3158212*a^18 + 4374189477/3158212*a^17 - 4059860553/1579106*a^16 + 6442403031/1579106*a^15 - 17542341771/3158212*a^14 + 20537782665/3158212*a^13 - 20658463789/3158212*a^12 + 17502836649/3158212*a^11 - 11908953451/3158212*a^10 + 6086953981/3158212*a^9 - 559822335/789553*a^8 + 194545353/789553*a^7 - 505969453/3158212*a^6 + 338959407/3158212*a^5 - 155204647/3158212*a^4 + 79628015/3158212*a^3 - 57339525/3158212*a^2 + 26692783/3158212*a - 1636338/789553) * ...
            sage: f = QQbar['x'](1)
            sage: f.factor()
            1

        Factorization also works even if the variable of the finite
        field is nefariously labeled "x"::

            sage: R.<x> = GF(3^2, 'x')[]
            sage: f = x^10 +7*x -13
            sage: G = f.factor(); G
            (x + x) * (x + 2*x + 1) * (x^4 + (x + 2)*x^3 + (2*x + 2)*x + 2) * (x^4 + 2*x*x^3 + (x + 1)*x + 2)
            sage: prod(G) == f
            True

        ::

            sage: R.<x0> = GF(9,'x')[]  # purposely calling it x to test robustness
            sage: f = x0^3 + x0 + 1
            sage: f.factor()
            (x0 + 2) * (x0 + x) * (x0 + 2*x + 1)
            sage: f = 0*x0
            sage: f.factor()
            Traceback (most recent call last):
            ...
            ValueError: factorization of 0 not defined

        ::

            sage: f = x0^0
            sage: f.factor()
            1

        Over a complicated number field::

            sage: x = polygen(QQ, 'x')
            sage: f = x^6 + 10/7*x^5 - 867/49*x^4 - 76/245*x^3 + 3148/35*x^2 - 25944/245*x + 48771/1225
            sage: K.<a> = NumberField(f)
            sage: S.<T> = K[]
            sage: ff = S(f); ff
            T^6 + 10/7*T^5 - 867/49*T^4 - 76/245*T^3 + 3148/35*T^2 - 25944/245*T + 48771/1225
            sage: F = ff.factor()
            sage: len(F)
            4
            sage: F[:2]
            [(T - a, 1), (T - 40085763200/924556084127*a^5 - 145475769880/924556084127*a^4 + 527617096480/924556084127*a^3 + 1289745809920/924556084127*a^2 - 3227142391585/924556084127*a - 401502691578/924556084127, 1)]
            sage: expand(F)
            T^6 + 10/7*T^5 - 867/49*T^4 - 76/245*T^3 + 3148/35*T^2 - 25944/245*T + 48771/1225

        ::

            sage: f = x^2 - 1/3
            sage: K.<a> = NumberField(f)
            sage: A.<T> = K[]
            sage: A(x^2 - 1).factor()
            (T - 1) * (T + 1)


        ::

            sage: A(3*x^2 - 1).factor()
            (3) * (T - a) * (T + a)

        ::

            sage: A(x^2 - 1/3).factor()
            (T - a) * (T + a)

        Test that :trac:`10279` is fixed::

            sage: R.<t> = PolynomialRing(QQ)
            sage: K.<a> = NumberField(t^4 - t^2 + 1)
            sage: pol = t^3 + (-4*a^3 + 2*a)*t^2 - 11/3*a^2*t + 2/3*a^3 - 4/3*a
            sage: pol.factor()
            (t - 2*a^3 + a) * (t - 4/3*a^3 + 2/3*a) * (t - 2/3*a^3 + 1/3*a)

        Test that this factorization really uses ``nffactor()`` internally::

            sage: pari.default("debug", 3)
            sage: F = pol.factor()
            <BLANKLINE>
            Entering nffactor:
            ...
            sage: pari.default("debug", 0)

        Test that :trac:`10369` is fixed::

            sage: x = polygen(QQ)
            sage: K.<a> = NumberField(x^6 + x^5 + x^4 + x^3 + x^2 + x + 1)
            sage: R.<t> = PolynomialRing(K)

            sage: pol = (-1/7*a^5 - 1/7*a^4 - 1/7*a^3 - 1/7*a^2 - 2/7*a - 1/7)*t^10 + (4/7*a^5 - 2/7*a^4 - 2/7*a^3 - 2/7*a^2 - 2/7*a - 6/7)*t^9 + (90/49*a^5 + 152/49*a^4 + 18/49*a^3 + 24/49*a^2 + 30/49*a + 36/49)*t^8 + (-10/49*a^5 + 10/7*a^4 + 198/49*a^3 - 102/49*a^2 - 60/49*a - 26/49)*t^7 + (40/49*a^5 + 45/49*a^4 + 60/49*a^3 + 277/49*a^2 - 204/49*a - 78/49)*t^6 + (90/49*a^5 + 110/49*a^4 + 2*a^3 + 80/49*a^2 + 46/7*a - 30/7)*t^5 + (30/7*a^5 + 260/49*a^4 + 250/49*a^3 + 232/49*a^2 + 32/7*a + 8)*t^4 + (-184/49*a^5 - 58/49*a^4 - 52/49*a^3 - 66/49*a^2 - 72/49*a - 72/49)*t^3 + (18/49*a^5 - 32/49*a^4 + 10/49*a^3 + 4/49*a^2)*t^2 + (2/49*a^4 - 4/49*a^3 + 2/49*a^2)*t
            sage: pol.factor()
            (-1/7*a^5 - 1/7*a^4 - 1/7*a^3 - 1/7*a^2 - 2/7*a - 1/7) * t * (t - a^5 - a^4 - a^3 - a^2 - a - 1)^4 * (t^5 + (-12/7*a^5 - 10/7*a^4 - 8/7*a^3 - 6/7*a^2 - 4/7*a - 2/7)*t^4 + (12/7*a^5 - 8/7*a^3 + 16/7*a^2 + 2/7*a + 20/7)*t^3 + (-20/7*a^5 - 20/7*a^3 - 20/7*a^2 + 4/7*a - 2)*t^2 + (12/7*a^5 + 12/7*a^3 + 2/7*a + 16/7)*t - 4/7*a^5 - 4/7*a^3 - 4/7*a - 2/7)

            sage: pol = (1/7*a^2 - 1/7*a)*t^10 + (4/7*a - 6/7)*t^9 + (102/49*a^5 + 99/49*a^4 + 96/49*a^3 + 93/49*a^2 + 90/49*a + 150/49)*t^8 + (-160/49*a^5 - 36/49*a^4 - 48/49*a^3 - 8/7*a^2 - 60/49*a - 60/49)*t^7 + (30/49*a^5 - 55/49*a^4 + 20/49*a^3 + 5/49*a^2)*t^6 + (6/49*a^4 - 12/49*a^3 + 6/49*a^2)*t^5
            sage: pol.factor()
            (1/7*a^2 - 1/7*a) * t^5 * (t^5 + (-40/7*a^5 - 38/7*a^4 - 36/7*a^3 - 34/7*a^2 - 32/7*a - 30/7)*t^4 + (60/7*a^5 - 30/7*a^4 - 18/7*a^3 - 9/7*a^2 - 3/7*a)*t^3 + (60/7*a^4 - 40/7*a^3 - 16/7*a^2 - 4/7*a)*t^2 + (30/7*a^3 - 25/7*a^2 - 5/7*a)*t + 6/7*a^2 - 6/7*a)

            sage: pol = x^10 + (4/7*a - 6/7)*x^9 + (9/49*a^2 - 3/7*a + 15/49)*x^8 + (8/343*a^3 - 32/343*a^2 + 40/343*a - 20/343)*x^7 + (5/2401*a^4 - 20/2401*a^3 + 40/2401*a^2 - 5/343*a + 15/2401)*x^6 + (-6/16807*a^4 + 12/16807*a^3 - 18/16807*a^2 + 12/16807*a - 6/16807)*x^5
            sage: pol.factor()
            x^5 * (x^5 + (4/7*a - 6/7)*x^4 + (9/49*a^2 - 3/7*a + 15/49)*x^3 + (8/343*a^3 - 32/343*a^2 + 40/343*a - 20/343)*x^2 + (5/2401*a^4 - 20/2401*a^3 + 40/2401*a^2 - 5/343*a + 15/2401)*x - 6/16807*a^4 + 12/16807*a^3 - 18/16807*a^2 + 12/16807*a - 6/16807)

        Factoring over a number field over which we cannot factor the
        discriminant by trial division::

            sage: x = polygen(QQ)
            sage: K.<a> = NumberField(x^16 - x - 6)
            sage: R.<x> = PolynomialRing(K)
            sage: f = (x+a)^50 - (a-1)^50
            sage: len(factor(f))
            6
            sage: pari(K.discriminant()).factor(limit=10^6)
            [-1, 1; 3, 15; 23, 1; 887, 1; 12583, 1; 2354691439917211, 1]
            sage: factor(K.discriminant())
            -1 * 3^15 * 23 * 887 * 12583 * 6335047 * 371692813

        Factoring over a number field over which we cannot factor the
        discriminant and over which `nffactor()` fails::

            sage: p = next_prime(10^50); q = next_prime(10^51); n = p*q;
            sage: K.<a> = QuadraticField(p*q)
            sage: R.<x> = PolynomialRing(K)
            sage: K.pari_polynomial('a').nffactor("x^2+1")
            Mat([x^2 + 1, 1])
            sage: factor(x^2 + 1)
            x^2 + 1
            sage: factor( (x - a) * (x + 2*a) )
            (x - a) * (x + 2*a)

        A test where nffactor used to fail without a nf structure::

            sage: x = polygen(QQ)
            sage: K = NumberField([x^2-1099511627777, x^3-3],'a')
            sage: x = polygen(K)
            sage: f = x^3 - 3
            sage: factor(f)
            (x - a1) * (x^2 + a1*x + a1^2)

        We check that :trac:`7554` is fixed::

            sage: L.<q> = LaurentPolynomialRing(QQ)
            sage: F = L.fraction_field()
            sage: R.<x> = PolynomialRing(F)
            sage: factor(x)
            x
            sage: factor(x^2 - q^2)
            (-1) * (-x + q) * (x + q)
            sage: factor(x^2 - q^-2)
            (1/q^2) * (q*x - 1) * (q*x + 1)

            sage: P.<a,b,c> = PolynomialRing(ZZ)
            sage: R.<x> = PolynomialRing(FractionField(P))
            sage: p = (x - a)*(b*x + c)*(a*b*x + a*c) / (a + 2)
            sage: factor(p)
            (a/(a + 2)) * (x - a) * (b*x + c)^2
        """
        # PERFORMANCE NOTE:
        #     In many tests with SMALL degree PARI is substantially
        #     better than NTL.  (And magma is better yet.)  And the
        #     timing difference has nothing to do with moving Python
        #     data to NTL and back.
        #     For large degree ( > 1500) in the one test I tried, NTL was
        #     *much* better than MAGMA, and far better than PARI.  So probably
        #     NTL's implementation is asymptotically better.  I could use
        #     PARI for smaller degree over other rings besides Z, and use
        #     NTL in general.
        # A remark from Bill Hart (2007-09-25) about the above observation:
        ## NTL uses the Berlekamp-Zassenhaus method with van Hoeij's improvements.
        ## But so does Magma since about Jul 2001.
        ##
        ## But here's the kicker. PARI also uses this algorithm. Even Maple uses
        ## it!
        ##
        ## NTL's LLL algorithms are extremely well developed (van Hoeij uses
        ## LLL). There is also a possible speed difference in whether one uses
        ## quadratic convergence or not in the Hensel lift. But the right choice
        ## is not always what one thinks.
        ##
        ## But more than likely NTL is just better for large problems because
        ## Victor Shoup was very careful with the choice of strategies and
        ## parameters he used. Paul Zimmerman supplied him with a pile of
        ## polynomials to factor for comparison purposes and these seem to have
        ## been used to tune the algorithm for a wide range of inputs, including
        ## cases that van Hoeij's algorithm doesn't usually like.
        ##
        ## If you have a bound on the coefficients of the factors, one can surely
        ## do better than a generic implementation, but probably not much better
        ## if there are many factors.
        ##

        ## HUGE TODO, refactor the code below here such that this method will
        ## have as only the following code
        ##
        ## R = self.parent().base_ring()
        ## return R._factor_univariate_polynomial(self)
        ##
        ## in this way we can move the specific logic of factoring to the
        ## self.parent().base_ring() and get rid of all the ugly
        ## is_SomeType(R) checks and get way nicer structured code
        ## 200 lines of spagetti code is just way to much!

        if self.degree() < 0:
            raise ValueError("factorization of 0 not defined")
        if self.degree() == 0:
            return Factorization([], unit=self[0])

        # Use multivariate implementations for polynomials over polynomial rings
        variables = self._parent.variable_names_recursive()
        if len(variables) > 1:
            base = self._parent._mpoly_base_ring()
            ring = PolynomialRing(base, variables)
            if ring._has_singular:
                try:
                    d = self._mpoly_dict_recursive()
                    F = ring(d).factor(**kwargs)
                    return Factorization([(self._parent(f),m) for (f,m) in F], unit = F.unit())
                except NotImplementedError:
                    pass

        R = self.parent().base_ring()
        if hasattr(R, '_factor_univariate_polynomial'):
            return R._factor_univariate_polynomial(self, **kwargs)

        G = None
        ch = R.characteristic()
        if not (ch == 0 or is_prime(ch)):
            raise NotImplementedError("factorization of polynomials over rings with composite characteristic is not implemented")

        from sage.rings.number_field.number_field_base import is_NumberField
        from sage.rings.number_field.number_field_rel import is_RelativeNumberField
        from sage.rings.number_field.all import NumberField
        from sage.rings.finite_rings.finite_field_constructor import is_FiniteField
        from sage.rings.finite_rings.integer_mod_ring import is_IntegerModRing
        from sage.rings.integer_ring import is_IntegerRing

        n = None

        if is_IntegerModRing(R) or is_IntegerRing(R):
            try:
                G = list(self._pari_with_name().factor())
            except PariError:
                raise NotImplementedError

        elif is_RelativeNumberField(R):

            M = R.absolute_field('a')
            from_M, to_M = M.structure()
            g = M['x']([to_M(x) for x in self.list()])
            F = g.factor()
            S = self.parent()
            v = [(S([from_M(x) for x in f.list()]), e) for f, e in F]
            return Factorization(v, from_M(F.unit()))

        elif is_FiniteField(R):
            v = [x._pari_("a") for x in self.list()]
            f = pari(v).Polrev()
            G = list(f.factor())

        elif is_NumberField(R):
            if R.degree() == 1:
                factors = self.change_ring(QQ).factor()
                return Factorization([(self._parent(p), e) for p, e in factors], R(factors.unit()))

            # Convert the polynomial we want to factor to PARI
            f = self._pari_with_name()
            try:
                try:
                    # Try to compute the PARI nf structure with important=False.
                    # This will raise RuntimeError if the computation is too
                    # difficult.  It will raise TypeError if the defining
                    # polynomial is not integral.
                    Rpari = R.pari_nf(important=False)
                except RuntimeError:
                    # Cannot easily compute the nf structure, use the defining
                    # polynomial instead.
                    Rpari = R.pari_polynomial("y")
                # nffactor() can fail with PariError "precision too low"
                G = list(Rpari.nffactor(f))
            except (PariError, TypeError):
                # Use factornf() which only needs the defining polynomial,
                # which does not require an integral polynomial and which
                # has no problems with floating-point precision.
                G = list(f.factornf(R.pari_polynomial("y")))
            # PARI's nffactor() ignores the unit, _factor_pari_helper()
            # adds back the unit of the factorization.
            return self._factor_pari_helper(G)

        if G is None:
            # See if we can do this as a singular polynomial as a fallback
            # This was copied from the general multivariate implementation
            try:
                if R.is_finite():
                    if R.characteristic() > 1<<29:
                        raise NotImplementedError("Factorization of multivariate polynomials over prime fields with characteristic > 2^29 is not implemented.")

                P = self.parent()
                P._singular_().set_ring()
                S = self._singular_().factorize()
                factors = S[1]
                exponents = S[2]
                v = sorted([( P(factors[i+1]),
                              sage.rings.integer.Integer(exponents[i+1]))
                            for i in range(len(factors))])
                unit = P.one()
                for i in range(len(v)):
                    if v[i][0].is_unit():
                        unit = unit * v[i][0]
                        del v[i]
                        break
                F = Factorization(v, unit=unit)
                F.sort()
                return F
            except (TypeError, AttributeError):
                raise NotImplementedError

        return self._factor_pari_helper(G, n)

    def _factor_pari_helper(self, G, n=None, unit=None):
        """
        Fix up and normalize a factorization that came from PARI.

        TESTS::

            sage: R.<x>=PolynomialRing(ZZ)
            sage: f = (2*x + 1) * (3*x^2 - 5)^2
            sage: f._factor_pari_helper(pari(f).factor())
            (2*x + 1) * (3*x^2 - 5)^2
            sage: f._factor_pari_helper(pari(f).factor(), unit=11)
            11 * (2*x + 1) * (3*x^2 - 5)^2
            sage: (8*f)._factor_pari_helper(pari(f).factor())
            8 * (2*x + 1) * (3*x^2 - 5)^2
            sage: (8*f)._factor_pari_helper(pari(f).factor(), unit=11)
            88 * (2*x + 1) * (3*x^2 - 5)^2
            sage: QQ['x'](f)._factor_pari_helper(pari(f).factor())
            (18) * (x + 1/2) * (x^2 - 5/3)^2
            sage: QQ['x'](f)._factor_pari_helper(pari(f).factor(), unit=11)
            (198) * (x + 1/2) * (x^2 - 5/3)^2

            sage: f = prod((k^2*x^k + k)^(k-1) for k in primes(10))
            sage: F = f._factor_pari_helper(pari(f).factor()); F
            1323551250 * (2*x^2 + 1) * (3*x^3 + 1)^2 * (5*x^5 + 1)^4 * (7*x^7 + 1)^6
            sage: F.prod() == f
            True
            sage: QQ['x'](f)._factor_pari_helper(pari(f).factor())
            (1751787911376562500) * (x^2 + 1/2) * (x^3 + 1/3)^2 * (x^5 + 1/5)^4 * (x^7 + 1/7)^6

            sage: g = GF(19)['x'](f)
            sage: G = g._factor_pari_helper(pari(g).factor()); G
            (4) * (x + 3) * (x + 16)^5 * (x + 11)^6 * (x^2 + 7*x + 9)^4 * (x^2 + 15*x + 9)^4 * (x^3 + 13)^2 * (x^6 + 8*x^5 + 7*x^4 + 18*x^3 + 11*x^2 + 12*x + 1)^6
            sage: G.prod() == g
            True
        """
        pols = G[0]
        exps = G[1]
        R = self.parent()
        F = [(R(f), int(e)) for f, e in zip(pols, exps)]

        if unit is None:
            unit = self.leading_coefficient()
        else:
            unit *= self.leading_coefficient()

        if R.base_ring().is_field():
            # When the base ring is a field we normalize
            # the irreducible factors so they have leading
            # coefficient 1.
            for i, (f, e) in enumerate(F):
                if not f.is_monic():
                    F[i] = (f.monic(), e)

        else:
            # Otherwise we have to adjust for
            # the content ignored by PARI.
            content_fix = R.base_ring().one()
            for f, e in F:
                if not f.is_monic():
                    content_fix *= f.leading_coefficient()**e
            unit //= content_fix
            if not unit.is_unit():
                F.append((R(unit), ZZ(1)))
                unit = R.base_ring().one()

        if not n is None:
            pari.set_real_precision(n)  # restore precision
        return Factorization(F, unit)

    @coerce_binop
    def gcd(self, other):
        """
        Compute a greatest common divisor of ``self`` and ``other``.

        INPUT:

            - ``other`` -- a polynomial in the same ring as ``self``

        OUTPUT:

            A greatest common divisor of ``self`` and ``other`` as a polynomial
            in the same ring as ``self``. Over a field, the return value will
            be a monic polynomial.

        .. NOTE::

            The actual algorithm for computing greatest common divisors depends
            on the base ring underlying the polynomial ring. If the base ring
            defines a method ``_gcd_univariate_polynomial``, then this method
            will be called (see examples below).

        EXAMPLES::

            sage: R.<x> = QQ[]
            sage: (2*x^2).gcd(2*x)
            x
            sage: R.zero().gcd(0)
            0
            sage: (2*x).gcd(0)
            x

            One can easily add gcd functionality to new rings by providing a
            method ``_gcd_univariate_polynomial``::

            sage: R.<x> = QQ[]
            sage: S.<y> = R[]
            sage: h1 = y*x
            sage: h2 = y^2*x^2
            sage: h1.gcd(h2)
            Traceback (most recent call last):
            ...
            NotImplementedError: Univariate Polynomial Ring in x over Rational Field does not provide a gcd implementation for univariate polynomials
            sage: T.<x,y> = QQ[]
            sage: R._gcd_univariate_polynomial = lambda f,g: S(T(f).gcd(g))
            sage: h1.gcd(h2)
            x*y
            sage: del R._gcd_univariate_polynomial

        """
        if hasattr(self.base_ring(), '_gcd_univariate_polynomial'):
            return self.base_ring()._gcd_univariate_polynomial(self, other)
        else:
            raise NotImplementedError("%s does not provide a gcd implementation for univariate polynomials"%self.base_ring())
    def splitting_field(self, names, map=False, **kwds):
        """
        Compute the absolute splitting field of a given polynomial.

        INPUT:

        - ``names`` -- a variable name for the splitting field.

        - ``map`` -- (default: ``False``) also return an embedding of
          ``self`` into the resulting field.

        - ``kwds`` -- additional keywords depending on the type.
          Currently, only number fields are implemented. See
          :func:`sage.rings.number_field.splitting_field.splitting_field`
          for the documentation of these keywords.

        OUTPUT:

        If ``map`` is ``False``, the splitting field as an absolute field.
        If ``map`` is ``True``, a tuple ``(K, phi)`` where ``phi`` is an
        embedding of the base field of ``self`` in ``K``.

        EXAMPLES::

            sage: R.<x> = PolynomialRing(ZZ)
            sage: K.<a> = (x^3 + 2).splitting_field(); K
            Number Field in a with defining polynomial x^6 + 3*x^5 + 6*x^4 + 11*x^3 + 12*x^2 - 3*x + 1
            sage: K.<a> = (x^3 - 3*x + 1).splitting_field(); K
            Number Field in a with defining polynomial x^3 - 3*x + 1

        Relative situation::

            sage: R.<x> = PolynomialRing(QQ)
            sage: K.<a> = NumberField(x^3 + 2)
            sage: S.<t> = PolynomialRing(K)
            sage: L.<b> = (t^2 - a).splitting_field()
            sage: L
            Number Field in b with defining polynomial t^6 + 2

        With ``map=True``, we also get the embedding of the base field
        into the splitting field::

            sage: L.<b>, phi = (t^2 - a).splitting_field(map=True)
            sage: phi
            Ring morphism:
              From: Number Field in a with defining polynomial x^3 + 2
              To:   Number Field in b with defining polynomial t^6 + 2
              Defn: a |--> b^2

        An example over a finite field::

            sage: P.<x> = PolynomialRing(GF(7))
            sage: t = x^2 + 1
            sage: t.splitting_field('b')
            Finite Field in b of size 7^2

            sage: P.<x> = PolynomialRing(GF(7^3, 'a'))
            sage: t = x^2 + 1
            sage: t.splitting_field('b', map=True)
            (Finite Field in b of size 7^6,
             Ring morphism:
               From: Finite Field in a of size 7^3
               To:   Finite Field in b of size 7^6
               Defn: a |--> 2*b^4 + 6*b^3 + 2*b^2 + 3*b + 2)

        If the extension is trivial and the generators have the same
        name, the map will be the identity::

            sage: t = 24*x^13 + 2*x^12 + 14
            sage: t.splitting_field('a', map=True)
            (Finite Field in a of size 7^3,
             Identity endomorphism of Finite Field in a of size 7^3)

            sage: t = x^56 - 14*x^3
            sage: t.splitting_field('b', map=True)
            (Finite Field in b of size 7^3,
             Ring morphism:
             From: Finite Field in a of size 7^3
               To:   Finite Field in b of size 7^3
               Defn: a |--> b)

        .. SEEALSO::

            :func:`sage.rings.number_field.splitting_field.splitting_field` for more examples over number fields

        TESTS::

            sage: K.<a,b> = x.splitting_field()
            Traceback (most recent call last):
            ...
            IndexError: the number of names must equal the number of generators
            sage: polygen(RR).splitting_field('x')
            Traceback (most recent call last):
            ...
            NotImplementedError: splitting_field() is only implemented over number fields and finite fields

            sage: P.<x> = PolynomialRing(GF(11^5, 'a'))
            sage: t = x^2 + 1
            sage: t.splitting_field('b')
            Finite Field in b of size 11^10
            sage: t = 24*x^13 + 2*x^12 + 14
            sage: t.splitting_field('b')
            Finite Field in b of size 11^30
            sage: t = x^56 - 14*x^3
            sage: t.splitting_field('b')
            Finite Field in b of size 11^130

            sage: P.<x> = PolynomialRing(GF(19^6, 'a'))
            sage: t = -x^6 + x^2 + 1
            sage: t.splitting_field('b')
            Finite Field in b of size 19^6
            sage: t = 24*x^13 + 2*x^12 + 14
            sage: t.splitting_field('b')
            Finite Field in b of size 19^18
            sage: t = x^56 - 14*x^3
            sage: t.splitting_field('b')
            Finite Field in b of size 19^156

            sage: P.<x> = PolynomialRing(GF(83^6, 'a'))
            sage: t = 2*x^14 - 5 + 6*x
            sage: t.splitting_field('b')
            Finite Field in b of size 83^84
            sage: t = 24*x^13 + 2*x^12 + 14
            sage: t.splitting_field('b')
            Finite Field in b of size 83^78
            sage: t = x^56 - 14*x^3
            sage: t.splitting_field('b')
            Finite Field in b of size 83^12

            sage: P.<x> = PolynomialRing(GF(401^13, 'a'))
            sage: t = 2*x^14 - 5 + 6*x
            sage: t.splitting_field('b')
            Finite Field in b of size 401^104
            sage: t = 24*x^13 + 2*x^12 + 14
            sage: t.splitting_field('b')
            Finite Field in b of size 401^156
            sage: t = x^56 - 14*x^3
            sage: t.splitting_field('b')
            Finite Field in b of size 401^52

        """
        name = normalize_names(1, names)[0]

        from sage.rings.number_field.number_field_base import is_NumberField
        from sage.rings.finite_rings.finite_field_base import is_FiniteField

        f = self.monic()            # Given polynomial, made monic
        F = f.parent().base_ring()  # Base field
        if not F.is_field():
            F = F.fraction_field()
            f = self.change_ring(F)

        if is_NumberField(F):
            from sage.rings.number_field.splitting_field import splitting_field
            return splitting_field(f, name, map, **kwds)
        elif is_FiniteField(F):
            degree = lcm([f.degree() for f, _ in self.factor()])
            return F.extension(degree, name, map=map, **kwds)

        raise NotImplementedError("splitting_field() is only implemented over number fields and finite fields")

    def pseudo_quo_rem(self,other):
        """
        Compute the pseudo-division of two polynomials.

        INPUT:

        - ``other`` -- a nonzero polynomial

        OUTPUT:

        `Q` and `R` such that `l^{m-n+1} \mathrm{self} = Q \cdot\mathrm{other} + R`
        where `m` is the degree of this polynomial, `n` is the degree of
        ``other``, `l` is the leading coefficient of ``other``. The result is
        such that `\deg(R) < \deg(\mathrm{other})`.

        ALGORITHM:

        Algorithm 3.1.2 in [GTM138]_.

        EXAMPLES::

            sage: R.<x> = PolynomialRing(ZZ, sparse=True)
            sage: p = x^4 + 6*x^3 + x^2 - x + 2
            sage: q = 2*x^2 - 3*x - 1
            sage: (quo,rem)=p.pseudo_quo_rem(q); quo,rem
            (4*x^2 + 30*x + 51, 175*x + 67)
            sage: 2^(4-2+1)*p == quo*q + rem
            True

            sage: S.<T> = R[]
            sage: p = (-3*x^2 - x)*T^3 - 3*x*T^2 + (x^2 - x)*T + 2*x^2 + 3*x - 2
            sage: q = (-x^2 - 4*x - 5)*T^2 + (6*x^2 + x + 1)*T + 2*x^2 - x
            sage: quo,rem=p.pseudo_quo_rem(q); quo,rem
            ((3*x^4 + 13*x^3 + 19*x^2 + 5*x)*T + 18*x^4 + 12*x^3 + 16*x^2 + 16*x,
             (-113*x^6 - 106*x^5 - 133*x^4 - 101*x^3 - 42*x^2 - 41*x)*T - 34*x^6 + 13*x^5 + 54*x^4 + 126*x^3 + 134*x^2 - 5*x - 50)
            sage: (-x^2 - 4*x - 5)^(3-2+1) * p == quo*q + rem
            True

        REFERENCES:

        .. [GTM138] Henri Cohen. A Course in Computational Number Theory.
           Graduate Texts in Mathematics, vol. 138. Springer, 1993.
        """
        if other.is_zero():
            raise ZeroDivisionError("Pseudo-division by zero is not possible")

        # if other is a constant, then R = 0 and Q = self * other^(deg(self))
        if other in self.parent().base_ring():
            return (self * other**(self.degree()), self.parent().zero())

        R = self
        B = other
        Q = self.parent().zero()
        e = self.degree() - other.degree() + 1
        d = B.leading_coefficient()

        while not R.degree() < B.degree():
            c = R.leading_coefficient()
            diffdeg = R.degree() - B.degree()
            Q = d*Q + self.parent()(c).shift(diffdeg)
            R = d*R - c*B.shift(diffdeg)
            e -= 1

        q = d**e
        return (q*Q,q*R)

    @coerce_binop
    def gcd(self, other):
        """
        Return a greatest common divisor of this polynomial and ``other``.

        INPUT:

        - ``other`` -- a polynomial in the same ring as this polynomial

        OUTPUT:

        A greatest common divisor as a polynomial in the same ring as
        this polynomial. If the base ring is a field, the return value
        is a monic polynomial.

        .. NOTE::

            The actual algorithm for computing greatest common divisors depends
            on the base ring underlying the polynomial ring. If the base ring
            defines a method ``_gcd_univariate_polynomial``, then this method
            will be called (see examples below).

        EXAMPLES::

            sage: R.<x> = QQ[]
            sage: (2*x^2).gcd(2*x)
            x
            sage: R.zero().gcd(0)
            0
            sage: (2*x).gcd(0)
            x

        One can easily add gcd functionality to new rings by providing a method
        ``_gcd_univariate_polynomial``::

            sage: O = ZZ[-sqrt(5)]
            sage: R.<x> = O[]
            sage: a = O.1
            sage: p = x + a
            sage: q = x^2 - 5
            sage: p.gcd(q)
            Traceback (most recent call last):
            ...
            NotImplementedError: Order in Number Field in a with defining polynomial x^2 - 5 does not provide a gcd implementation for univariate polynomials
            sage: S.<x> = O.number_field()[]
            sage: O._gcd_univariate_polynomial = lambda f,g : R(S(f).gcd(S(g)))
            sage: p.gcd(q)
            x + a
            sage: del O._gcd_univariate_polynomial

        Use multivariate implementation for polynomials over polynomials rings::

            sage: R.<x> = ZZ[]
            sage: S.<y> = R[]
            sage: T.<z> = S[]
            sage: r = 2*x*y + z
            sage: p = r * (3*x*y*z - 1)
            sage: q = r * (x + y + z - 2)
            sage: p.gcd(q)
            z + 2*x*y

            sage: R.<x> = QQ[]
            sage: S.<y> = R[]
            sage: r = 2*x*y + 1
            sage: p = r * (x - 1/2 * y)
            sage: q = r * (x*y^2 - x + 1/3)
            sage: p.gcd(q)
            2*x*y + 1
        """
        variables = self._parent.variable_names_recursive()
        if len(variables) > 1:
            base = self._parent._mpoly_base_ring()
            ring = PolynomialRing(base, variables)
            if ring._has_singular:
                try:
                    d1 = self._mpoly_dict_recursive()
                    d2 = other._mpoly_dict_recursive()
                    return self._parent(ring(d1).gcd(ring(d2)))
                except NotImplementedError:
                    pass

        if hasattr(self.base_ring(), '_gcd_univariate_polynomial'):
            return self.base_ring()._gcd_univariate_polynomial(self, other)
        else:
            raise NotImplementedError("%s does not provide a gcd implementation for univariate polynomials"%self.base_ring())

    @coerce_binop
    def lcm(self, other):
        """
        Let f and g be two polynomials. Then this function returns the
        monic least common multiple of f and g.
        """
        f = self*other
        g = self.gcd(other)
        q = f//g
        return ~(q.leading_coefficient())*q

    def _lcm(self, other):
        """
        Let f and g be two polynomials. Then this function returns the
        monic least common multiple of f and g.
        """
        f = self*other
        g = self.gcd(other)
        q = f//g
        return ~(q.leading_coefficient())*q  # make monic  (~ is inverse in python)

    def is_primitive(self, n=None, n_prime_divs=None):
        """
        Returns ``True`` if the polynomial is primitive.  The semantics of
        "primitive" depend on the polynomial coefficients.

        - (field theory) A polynomial of degree `m` over a finite field
          `\GF{q}` is primitive if it is irreducible and its root in
          `\GF{q^m}` generates the multiplicative group `\GF{q^m}^*`.

        - (ring theory) A polynomial over a ring is primitive if its
          coefficients generate the unit ideal.

        Calling `is_primitive` on a polynomial over an infinite field will
        raise an error.

        The additional inputs to this function are to speed up computation for
        field semantics (see note).

        INPUT:

          - ``n`` (default: ``None``) - if provided, should equal
            `q-1` where ``self.parent()`` is the field with `q`
            elements;  otherwise it will be computed.

          - ``n_prime_divs`` (default: ``None``) - if provided, should
            be a list of the prime divisors of ``n``; otherwise it
            will be computed.

        .. note::

          Computation of the prime divisors of ``n`` can dominate the running
          time of this method, so performing this computation externally
          (e.g. ``pdivs=n.prime_divisors()``) is a good idea for repeated calls
          to is_primitive for polynomials of the same degree.

          Results may be incorrect if the wrong ``n`` and/or factorization are
          provided.

        EXAMPLES::

          Field semantics examples.

          ::

            sage: R.<x> = GF(2)['x']
            sage: f = x^4+x^3+x^2+x+1
            sage: f.is_irreducible(), f.is_primitive()
            (True, False)
            sage: f = x^3+x+1
            sage: f.is_irreducible(), f.is_primitive()
            (True, True)
            sage: R.<x> = GF(3)[]
            sage: f = x^3-x+1
            sage: f.is_irreducible(), f.is_primitive()
            (True, True)
            sage: f = x^2+1
            sage: f.is_irreducible(), f.is_primitive()
            (True, False)
            sage: R.<x> = GF(5)[]
            sage: f = x^2+x+1
            sage: f.is_primitive()
            False
            sage: f = x^2-x+2
            sage: f.is_primitive()
            True
            sage: x=polygen(QQ); f=x^2+1
            sage: f.is_primitive()
            Traceback (most recent call last):
            ...
            NotImplementedError: is_primitive() not defined for polynomials over infinite fields.

          Ring semantics examples.

          ::

            sage: x=polygen(ZZ)
            sage: f = 5*x^2+2
            sage: f.is_primitive()
            True
            sage: f = 5*x^2+5
            sage: f.is_primitive()
            False

            sage: K=NumberField(x^2+5,'a')
            sage: R=K.ring_of_integers()
            sage: a=R.gen(1)
            sage: a^2
            -5
            sage: f=a*x+2
            sage: f.is_primitive()
            True
            sage: f=(1+a)*x+2
            sage: f.is_primitive()
            False

            sage: x=polygen(Integers(10));
            sage: f=5*x^2+2
            sage: #f.is_primitive()  #BUG:: elsewhere in Sage, should return True
            sage: f=4*x^2+2
            sage: #f.is_primitive()  #BUG:: elsewhere in Sage, should return False

        TESTS::

            sage: R.<x> = GF(2)['x']
            sage: f = x^4+x^3+x^2+x+1
            sage: f.is_primitive(15)
            False
            sage: f.is_primitive(15, [3,5])
            False
            sage: f.is_primitive(n_prime_divs=[3,5])
            False
            sage: f = x^3+x+1
            sage: f.is_primitive(7, [7])
            True
            sage: R.<x> = GF(3)[]
            sage: f = x^3-x+1
            sage: f.is_primitive(26, [2,13])
            True
            sage: f = x^2+1
            sage: f.is_primitive(8, [2])
            False
            sage: R.<x> = GF(5)[]
            sage: f = x^2+x+1
            sage: f.is_primitive(24, [2,3])
            False
            sage: f = x^2-x+2
            sage: f.is_primitive(24, [2,3])
            True
            sage: x=polygen(Integers(103)); f=x^2+1
            sage: f.is_primitive()
            False
        """
        R = self.base_ring()
        if R.is_field():
            if not R.is_finite():
                raise NotImplementedError("is_primitive() not defined for polynomials over infinite fields.")

            if not self.is_irreducible():
                return False
            if n is None:
                q = self.base_ring().order()
                n = q ** self.degree() - 1
            y = self.parent().quo(self).gen()
            from sage.groups.generic import order_from_multiple
            return n == order_from_multiple(y, n, n_prime_divs, operation="*")
        else:
            return R.ideal(self.coefficients())==R.ideal(1)

    def is_constant(self):
        """
        Return True if this is a constant polynomial.

        OUTPUT:


        -  ``bool`` - True if and only if this polynomial is
           constant


        EXAMPLES::

            sage: R.<x> = ZZ[]
            sage: x.is_constant()
            False
            sage: R(2).is_constant()
            True
            sage: R(0).is_constant()
            True
        """
        return self.degree() <= 0

    def is_monomial(self):
        """
        Returns True if self is a monomial, i.e., a power of the generator.

        EXAMPLES::

            sage: R.<x> = QQ[]
            sage: x.is_monomial()
            True
            sage: (x+1).is_monomial()
            False
            sage: (x^2).is_monomial()
            True
            sage: R(1).is_monomial()
            True

        The coefficient must be 1::

            sage: (2*x^5).is_monomial()
            False

        To allow a non-1 leading coefficient, use is_term()::

            sage: (2*x^5).is_term()
            True

        .. warning::

           The definition of is_monomial in Sage up to 4.7.1 was the
           same as is_term, i.e., it allowed a coefficient not equal
           to 1.
        """
        return len(self.exponents()) == 1 and self.leading_coefficient() == 1

    def is_term(self):
        """
        Return True if self is an element of the base ring times a
        power of the generator.

        EXAMPLES::

            sage: R.<x> = QQ[]
            sage: x.is_term()
            True
            sage: R(1).is_term()
            True
            sage: (3*x^5).is_term()
            True
            sage: (1+3*x^5).is_term()
            False

        To require that the coefficient is 1, use is_monomial() instead::

            sage: (3*x^5).is_monomial()
            False
        """
        return len(self.exponents()) == 1

    def root_field(self, names, check_irreducible=True):
        """
        Return the field generated by the roots of the irreducible
        polynomial self. The output is either a number field, relative
        number field, a quotient of a polynomial ring over a field, or the
        fraction field of the base ring.

        EXAMPLES::

            sage: R.<x> = QQ['x']
            sage: f = x^3 + x + 17
            sage: f.root_field('a')
            Number Field in a with defining polynomial x^3 + x + 17

        ::

            sage: R.<x> = QQ['x']
            sage: f = x - 3
            sage: f.root_field('b')
            Rational Field

        ::

            sage: R.<x> = ZZ['x']
            sage: f = x^3 + x + 17
            sage: f.root_field('b')
            Number Field in b with defining polynomial x^3 + x + 17

        ::

            sage: y = QQ['x'].0
            sage: L.<a> = NumberField(y^3-2)
            sage: R.<x> = L['x']
            sage: f = x^3 + x + 17
            sage: f.root_field('c')
            Number Field in c with defining polynomial x^3 + x + 17 over its base field

        ::

            sage: R.<x> = PolynomialRing(GF(9,'a'))
            sage: f = x^3 + x^2 + 8
            sage: K.<alpha> = f.root_field(); K
            Univariate Quotient Polynomial Ring in alpha over Finite Field in a of size 3^2 with modulus x^3 + x^2 + 2
            sage: alpha^2 + 1
            alpha^2 + 1
            sage: alpha^3 + alpha^2
            1

        ::

            sage: R.<x> = QQ[]
            sage: f = x^2
            sage: K.<alpha> = f.root_field()
            Traceback (most recent call last):
            ...
            ValueError: polynomial must be irreducible

        TESTS::

            sage: (PolynomialRing(Integers(31),name='x').0+5).root_field('a')
            Ring of integers modulo 31
        """
        from sage.rings.number_field.number_field import is_NumberField, NumberField

        R = self.base_ring()
        if not R.is_integral_domain():
            raise ValueError("the base ring must be a domain")

        if check_irreducible and not self.is_irreducible():
            raise ValueError("polynomial must be irreducible")

        if self.degree() <= 1:
            return R.fraction_field()

        if sage.rings.integer_ring.is_IntegerRing(R):
            return NumberField(self, names)

        if sage.rings.rational_field.is_RationalField(R) or is_NumberField(R):
            return NumberField(self, names)

        return R.fraction_field()[self.parent().variable_name()].quotient(self, names)

    def sylvester_matrix(self, right, variable = None):
        """
        Returns the Sylvester matrix of self and right.

        Note that the Sylvester matrix is not defined if one of the polynomials
        is zero.

        INPUT:

        - right: a polynomial in the same ring as self.
        - variable: optional, included for compatibility with the multivariate
          case only. The variable of the polynomials.

        EXAMPLES::

            sage: R.<x> = PolynomialRing(ZZ)
            sage: f = (6*x + 47)*(7*x^2 - 2*x + 38)
            sage: g = (6*x + 47)*(3*x^3 + 2*x + 1)
            sage: M = f.sylvester_matrix(g)
            sage: M
            [  42  317  134 1786    0    0    0]
            [   0   42  317  134 1786    0    0]
            [   0    0   42  317  134 1786    0]
            [   0    0    0   42  317  134 1786]
            [  18  141   12  100   47    0    0]
            [   0   18  141   12  100   47    0]
            [   0    0   18  141   12  100   47]

        If the polynomials share a non-constant common factor then the
        determinant of the Sylvester matrix will be zero::

            sage: M.determinant()
            0

        If self and right are polynomials of positive degree, the determinant
        of the Sylvester matrix is the resultant of the polynomials.::

            sage: h1 = R.random_element()
            sage: h2 = R.random_element()
            sage: M1 = h1.sylvester_matrix(h2)
            sage: M1.determinant() == h1.resultant(h2)
            True

        The rank of the Sylvester matrix is related to the degree of the
        gcd of self and right::

            sage: f.gcd(g).degree() == f.degree() + g.degree() - M.rank()
            True
            sage: h1.gcd(h2).degree() == h1.degree() + h2.degree() - M1.rank()
            True

        TESTS:

        The variable is optional, but must be the same in both rings::

            sage: K.<x> = QQ['x']
            sage: f = x+1
            sage: g = QQ['y']([1, 0, 1])
            sage: f.sylvester_matrix(f, x)
            [1 1]
            [1 1]
            sage: f.sylvester_matrix(g, x)
            Traceback (most recent call last):
            ...
            TypeError: no common canonical parent for objects with parents: 'Univariate Polynomial Ring in x over Rational Field' and 'Univariate Polynomial Ring in y over Rational Field'

        Polynomials must be defined over compatible base rings::

            sage: f = QQ['x']([1, 0, 1])
            sage: g = ZZ['x']([1, 0, 1])
            sage: h = GF(25, 'a')['x']([1, 0, 1])
            sage: f.sylvester_matrix(g)
            [1 0 1 0]
            [0 1 0 1]
            [1 0 1 0]
            [0 1 0 1]
            sage: g.sylvester_matrix(h)
            [1 0 1 0]
            [0 1 0 1]
            [1 0 1 0]
            [0 1 0 1]
            sage: f.sylvester_matrix(h)
            Traceback (most recent call last):
            ...
            TypeError: no common canonical parent for objects with parents: 'Univariate Polynomial Ring in x over Rational Field' and 'Univariate Polynomial Ring in x over Finite Field in a of size 5^2'

        We can compute the sylvester matrix of a univariate and multivariate
        polynomial::

            sage: K.<x,y> = QQ['x,y']
            sage: g = K.random_element()
            sage: f.sylvester_matrix(g) == K(f).sylvester_matrix(g,x)
            True

        Corner cases::

            sage: K.<x>=QQ[]
            sage: f = x^2+1
            sage: g = K(0)
            sage: f.sylvester_matrix(g)
            Traceback (most recent call last):
            ...
            ValueError: The Sylvester matrix is not defined for zero polynomials
            sage: g.sylvester_matrix(f)
            Traceback (most recent call last):
            ...
            ValueError: The Sylvester matrix is not defined for zero polynomials
            sage: g.sylvester_matrix(g)
            Traceback (most recent call last):
            ...
            ValueError: The Sylvester matrix is not defined for zero polynomials
            sage: K(3).sylvester_matrix(x^2)
            [3 0]
            [0 3]
            sage: K(3).sylvester_matrix(K(4))
            []
        """

        # This code is almost exactly the same as that of
        # sylvester_matrix() in multi_polynomial.pyx.

        if self.parent() != right.parent():
            a, b = coercion_model.canonical_coercion(self,right)
            variable = a.parent()(self.variables()[0])
            #We add the variable to cover the case that right is a multivariate
            #polynomial
            return a.sylvester_matrix(b, variable)

        if variable:
            if variable.parent() != self.parent():
                variable = self.parent()(variable)

        from sage.matrix.constructor import matrix

        # The dimension of the sage matrix is self.degree() + right.degree()

        if self.is_zero() or right.is_zero():
            raise ValueError("The Sylvester matrix is not defined for zero polynomials")

        m = self.degree()
        n = right.degree()

        M = matrix(self.base_ring(), n + m, n + m)

        r = 0
        offset = 0
        for _ in range(n):
            for c in range(m, -1, -1):
                M[r, m - c + offset] = self[c]
            offset += 1
            r += 1

        offset = 0
        for _ in range(m):
            for c in range(n, -1, -1):
                M[r, n - c + offset] = right[c]
            offset += 1
            r += 1

        return M

    cpdef constant_coefficient(self):
        """
        Return the constant coefficient of this polynomial.

        OUTPUT: element of base ring

        EXAMPLES::

            sage: R.<x> = QQ[]
            sage: f = -2*x^3 + 2*x - 1/3
            sage: f.constant_coefficient()
            -1/3
        """
        return self[0]

    cpdef Polynomial _new_constant_poly(self, a, Parent P):
        """
        Create a new constant polynomial from a in P, which MUST be an
        element of the base ring of P (this is not checked).

        EXAMPLE::

            sage: R.<w> = PolynomialRing(GF(9,'a'), sparse=True)
            sage: a = w._new_constant_poly(0, R); a
            0
            sage: a.coefficients()
            []
        """
        if a:
            return self.__class__(P,[a], check=False) #P._element_constructor(a, check=False)
        return self.__class__(P,[], check=False)

    def is_monic(self):
        """
        Returns True if this polynomial is monic. The zero polynomial is by
        definition not monic.

        EXAMPLES::

            sage: x = QQ['x'].0
            sage: f = x + 33
            sage: f.is_monic()
            True
            sage: f = 0*x
            sage: f.is_monic()
            False
            sage: f = 3*x^3 + x^4 + x^2
            sage: f.is_monic()
            True
            sage: f = 2*x^2 + x^3 + 56*x^5
            sage: f.is_monic()
            False

        AUTHORS:

        - Naqi Jaffery (2006-01-24): examples
        """
        return not self.is_zero() and self[self.degree()] == 1

    def is_unit(self):
        r"""
        Return True if this polynomial is a unit.

        EXAMPLES::

            sage: a = Integers(90384098234^3)
            sage: b = a(2*191*236607587)
            sage: b.is_nilpotent()
            True
            sage: R.<x> = a[]
            sage: f = 3 + b*x + b^2*x^2
            sage: f.is_unit()
            True
            sage: f = 3 + b*x + b^2*x^2 + 17*x^3
            sage: f.is_unit()
            False

        EXERCISE (Atiyah-McDonald, Ch 1): Let `A[x]` be a
        polynomial ring in one variable. Then
        `f=\sum a_i x^i \in A[x]` is a unit if and only if
        `a_0` is a unit and `a_1,\ldots, a_n` are
        nilpotent.

        TESTS:

        Check that :trac:`18600` is fixed::

            sage: R.<x> = PolynomialRing(ZZ, sparse=True)
            sage: c = x^2^100 + 1
            sage: c.is_unit()
            False
        """
        if self.degree() > 0:
            try:
                if self._parent.base_ring().is_integral_domain():
                    return False
            except NotImplementedError:
                pass
            for c in self.coefficients()[1:]:
                if not c.is_nilpotent():
                    return False
        return self[0].is_unit()

    def is_nilpotent(self):
        r"""
        Return True if this polynomial is nilpotent.

        EXAMPLES::

            sage: R = Integers(12)
            sage: S.<x> = R[]
            sage: f = 5 + 6*x
            sage: f.is_nilpotent()
            False
            sage: f = 6 + 6*x^2
            sage: f.is_nilpotent()
            True
            sage: f^2
            0

        EXERCISE (Atiyah-McDonald, Ch 1): Let `A[x]` be a
        polynomial ring in one variable. Then
        `f=\sum a_i x^i \in A[x]` is nilpotent if and only if
        every `a_i` is nilpotent.

        TESTS:

        Check that :trac:`18600` is fixed::

            sage: R.<x> = PolynomialRing(Zmod(4), sparse=True)
            sage: (2*x^2^100 + 2).is_nilpotent()
            True
        """
        for c in self.coefficients():
            if not c.is_nilpotent():
                return False
        return True

    def is_gen(self):
        r"""
        Return True if this polynomial is the distinguished generator of
        the parent polynomial ring.

        EXAMPLES::

            sage: R.<x> = QQ[]
            sage: R(1).is_gen()
            False
            sage: R(x).is_gen()
            True

        Important - this function doesn't return True if self equals the
        generator; it returns True if self *is* the generator.

        ::

            sage: f = R([0,1]); f
            x
            sage: f.is_gen()
            False
            sage: f is x
            False
            sage: f == x
            True
        """
        return bool(self._is_gen)

    def leading_coefficient(self):
        """
        Return the leading coefficient of this polynomial.

        OUTPUT: element of the base ring

        EXAMPLES::

            sage: R.<x> = QQ[]
            sage: f = (-2/5)*x^3 + 2*x - 1/3
            sage: f.leading_coefficient()
            -2/5
        """
        return self[self.degree()]

    def monic(self):
        """
        Return this polynomial divided by its leading coefficient. Does not
        change this polynomial.

        EXAMPLES::

            sage: x = QQ['x'].0
            sage: f = 2*x^2 + x^3 + 56*x^5
            sage: f.monic()
            x^5 + 1/56*x^3 + 1/28*x^2
            sage: f = (1/4)*x^2 + 3*x + 1
            sage: f.monic()
            x^2 + 12*x + 4

        The following happens because `f = 0` cannot be made into a
        monic polynomial

        ::

            sage: f = 0*x
            sage: f.monic()
            Traceback (most recent call last):
            ...
            ZeroDivisionError: rational division by zero

        Notice that the monic version of a polynomial over the integers is
        defined over the rationals.

        ::

            sage: x = ZZ['x'].0
            sage: f = 3*x^19 + x^2 - 37
            sage: g = f.monic(); g
            x^19 + 1/3*x^2 - 37/3
            sage: g.parent()
            Univariate Polynomial Ring in x over Rational Field

        AUTHORS:

        - Naqi Jaffery (2006-01-24): examples
        """
        if self.is_monic():
            return self
        a = ~self.leading_coefficient()
        R = self.parent()
        if a.parent() != R.base_ring():
            S = R.base_extend(a.parent())
            return a*S(self)
        else:
            return a*self

    def coefficients(self, sparse=True):
        """
        Return the coefficients of the monomials appearing in self.
        If ``sparse=True`` (the default), it returns only the non-zero coefficients.
        Otherwise, it returns the same value as ``self.list()``.
        (In this case, it may be slightly faster to invoke ``self.list()`` directly.)

        EXAMPLES::

            sage: _.<x> = PolynomialRing(ZZ)
            sage: f = x^4+2*x^2+1
            sage: f.coefficients()
            [1, 2, 1]
            sage: f.coefficients(sparse=False)
            [1, 0, 2, 0, 1]
        """
        zero = self.parent().base_ring().zero()
        if (sparse):
          return [c for c in self.list() if c != zero]
        else:
          return self.list()

    def exponents(self):
        """
        Return the exponents of the monomials appearing in self.

        EXAMPLES::

            sage: _.<x> = PolynomialRing(ZZ)
            sage: f = x^4+2*x^2+1
            sage: f.exponents()
            [0, 2, 4]
        """
        zero = self.parent().base_ring().zero()
        l = self.list()
        return [i for i in range(len(l)) if l[i] != zero]

    def list(self):
        """
        Return a new copy of the list of the underlying elements of self.

        EXAMPLES::

            sage: R.<x> = QQ[]
            sage: f = (-2/5)*x^3 + 2*x - 1/3
            sage: v = f.list(); v
            [-1/3, 2, 0, -2/5]

        Note that v is a list, it is mutable, and each call to the list
        method returns a new list::

            sage: type(v)
            <type 'list'>
            sage: v[0] = 5
            sage: f.list()
            [-1/3, 2, 0, -2/5]

        Here is an example with a generic polynomial ring::

            sage: R.<x> = QQ[]
            sage: S.<y> = R[]
            sage: f = y^3 + x*y -3*x; f
            y^3 + x*y - 3*x
            sage: type(f)
            <type 'sage.rings.polynomial.polynomial_element.Polynomial_generic_dense'>
            sage: v = f.list(); v
            [-3*x, x, 0, 1]
            sage: v[0] = 10
            sage: f.list()
            [-3*x, x, 0, 1]
        """
        raise NotImplementedError

    def prec(self):
        """
        Return the precision of this polynomial. This is always infinity,
        since polynomials are of infinite precision by definition (there is
        no big-oh).

        EXAMPLES::

            sage: x = polygen(ZZ)
            sage: (x^5 + x + 1).prec()
            +Infinity
            sage: x.prec()
            +Infinity
        """
        return infinity.infinity

    def padded_list(self, n=None):
        """
        Return list of coefficients of self up to (but not including)
        `q^n`.

        Includes 0's in the list on the right so that the list has length
        `n`.

        INPUT:


        -  ``n`` - (default: None); if given, an integer that
           is at least 0


        EXAMPLES::

            sage: x = polygen(QQ)
            sage: f = 1 + x^3 + 23*x^5
            sage: f.padded_list()
            [1, 0, 0, 1, 0, 23]
            sage: f.padded_list(10)
            [1, 0, 0, 1, 0, 23, 0, 0, 0, 0]
            sage: len(f.padded_list(10))
            10
            sage: f.padded_list(3)
            [1, 0, 0]
            sage: f.padded_list(0)
            []
            sage: f.padded_list(-1)
            Traceback (most recent call last):
            ...
            ValueError: n must be at least 0

        TESTS:

        Check that :trac:`18600` is fixed::

            sage: R.<x> = PolynomialRing(ZZ, sparse=True)
            sage: (x^2^100 + x^8 - 1).padded_list(10)
            [-1, 0, 0, 0, 0, 0, 0, 0, 1, 0]
        """
        if n is None:
            return self.list()
        if n < 0:
            raise ValueError("n must be at least 0")
        if self.degree() < n:
            v = self.list()
            z = self._parent.base_ring().zero()
            return v + [z]*(n - len(v))
        else:
            return self[:int(n)].padded_list(n)

    def coeffs(self):
        r"""
        Using ``coeffs()`` is now deprecated (:trac:`17518`).
        Returns ``self.list()``.

        (It is potentially slightly faster to use
        ``self.list()`` directly.)

        EXAMPLES::

            sage: x = QQ['x'].0
            sage: f = 10*x^3 + 5*x + 2/17
            sage: f.coeffs()
            doctest:...: DeprecationWarning: The use of coeffs() is now deprecated in favor of coefficients(sparse=False).
            See http://trac.sagemath.org/17518 for details.
            [2/17, 5, 0, 10]
        """
        deprecation(17518, 'The use of coeffs() is now deprecated in favor of coefficients(sparse=False).')
        return self.list()

    def newton_raphson(self, n, x0):
        """
        Return a list of n iterative approximations to a root of this
        polynomial, computed using the Newton-Raphson method.

        The Newton-Raphson method is an iterative root-finding algorithm.
        For f(x) a polynomial, as is the case here, this is essentially the
        same as Horner's method.

        INPUT:


        -  ``n`` - an integer (=the number of iterations),

        -  ``x0`` - an initial guess x0.


        OUTPUT: A list of numbers hopefully approximating a root of
        f(x)=0.

        If one of the iterates is a critical point of f then a
        ZeroDivisionError exception is raised.

        EXAMPLES::

            sage: x = PolynomialRing(RealField(), 'x').gen()
            sage: f = x^2 - 2
            sage: f.newton_raphson(4, 1)
            [1.50000000000000, 1.41666666666667, 1.41421568627451, 1.41421356237469]

        AUTHORS:

        - David Joyner and William Stein (2005-11-28)
        """
        n = sage.rings.integer.Integer(n)
        df = self.derivative()
        K = self.parent().base_ring()
        a = K(x0)
        L = []
        for i in range(n):
            a -= self(a) / df(a)
            L.append(a)
        return L

    def polynomial(self, var):
        r"""
        Let var be one of the variables of the parent of self. This returns
        self viewed as a univariate polynomial in var over the polynomial
        ring generated by all the other variables of the parent.

        For univariate polynomials, if var is the generator of the parent
        ring, we return this polynomial, otherwise raise an error.

        EXAMPLES::

            sage: R.<x> = QQ[]
            sage: (x+1).polynomial(x)
            x + 1

        TESTS::

            sage: x.polynomial(1)
            Traceback (most recent call last):
            ...
            ValueError: given variable is not the generator of parent.
        """
        if self._parent.ngens() == 1:
            if self._parent.gen() == var:
                return self
            raise ValueError("given variable is not the generator of parent.")
        raise NotImplementedError

    def newton_slopes(self, p, lengths=False):
        """
        Return the `p`-adic slopes of the Newton polygon of self,
        when this makes sense.

        OUTPUT:

        If `lengths` is `False`, a list of rational numbers. If `lengths` is
        `True`, a list of couples `(s,l)` where `s` is the slope and `l` the
        length of the corresponding segment in the Newton polygon.

        EXAMPLES::

            sage: x = QQ['x'].0
            sage: f = x^3 + 2
            sage: f.newton_slopes(2)
            [1/3, 1/3, 1/3]
            sage: R.<x> = PolynomialRing(ZZ, sparse=True)
            sage: p = x^5 + 6*x^2 + 4
            sage: p.newton_slopes(2)
            [1/2, 1/2, 1/3, 1/3, 1/3]
            sage: p.newton_slopes(2, lengths=True)
            [(1/2, 2), (1/3, 3)]
            sage: (x^2^100 + 27).newton_slopes(3, lengths=True)
            [(3/1267650600228229401496703205376, 1267650600228229401496703205376)]

        ALGORITHM: Uses PARI if `lengths` is `False`.
        """
        if not lengths:
            f = self._pari_()
            v = list(f.newtonpoly(p))
            return [sage.rings.rational.Rational(x) for x in v]

        e = self.exponents()
        c = self.coefficients()
        if len(e) == 0: return []
        if len(e) == 1:
            if e[0] == 0: return []
            else:         return [(infinity.infinity, e[0])]

        if e[0] == 0: slopes = []
        else:         slopes = [(infinity.infinity, e[0])]

        points = [(e[0], c[0].valuation(p)), (e[1], c[1].valuation(p))]
        slopes.append((-(c[1].valuation(p)-c[0].valuation(p))/(e[1] - e[0]), e[1]-e[0]))
        for i in range(2, len(e)):
            v = c[i].valuation(p)
            s = -(v-points[-1][1])/(e[i]-points[-1][0])
            while len(slopes) > 0 and s >= slopes[-1][0]:
                slopes = slopes[:-1]
                points = points[:-1]
                s = -(v-points[-1][1])/(e[i]-points[-1][0])
            slopes.append((s,e[i]-points[-1][0]))
            points.append((e[i],v))

        return slopes

    def dispersion_set(self, other=None):
        r"""
        Compute the dispersion set of two polynomials.

        The dispersion set of `f` and `g` is the set of nonnegative integers
        `n` such that `f(x + n)` and `g(x)` have a nonconstant common factor.

        When ``other`` is ``None``, compute the auto-dispersion set of
        ``self``, i.e., its dispersion set with itself.

        ALGORITHM:

        See Section 4 of Man & Wright [ManWright1994]_.

        .. [ManWright1994] Yiu-Kwong Man and Francis J. Wright.
           *Fast Polynomial Dispersion Computation and its Application to
           Indefinite Summation*. ISSAC 1994.

        .. SEEALSO:: :meth:`dispersion`

        EXAMPLES::

            sage: Pol.<x> = QQ[]
            sage: x.dispersion_set(x + 1)
            [1]
            sage: (x + 1).dispersion_set(x)
            []

            sage: pol = x^3 + x - 7
            sage: (pol*pol(x+3)^2).dispersion_set()
            [0, 3]
        """
        other = self if other is None else self._parent.coerce(other)
        x = self._parent.gen()
        dispersions = set()
        for p, _ in self.factor():
            # need both due to the semantics of is_primitive() over fields
            assert p.is_monic() or p.is_primitive()
            for q, _ in other.factor():
                m, n = p.degree(), q.degree()
                assert q.is_monic() or q.is_primitive()
                if m != n or p[n] != q[n]:
                    continue
                alpha = (q[n-1] - p[n-1])/(n*p[n])
                if alpha.is_integer(): # ZZ() might work for non-integers...
                    alpha = ZZ(alpha)
                else:
                    continue
                if alpha < 0 or alpha in dispersions:
                    continue
                if n >= 1 and p(x + alpha) != q:
                    continue
                dispersions.add(alpha)
        return list(dispersions)

    def dispersion(self, other=None):
        r"""
        Compute the dispersion of a pair of polynomials.

        The dispersion of `f` and `g` is the largest nonnegative integer `n`
        such that `f(x + n)` and `g(x)` have a nonconstant common factor.

        When ``other`` is ``None``, compute the auto-dispersion of ``self``,
        i.e., its dispersion with itself.

        .. SEEALSO:: :meth:`dispersion_set`

        EXAMPLES::

            sage: Pol.<x> = QQ[]
            sage: x.dispersion(x + 1)
            1
            sage: (x + 1).dispersion(x)
            -Infinity

            sage: Pol.<x> = QQbar[]
            sage: pol = Pol([sqrt(5), 1, 3/2])
            sage: pol.dispersion()
            0
            sage: (pol*pol(x+3)).dispersion()
            3
        """
        dispersions = self.dispersion_set(other)
        return max(dispersions) if len(dispersions) > 0 else infinity.minus_infinity

    #####################################################################
    # Conversions to other systems
    #####################################################################
    def _pari_(self):
        r"""
        Return polynomial as a PARI object.

        Sage does not handle PARI's variable ordering requirements
        gracefully at this time. In practice, this means that the variable
        ``x`` needs to be the topmost variable, as in the
        example.

        EXAMPLES::

            sage: f = QQ['x']([0,1,2/3,3])
            sage: pari(f)
            3*x^3 + 2/3*x^2 + x

        ::

            sage: S.<a> = QQ['a']
            sage: R.<x> = S['x']
            sage: f = R([0, a]) + R([0, 0, 2/3])
            sage: pari(f)
            2/3*x^2 + a*x

        Polynomials over a number field work, provided that the variable is
        called 'x'::

            sage: x = polygen(QQ)
            sage: K.<b> = NumberField(x^2 + x + 1)
            sage: R.<x> = PolynomialRing(K)
            sage: pol = (b + x)^3; pol
            x^3 + 3*b*x^2 + (-3*b - 3)*x + 1
            sage: pari(pol)
            Mod(1, y^2 + y + 1)*x^3 + Mod(3*y, y^2 + y + 1)*x^2 + Mod(-3*y - 3, y^2 + y + 1)*x + Mod(1, y^2 + y + 1)

        TESTS:

        Unfortunately, variable names matter::

            sage: R.<x, y> = QQ[]
            sage: S.<a> = R[]
            sage: f = x^2 + a; g = y^3 + a
            sage: pari(f)
            Traceback (most recent call last):
            ...
            PariError: incorrect priority in gtopoly: variable x <= a

        Stacked polynomial rings, first with a univariate ring on the
        bottom::

            sage: S.<a> = QQ['a']
            sage: R.<x> = S['x']
            sage: pari(x^2 + 2*x)
            x^2 + 2*x
            sage: pari(a*x + 2*x^3)
            2*x^3 + a*x

        Stacked polynomial rings, second with a multivariate ring on the
        bottom::

            sage: S.<a, b> = ZZ['a', 'b']
            sage: R.<x> = S['x']
            sage: pari(x^2 + 2*x)
            x^2 + 2*x
            sage: pari(a*x + 2*b*x^3)
            2*b*x^3 + a*x

        Stacked polynomial rings with exotic base rings::

            sage: S.<a, b> = GF(7)['a', 'b']
            sage: R.<x> = S['x']
            sage: pari(x^2 + 9*x)
            x^2 + 2*x
            sage: pari(a*x + 9*b*x^3)
            2*b*x^3 + a*x

        ::

            sage: S.<a> = Integers(8)['a']
            sage: R.<x> = S['x']
            sage: pari(x^2 + 2*x)
            Mod(1, 8)*x^2 + Mod(2, 8)*x
            sage: pari(a*x + 10*x^3)
            Mod(2, 8)*x^3 + Mod(1, 8)*a*x
        """
        return self._pari_with_name(self.parent().variable_name())

    def _pari_or_constant(self, name=None):
        r"""
        Convert ``self`` to PARI.  This behaves identical to :meth:`_pari_`
        or :meth:`_pari_with_name` except for constant polynomials:
        then the constant is returned instead of a constant polynomial.

        INPUT:

        - ``name`` -- (default: None) Variable name.  If not given, use
          ``self.parent().variable_name()``.  This argument is irrelevant
          for constant polynomials.

        EXAMPLES::

            sage: R.<x> = PolynomialRing(ZZ)
            sage: pol = 2*x^2 + 7*x - 5
            sage: pol._pari_or_constant()
            2*x^2 + 7*x - 5
            sage: pol._pari_or_constant('a')
            2*a^2 + 7*a - 5
            sage: pol = R(7)
            sage: pol._pari_or_constant()
            7
            sage: pol._pari_or_constant().type()
            't_INT'
            sage: pol._pari_().type()
            't_POL'
            sage: PolynomialRing(IntegerModRing(101), 't')()._pari_or_constant()
            Mod(0, 101)
        """
        if self.is_constant():
            return self[0]._pari_()
        if name is None:
            name = self.parent().variable_name()
        return self._pari_with_name(name)

    def _pari_with_name(self, name='x'):
        r"""
        Return polynomial as a PARI object with topmost variable
        ``name``.  By default, use 'x' for the variable name.

        For internal use only.

        EXAMPLES:

            sage: R.<a> = PolynomialRing(ZZ)
            sage: (2*a^2 + a)._pari_with_name()
            2*x^2 + x
            sage: (2*a^2 + a)._pari_with_name('y')
            2*y^2 + y
        """
        vals = [x._pari_() for x in self.list()]
        return pari(vals).Polrev(name)

    def _pari_init_(self):
        return repr(self._pari_())

    def _magma_init_(self, magma):
        """
        Return a string that evaluates in Magma to this polynomial.

        EXAMPLES::

            sage: magma = Magma()  # new session
            sage: R.<y> = ZZ[]
            sage: f = y^3 - 17*y + 5
            sage: f._magma_init_(magma)        # optional - magma
            '_sage_[...]![5,-17,0,1]'
            sage: g = magma(f); g              # optional - magma
            y^3 - 17*y + 5

        Note that in Magma there is only one polynomial ring over each
        base, so if we make the polynomial ring over ZZ with variable
        `z`, then this changes the variable name of the polynomial
        we already defined::

            sage: R.<z> = ZZ[]
            sage: magma(R)                     # optional - magma
            Univariate Polynomial Ring in z over Integer Ring
            sage: g                            # optional - magma
            z^3 - 17*z + 5

        In Sage the variable name does not change::

            sage: f
            y^3 - 17*y + 5

        A more complicated nested example::

            sage: k.<a> = GF(9); R.<s,t> = k[]; S.<W> = R[]
            sage: magma(a*W^20 + s*t/a)        # optional - magma
            a*W^20 + a^7*s*t
        """
        # Get a reference to Magma version of parent.
        R = magma(self.parent())
        # Get list of coefficients.
        v = ','.join([a._magma_init_(magma) for a in self.list()])
        return '%s![%s]'%(R.name(), v)

    def _gap_(self, gap):
        """
        Return this polynomial in GAP.

        INPUT:

        - ``gap`` -- a GAP or libgap instance

        EXAMPLES::

            sage: R.<y> = ZZ[]
            sage: f = y^3 - 17*y + 5
            sage: g = gap(f); g   # indirect doctest
            y^3-17*y+5
            sage: f._gap_init_()
            'y^3 - 17*y + 5'
            sage: R.<z> = ZZ[]
            sage: gap(R)
            PolynomialRing( Integers, ["z"] )
            sage: g
            y^3-17*y+5
            sage: gap(z^2 + z)
            z^2+z
            sage: libgap(z^2 + z)
            z^2+z

        Coefficients in a finite field::

            sage: R.<y> = GF(7)[]
            sage: f = y^3 - 17*y + 5
            sage: g = gap(f); g
            y^3+Z(7)^4*y+Z(7)^5
            sage: h = libgap(f); h
            y^3+Z(7)^4*y+Z(7)^5
            sage: g.Factors()
            [ y+Z(7)^0, y+Z(7)^0, y+Z(7)^5 ]
            sage: h.Factors()
            [ y+Z(7)^0, y+Z(7)^0, y+Z(7)^5 ]
            sage: f.factor()
            (y + 5) * (y + 1)^2
        """
        R = gap(self.parent())
        var = list(R.IndeterminatesOfPolynomialRing())[0]
        return self(var)

    def _libgap_(self):
        r"""
        TESTS::

            sage: R.<x> = ZZ[]
            sage: libgap(-x^3 + 3*x)   # indirect doctest
            -x^3+3*x
            sage: libgap(R.zero())     # indirect doctest
            0
        """
        from sage.libs.gap.libgap import libgap
        return self._gap_(libgap)

    ######################################################################

    @coerce_binop
    def resultant(self, other):
        r"""
        Return the resultant of ``self`` and ``other``.

        INPUT:

        - ``other`` -- a polynomial

        OUTPUT: an element of the base ring of the polynomial ring

        ALGORITHM:

        Uses PARI's ``polresultant`` function.  For base rings that
        are not supported by PARI, the resultant is computed as the
        determinant of the Sylvester matrix.

        EXAMPLES::

            sage: R.<x> = QQ[]
            sage: f = x^3 + x + 1;  g = x^3 - x - 1
            sage: r = f.resultant(g); r
            -8
            sage: r.parent() is QQ
            True

        We can compute resultants over univariate and multivariate
        polynomial rings::

            sage: R.<a> = QQ[]
            sage: S.<x> = R[]
            sage: f = x^2 + a; g = x^3 + a
            sage: r = f.resultant(g); r
            a^3 + a^2
            sage: r.parent() is R
            True

        ::

            sage: R.<a, b> = QQ[]
            sage: S.<x> = R[]
            sage: f = x^2 + a; g = x^3 + b
            sage: r = f.resultant(g); r
            a^3 + b^2
            sage: r.parent() is R
            True

        TESTS::

            sage: R.<x, y> = QQ[]
            sage: S.<a> = R[]
            sage: f = x^2 + a; g = y^3 + a
            sage: h = f.resultant(g); h
            y^3 - x^2
            sage: h.parent() is R
            True

        Check that :trac:`13672` is fixed::

            sage: R.<t> = GF(2)[]
            sage: S.<x> = R[]
            sage: f = (t^2 + t)*x + t^2 + t
            sage: g = (t + 1)*x + t^2
            sage: f.resultant(g)
            t^4 + t

        Check that :trac:`15061` is fixed::

            sage: R.<T> = PowerSeriesRing(QQ)
            sage: F = R([1,1],2)
            sage: RP.<x> = PolynomialRing(R)
            sage: P = x^2 - F
            sage: P.resultant(P.derivative())
            -4 - 4*T + O(T^2)

        Check that :trac:`16360` is fixed::

            sage: K.<x> = FunctionField(QQ)
            sage: R.<y> = K[]
            sage: y.resultant(y+x)
            x

            sage: K.<a> = FunctionField(QQ)
            sage: R.<b> = K[]
            sage: L.<b> = K.extension(b^2-a)
            sage: R.<x> = L[]
            sage: f=x^2-a
            sage: g=x-b
            sage: f.resultant(g)
            0

        Check that :trac:`17817` is fixed::

            sage: A.<a,b,c> = Frac(PolynomialRing(QQ,'a,b,c'))
            sage: B.<d,e,f> = PolynomialRing(A,'d,e,f')
            sage: R.<x>= PolynomialRing(B,'x')
            sage: S.<y> = PolynomialRing(R,'y')
            sage: p = ((1/b^2*d^2+1/a)*x*y^2+a*b/c*y+e+x^2)
            sage: q = -4*c^2*y^3+1
            sage: p.resultant(q)
            16*c^4*x^6 + 48*c^4*e*x^4 + (1/b^6*d^6 + 3/(a*b^4)*d^4 + ((-12*a^3*b*c + 3)/(a^2*b^2))*d^2 + (-12*a^3*b*c + 1)/a^3)*x^3 + 48*c^4*e^2*x^2 + (((-12*a*c)/b)*d^2*e + (-12*b*c)*e)*x + 16*c^4*e^3 + 4*a^3*b^3/c

        """
        variable = self.variable_name()
        try:
            res = self._pari_().polresultant(other._pari_(), variable)
            return self.parent().base_ring()(res)
        except (TypeError, ValueError, PariError, NotImplementedError):
            return self.sylvester_matrix(other).det()

    def composed_op(p1, p2, op, algorithm=None, monic=False):
        r"""
        Return the composed sum, difference, product or quotient of this
        polynomial with another one.

        In the case of two monic polynomials `p_1` and `p_2` over an integral
        domain, the composed sum, difference, etc. are given by

        .. MATH::

            \prod_{p_1(a)=p_2(b)=0}(x - (a \ast b)), \qquad
            \ast ∈ \{ +, -, ×, / \}

        where the roots `a` and `b` are to be considered in the algebraic
        closure of the fraction field of the coefficients and counted with
        multiplicities. If the polynomials are not monic this quantity is
        multiplied by `\\alpha_1^{deg(p_2)} \\alpha_2^{deg(p_1)}` where
        `\\alpha_1` and `\\alpha_2` are the leading coefficients of `p_1` and
        `p_2` respectively.

        INPUT:

        - ``p2`` -- univariate polynomial belonging to the same polynomial ring
          as this polynomial

        - ``op`` -- ``operator.OP`` where ``OP=add`` or ``sub`` or ``mul`` or
          ``div``.

        - ``algorithm`` -- can be "resultant" or "BFSS";
          by default the former is used when the polynomials have few nonzero
          coefficients and small degrees or if the base ring is not `\ZZ` or
          `\QQ`. Otherwise the latter is used.

        - ``monic`` -- whether to return a monic polynomial. If ``True`` the
          coefficients of the result belong to the fraction field of the
          coefficients.

        ALGORITHM:

        The computation is straightforward using resultants. Indeed for the
        composed sum it would be `Res_y(p1(x-y), p2(y))`. However, the method
        from [BFSS]_ using series expansions is asymptotically much faster.

        Note that the algorithm ``BFSS`` with polynomials with coefficients in
        `\ZZ` needs to perform operations over `\QQ`.

        .. TODO::

           - The [BFSS]_ algorithm has been implemented here only in the case of
             polynomials over rationals. For other rings of zero characteristic
             (or if the characteristic is larger than the product of the degrees),
             one needs to implement a generic method ``_exp_series``. In the
             general case of non-zero characteristic there is an alternative
             algorithm in the same paper.

           - The Newton series computation can be done much more efficiently!
             See [BFSS]_.

        EXAMPLES::

            sage: x = polygen(ZZ)
            sage: p1 = x^2 - 1
            sage: p2 = x^4 - 1
            sage: p1.composed_op(p2, operator.add)
            x^8 - 4*x^6 + 4*x^4 - 16*x^2
            sage: p1.composed_op(p2, operator.mul)
            x^8 - 2*x^4 + 1
            sage: p1.composed_op(p2, operator.div)
            x^8 - 2*x^4 + 1

        This function works over any field. However for base rings other than
        `\ZZ` and `\QQ` only the resultant algorithm is available::

            sage: x = polygen(QQbar)
            sage: p1 = x**2 - AA(2).sqrt()
            sage: p2 = x**3 - AA(3).sqrt()
            sage: r1 = p1.roots(multiplicities=False)
            sage: r2 = p2.roots(multiplicities=False)
            sage: p = p1.composed_op(p2, operator.add)
            sage: p
            1.000000000000000?*x^6 - 4.242640687119285?*x^4 -
            3.464101615137755?*x^3 + 6.000000000000000?*x^2 -
            14.69693845669907?*x + 0.1715728752538099?
            sage: all(p(x+y).is_zero() for x in r1 for y in r2)
            True

            sage: x = polygen(GF(2))
            sage: p1 = x**2 + x - 1
            sage: p2 = x**3 + x - 1
            sage: p_add = p1.composed_op(p2, operator.add)
            sage: p_add
            x^6 + x^5 + x^3 + x^2 + 1
            sage: p_mul = p1.composed_op(p2, operator.mul)
            sage: p_mul
            x^6 + x^4 + x^2 + x + 1
            sage: p_div = p1.composed_op(p2, operator.div)
            sage: p_div
            x^6 + x^5 + x^4 + x^2 + 1

            sage: K = GF(2**6, 'a')
            sage: r1 = p1.roots(K, multiplicities=False)
            sage: r2 = p2.roots(K, multiplicities=False)
            sage: all(p_add(x1+x2).is_zero() for x1 in r1 for x2 in r2)
            True
            sage: all(p_mul(x1*x2).is_zero() for x1 in r1 for x2 in r2)
            True
            sage: all(p_div(x1/x2).is_zero() for x1 in r1 for x2 in r2)
            True

        TESTS::

            sage: y = polygen(ZZ)
            sage: for p1 in [2*y^3 - y + 3, -y^5 - 2, 4*y - 3]:
            ....:   for p2 in [5*y^2 - 7, -3*y - 1]:
            ....:     for monic in [True,False]:
            ....:       for op in [operator.add, operator.sub, operator.mul, operator.div]:
            ....:         pr = p1.composed_op(p2, operator.add, "resultant", monic=monic)
            ....:         pb = p1.composed_op(p2, operator.add, "BFSS", monic=monic)
            ....:         assert pr == pb and parent(pr) is parent(pb)

        REFERENCES:

        .. [BFSS] A. Bostan, P. Flajolet, B. Salvy and E. Schost,
           "Fast Computation of special resultants",
           Journal of Symbolic Computation 41 (2006), 1-29
        """
        cdef long j
        cdef long prec

        if op not in (operator.add, operator.sub, operator.mul, operator.div):
            raise ValueError("op must be operator.OP where OP=add, sub, mul or div")

        if not isinstance(p2, Polynomial):
            raise TypeError("p2 must be a polynomial")
        p1, p2 = coercion_model.canonical_coercion(p1, p2)
        K = p1.parent()
        assert is_PolynomialRing(p1.parent())
        S = K.base_ring()
        Sf = S.fraction_field()

        cdef long d1 = p1.degree()
        cdef long d2 = p2.degree()
        if d1 <= 0 or d2 <= 0:
            raise ValueError('the polynomials must have positive degree')

        if op is operator.div and p2.valuation() > 0:
            raise ZeroDivisionError('p2 must have zero valuation')
        if algorithm is None:
            # choose the algorithm observing that the "resultant" one
            # is fast when there are few terms and the degrees are not high
            N = 7
            if Sf is not QQ or (d1 <= N and d2 <= N):
                algorithm = "resultant"
            else:
                c = d1*sum(bool(p1[i]) for i in range(d1 + 1))*\
                    d2*sum(bool(p2[i]) for i in range(d2 + 1))
                if c <= N**4:
                    algorithm = "resultant"
                else:
                    algorithm = "BFSS"

        if algorithm == "resultant":
            R = K['x', 'y']
            x = R.gen(0)
            y = R.gen(1)
            if op is operator.add:
                lp = p1(x - y)
            elif op is operator.sub:
                lp = p1(x + y)
            elif op is operator.mul:
                lp = p1(x).homogenize(y)
            else:
                lp = p1(x * y)
            q = p2(y).resultant(lp, y).univariate_polynomial(K)
            return q.monic() if monic else q

        elif algorithm == "BFSS":
            if Sf is not QQ:
                raise ValueError("BFSS algorithm is available only for the base ring ZZ or QQ")
            if op is operator.sub:
                p2 = p2(-K.gen())
            elif op is operator.div:
                p2 = p2.reverse()
            # the computation below needs must be done in the fraction field
            # even though the result would have the same ring
            if Sf is not S:
                K = K.change_ring(Sf)
                p1 = p1.change_ring(Sf)
                p2 = p2.change_ring(Sf)
            prec = d1*d2 + 1
            np1 = p1.reverse().inverse_series_trunc(prec)
            np1 = np1._mul_trunc_(p1.derivative().reverse(), prec)
            np2 = p2.reverse().inverse_series_trunc(prec)
            np2 = np2._mul_trunc_(p2.derivative().reverse(), prec)
            if op in (operator.add, operator.sub):
                # compute np1e and np2e, the Hadamard products of respectively
                # np1 and np2 with the exponential series. That is
                #  a0 + a1 x + a2 x^2 + ...
                #  ->
                #  a0 + a1/1! x + a2/2! x^2 + ...
                fj = Sf.one()
                a1, a2 = [np1[0]], [np2[0]]
                for j in range(1, prec):
                    fj = fj*j
                    a1.append(np1[j] / fj)
                    a2.append(np2[j] / fj)
                np1e = K(a1)
                np2e = K(a2)

                # recover the polynomial from its Newton series
                np3e = np1e*np2e
                fj = -Sf.one()
                a3 = [Sf.zero()]
                for j in range(1, prec):
                    a3.append(np3e[j] * fj)
                    fj = fj*j
                np = K(a3)
                q = np
            else:
                np = K([-np1[j]*np2[j] for j in range(1, prec)])
                q = np.integral()

            q = q._exp_series(prec).reverse()
            q = q.shift(prec - q.degree() - 1)
            if monic:
                return q
            else:
                return (p1.leading_coefficient()**p2.degree() *
                        p2.leading_coefficient()**p1.degree() * q).change_ring(S)

        else:
            raise ValueError('algorithm must be "resultant" or "BFSS"')

    def discriminant(self):
        r"""
        Returns the discriminant of self.

        The discriminant is

        .. math::

            R_n := a_n^{2 n-2} \prod_{1<i<j<n} (r_i-r_j)^2,

        where `n` is the degree of self, `a_n` is the
        leading coefficient of self and the roots of self are
        `r_1, \ldots, r_n`.

        OUTPUT: An element of the base ring of the polynomial ring.

        ALGORITHM:

        Uses the identity `R_n(f) := (-1)^{n (n-1)/2} R(f, f')
        a_n^{n-k-2}`, where `n` is the degree of self, `a_n` is the
        leading coefficient of self, `f'` is the derivative of `f`,
        and `k` is the degree of `f'`. Calls :meth:`.resultant`.

        EXAMPLES:

        In the case of elliptic curves in special form, the discriminant is
        easy to calculate::

            sage: R.<x> = QQ[]
            sage: f = x^3 + x + 1
            sage: d = f.discriminant(); d
            -31
            sage: d.parent() is QQ
            True
            sage: EllipticCurve([1, 1]).discriminant()/16
            -31

        ::

            sage: R.<x> = QQ[]
            sage: f = 2*x^3 + x + 1
            sage: d = f.discriminant(); d
            -116

        We can compute discriminants over univariate and multivariate
        polynomial rings::

            sage: R.<a> = QQ[]
            sage: S.<x> = R[]
            sage: f = a*x + x + a + 1
            sage: d = f.discriminant(); d
            1
            sage: d.parent() is R
            True

        ::

            sage: R.<a, b> = QQ[]
            sage: S.<x> = R[]
            sage: f = x^2 + a + b
            sage: d = f.discriminant(); d
            -4*a - 4*b
            sage: d.parent() is R
            True

        TESTS::

            sage: R.<x, y> = QQ[]
            sage: S.<a> = R[]
            sage: f = x^2 + a
            sage: f.discriminant()
            1

        Check that :trac:`13672` is fixed::

            sage: R.<t> = GF(5)[]
            sage: S.<x> = R[]
            sage: f = x^10 + 2*x^6 + 2*x^5 + x + 2
            sage: (f-t).discriminant()
            4*t^5

        The following examples show that :trac:`11782` has been fixed::

            sage: ZZ.quo(81)[x](3*x^2 + 3*x + 3).discriminant()
            54
            sage: ZZ.quo(9)[x](2*x^3 + x^2 + x).discriminant()
            2

        This was fixed by :trac:`15422`::

            sage: R.<s> = PolynomialRing(Qp(2))
            sage: (s^2).discriminant()
            0

        This was fixed by :trac:`16014`::

            sage: PR.<b,t1,t2,x1,y1,x2,y2> = QQ[]
            sage: PRmu.<mu> = PR[]
            sage: E1 = diagonal_matrix(PR, [1, b^2, -b^2])
            sage: M = matrix(PR, [[1,-t1,x1-t1*y1],[t1,1,y1+t1*x1],[0,0,1]])
            sage: E1 = M.transpose()*E1*M
            sage: E2 = E1.subs(t1=t2, x1=x2, y1=y2)
            sage: det(mu*E1 + E2).discriminant().degrees()
            (24, 12, 12, 8, 8, 8, 8)

        This addresses an issue raised by :trac:`15061`::

            sage: R.<T> = PowerSeriesRing(QQ)
            sage: F = R([1,1],2)
            sage: RP.<x> = PolynomialRing(R)
            sage: P = x^2 - F
            sage: P.discriminant()
            4 + 4*T + O(T^2)
        """
        # Late import to avoid cyclic dependencies:
        from sage.rings.power_series_ring import is_PowerSeriesRing
        if self.is_zero():
            return self.parent().zero()
        n = self.degree()
        base_ring = self.parent().base_ring()
        if (is_MPolynomialRing(base_ring) or
            is_PowerSeriesRing(base_ring)):
            # It is often cheaper to compute discriminant of simple
            # multivariate polynomial and substitute the real
            # coefficients into that result (see #16014).
            return universal_discriminant(n)(list(self))
        d = self.derivative()
        k = d.degree()

        r = n % 4
        u = -1 # (-1)**(n*(n-1)/2)
        if r == 0 or r == 1:
            u = 1
        try:
            an = self[n]**(n - k - 2)
        except ZeroDivisionError:
            assert(n-k-2 == -1)
            # Rather than dividing the resultant by the leading coefficient,
            # we alter the Sylvester matrix (see #11782).
            mat = self.sylvester_matrix(d)
            mat[0, 0] = self.base_ring()(1)
            mat[n - 1, 0] = self.base_ring()(n)
            return u * mat.determinant()
        else:
            return self.base_ring()(u * self.resultant(d) * an)

    def reverse(self, degree=None):
        """
        Return polynomial but with the coefficients reversed.

        If an optional degree argument is given the coefficient list will be
        truncated or zero padded as necessary before reversing it. Assuming
        that the constant coefficient of ``self`` is nonzero, the reverse
        polynomial will have the specified degree.

        EXAMPLES::

            sage: R.<x> = ZZ[]; S.<y> = R[]
            sage: f = y^3 + x*y -3*x; f
            y^3 + x*y - 3*x
            sage: f.reverse()
            -3*x*y^3 + x*y^2 + 1
            sage: f.reverse(degree=2)
            -3*x*y^2 + x*y
            sage: f.reverse(degree=5)
            -3*x*y^5 + x*y^4 + y^2

        TESTS::

            sage: f.reverse(degree=1.5r)
            Traceback (most recent call last):
            ...
            ValueError: degree argument must be a non-negative integer, got 1.5

            sage: f.reverse(0)
            -3*x
            sage: f
            y^3 + x*y - 3*x
        """
        v = self.list()

        cdef unsigned long d
        if degree is not None:
            d = degree
            if d != degree:
                raise ValueError("degree argument must be a non-negative integer, got %s"%(degree))
            if len(v) < degree+1:
                v.reverse()
                v = [0]*(degree+1-len(v)) + v
            elif len(v) > degree+1:
                v = v[:degree+1]
                v.reverse()
            else: # len(v) == degree + 1
                v.reverse()
        else:
            v.reverse()

        return self.parent()(v)

    def roots(self, ring=None, multiplicities=True, algorithm=None, **kwds):
        """
        Return the roots of this polynomial (by default, in the base ring
        of this polynomial).

        INPUT:


        -  ``ring`` - the ring to find roots in

        -  ``multiplicities`` - bool (default: True) if True
           return list of pairs (r, n), where r is the root and n is the
           multiplicity. If False, just return the unique roots, with no
           information about multiplicities.

        -  ``algorithm`` - the root-finding algorithm to use.
           We attempt to select a reasonable algorithm by default, but this
           lets the caller override our choice.


        By default, this finds all the roots that lie in the base ring of
        the polynomial. However, the ring parameter can be used to specify
        a ring to look for roots in.

        If the polynomial and the output ring are both exact (integers,
        rationals, finite fields, etc.), then the output should always be
        correct (or raise an exception, if that case is not yet handled).

        If the output ring is approximate (floating-point real or complex
        numbers), then the answer will be estimated numerically, using
        floating-point arithmetic of at least the precision of the output
        ring. If the polynomial is ill-conditioned, meaning that a small
        change in the coefficients of the polynomial will lead to a
        relatively large change in the location of the roots, this may give
        poor results. Distinct roots may be returned as multiple roots,
        multiple roots may be returned as distinct roots, real roots may be
        lost entirely (because the numerical estimate thinks they are
        complex roots). Note that polynomials with multiple roots are
        always ill-conditioned; there's a footnote at the end of the
        docstring about this.

        If the output ring is a RealIntervalField or ComplexIntervalField
        of a given precision, then the answer will always be correct (or an
        exception will be raised, if a case is not implemented). Each root
        will be contained in one of the returned intervals, and the
        intervals will be disjoint. (The returned intervals may be of
        higher precision than the specified output ring.)

        At the end of this docstring (after the examples) is a description
        of all the cases implemented in this function, and the algorithms
        used. That section also describes the possibilities for
        "algorithm=", for the cases where multiple algorithms exist.

        EXAMPLES::

            sage: x = QQ['x'].0
            sage: f = x^3 - 1
            sage: f.roots()
            [(1, 1)]
            sage: f.roots(ring=CC)   # note -- low order bits slightly different on ppc.
            [(1.00000000000000, 1), (-0.500000000000000 - 0.86602540378443...*I, 1), (-0.500000000000000 + 0.86602540378443...*I, 1)]
            sage: f = (x^3 - 1)^2
            sage: f.roots()
            [(1, 2)]

        ::

            sage: f = -19*x + 884736
            sage: f.roots()
            [(884736/19, 1)]
            sage: (f^20).roots()
            [(884736/19, 20)]

        ::

            sage: K.<z> = CyclotomicField(3)
            sage: f = K.defining_polynomial()
            sage: f.roots(ring=GF(7))
            [(4, 1), (2, 1)]
            sage: g = f.change_ring(GF(7))
            sage: g.roots()
            [(4, 1), (2, 1)]
            sage: g.roots(multiplicities=False)
            [4, 2]

        A new ring.  In the example below, we add the special method
        _roots_univariate_polynomial to the base ring, and observe
        that this method is called instead to find roots of
        polynomials over this ring.  This facility can be used to
        easily extend root finding to work over new rings you
        introduce::

             sage: R.<x> = QQ[]
             sage: (x^2 + 1).roots()
             []
             sage: g = lambda f, *args, **kwds: f.change_ring(CDF).roots()
             sage: QQ._roots_univariate_polynomial = g
             sage: (x^2 + 1).roots()  # abs tol 1e-14
             [(2.7755575615628914e-17 - 1.0*I, 1), (0.9999999999999997*I, 1)]
             sage: del QQ._roots_univariate_polynomial

        An example over RR, which illustrates that only the roots in RR are
        returned::

            sage: x = RR['x'].0
            sage: f = x^3 -2
            sage: f.roots()
            [(1.25992104989487, 1)]
            sage: f.factor()
            (x - 1.25992104989487) * (x^2 + 1.25992104989487*x + 1.58740105196820)
            sage: x = RealField(100)['x'].0
            sage: f = x^3 -2
            sage: f.roots()
            [(1.2599210498948731647672106073, 1)]

        ::

            sage: x = CC['x'].0
            sage: f = x^3 -2
            sage: f.roots()
            [(1.25992104989487, 1), (-0.62996052494743... - 1.09112363597172*I, 1), (-0.62996052494743... + 1.09112363597172*I, 1)]
            sage: f.roots(algorithm='pari')
            [(1.25992104989487, 1), (-0.629960524947437 - 1.09112363597172*I, 1), (-0.629960524947437 + 1.09112363597172*I, 1)]

        Another example showing that only roots in the base ring are
        returned::

            sage: x = polygen(ZZ)
            sage: f = (2*x-3) * (x-1) * (x+1)
            sage: f.roots()
            [(1, 1), (-1, 1)]
            sage: f.roots(ring=QQ)
            [(3/2, 1), (1, 1), (-1, 1)]

        An example involving large numbers::

            sage: x = RR['x'].0
            sage: f = x^2 - 1e100
            sage: f.roots()
            [(-1.00000000000000e50, 1), (1.00000000000000e50, 1)]
            sage: f = x^10 - 2*(5*x-1)^2
            sage: f.roots(multiplicities=False)
            [-1.6772670339941..., 0.19995479628..., 0.20004530611..., 1.5763035161844...]

        ::

            sage: x = CC['x'].0
            sage: i = CC.0
            sage: f = (x - 1)*(x - i)
            sage: f.roots(multiplicities=False)
            [1.00000000000000, 1.00000000000000*I]
            sage: g=(x-1.33+1.33*i)*(x-2.66-2.66*i)
            sage: g.roots(multiplicities=False)
            [1.33000000000000 - 1.33000000000000*I, 2.66000000000000 + 2.66000000000000*I]

        Describing roots using radical expressions::

            sage: x = QQ['x'].0
            sage: f = x^2 + 2
            sage: f.roots(SR)
            [(-I*sqrt(2), 1), (I*sqrt(2), 1)]
            sage: f.roots(SR, multiplicities=False)
            [-I*sqrt(2), I*sqrt(2)]

        The roots of some polynomials can't be described using radical
        expressions::

            sage: (x^5 - x + 1).roots(SR)
            []

        For some other polynomials, no roots can be found at the moment
        due to the way roots are computed. :trac:`17516` addresses
        these defecits. Until that gets implemented, one such example
        is the following::

            sage: f = x^6-300*x^5+30361*x^4-1061610*x^3+1141893*x^2-915320*x+101724
            sage: f.roots()
            []

        A purely symbolic roots example::

            sage: X = var('X')
            sage: f = expand((X-1)*(X-I)^3*(X^2 - sqrt(2))); f
            X^6 - (3*I + 1)*X^5 - sqrt(2)*X^4 + (3*I - 3)*X^4 + (3*I + 1)*sqrt(2)*X^3 + (I + 3)*X^3 - (3*I - 3)*sqrt(2)*X^2 - I*X^2 - (I + 3)*sqrt(2)*X + I*sqrt(2)
            sage: f.roots()
            [(I, 3), (-2^(1/4), 1), (2^(1/4), 1), (1, 1)]

        The same operation, performed over a polynomial ring
        with symbolic coefficients::

            sage: X = SR['X'].0
            sage: f = (X-1)*(X-I)^3*(X^2 - sqrt(2)); f
            X^6 + (-3*I - 1)*X^5 + (-sqrt(2) + 3*I - 3)*X^4 + ((3*I + 1)*sqrt(2) + I + 3)*X^3 + (-(3*I - 3)*sqrt(2) - I)*X^2 + (-(I + 3)*sqrt(2))*X + I*sqrt(2)
            sage: f.roots()
            [(I, 3), (-2^(1/4), 1), (2^(1/4), 1), (1, 1)]
            sage: f.roots(multiplicities=False)
            [I, -2^(1/4), 2^(1/4), 1]

        A couple of examples where the base ring doesn't have a
        factorization algorithm (yet). Note that this is currently done via
        naive enumeration, so could be very slow::

            sage: R = Integers(6)
            sage: S.<x> = R['x']
            sage: p = x^2-1
            sage: p.roots()
            Traceback (most recent call last):
            ...
            NotImplementedError: root finding with multiplicities for this polynomial not implemented (try the multiplicities=False option)
            sage: p.roots(multiplicities=False)
            [1, 5]
            sage: R = Integers(9)
            sage: A = PolynomialRing(R, 'y')
            sage: y = A.gen()
            sage: f = 10*y^2 - y^3 - 9
            sage: f.roots(multiplicities=False)
            [0, 1, 3, 6]

        An example over the complex double field (where root finding is
        fast, thanks to NumPy)::

            sage: R.<x> = CDF[]
            sage: f = R.cyclotomic_polynomial(5); f
            x^4 + x^3 + x^2 + x + 1.0
            sage: f.roots(multiplicities=False)  # abs tol 1e-9
            [-0.8090169943749469 - 0.5877852522924724*I, -0.8090169943749473 + 0.5877852522924724*I, 0.30901699437494773 - 0.951056516295154*I, 0.30901699437494756 + 0.9510565162951525*I]
            sage: [z^5 for z in f.roots(multiplicities=False)]  # abs tol 1e-14
            [0.9999999999999957 - 1.2864981197413038e-15*I, 0.9999999999999976 + 3.062854959141552e-15*I, 1.0000000000000024 + 1.1331077795295987e-15*I, 0.9999999999999953 - 2.0212861992297117e-15*I]
            sage: f = CDF['x']([1,2,3,4]); f
            4.0*x^3 + 3.0*x^2 + 2.0*x + 1.0
            sage: r = f.roots(multiplicities=False)
            sage: [f(a).abs() for a in r]  # abs tol 1e-14
            [2.574630599127759e-15, 1.457101633618084e-15, 1.1443916996305594e-15]

        Another example over RDF::

            sage: x = RDF['x'].0
            sage: ((x^3 -1)).roots()  # abs tol 4e-16
            [(1.0000000000000002, 1)]
            sage: ((x^3 -1)).roots(multiplicities=False)  # abs tol 4e-16
            [1.0000000000000002]

        More examples involving the complex double field::

            sage: x = CDF['x'].0
            sage: i = CDF.0
            sage: f = x^3 + 2*i; f
            x^3 + 2.0*I
            sage: f.roots()  # abs tol 1e-14
            [(-1.0911236359717227 - 0.6299605249474374*I, 1), (3.885780586188048e-16 + 1.2599210498948734*I, 1), (1.0911236359717211 - 0.6299605249474363*I, 1)]
            sage: f.roots(multiplicities=False)  # abs tol 1e-14
            [-1.0911236359717227 - 0.6299605249474374*I, 3.885780586188048e-16 + 1.2599210498948734*I, 1.0911236359717211 - 0.6299605249474363*I]
            sage: [abs(f(z)) for z in f.roots(multiplicities=False)]  # abs tol 1e-14
            [8.95090418262362e-16, 8.728374398092689e-16, 1.0235750533041806e-15]
            sage: f = i*x^3 + 2; f
            I*x^3 + 2.0
            sage: f.roots()  # abs tol 1e-14
            [(-1.0911236359717227 + 0.6299605249474374*I, 1), (3.885780586188048e-16 - 1.2599210498948734*I, 1), (1.0911236359717211 + 0.6299605249474363*I, 1)]
            sage: abs(f(f.roots()[0][0]))  # abs tol 1e-13
            1.1102230246251565e-16

        Examples using real root isolation::

            sage: x = polygen(ZZ)
            sage: f = x^2 - x - 1
            sage: f.roots()
            []
            sage: f.roots(ring=RIF)
            [(-0.6180339887498948482045868343657?, 1), (1.6180339887498948482045868343657?, 1)]
            sage: f.roots(ring=RIF, multiplicities=False)
            [-0.6180339887498948482045868343657?, 1.6180339887498948482045868343657?]
            sage: f.roots(ring=RealIntervalField(150))
            [(-0.6180339887498948482045868343656381177203091798057628621354486227?, 1), (1.618033988749894848204586834365638117720309179805762862135448623?, 1)]
            sage: f.roots(ring=AA)
            [(-0.618033988749895?, 1), (1.618033988749895?, 1)]
            sage: f = f^2 * (x - 1)
            sage: f.roots(ring=RIF)
            [(-0.6180339887498948482045868343657?, 2), (1.0000000000000000000000000000000?, 1), (1.6180339887498948482045868343657?, 2)]
            sage: f.roots(ring=RIF, multiplicities=False)
            [-0.6180339887498948482045868343657?, 1.0000000000000000000000000000000?, 1.6180339887498948482045868343657?]

        Examples using complex root isolation::

            sage: x = polygen(ZZ)
            sage: p = x^5 - x - 1
            sage: p.roots()
            []
            sage: p.roots(ring=CIF)
            [(1.167303978261419?, 1), (-0.764884433600585? - 0.352471546031727?*I, 1), (-0.764884433600585? + 0.352471546031727?*I, 1), (0.181232444469876? - 1.083954101317711?*I, 1), (0.181232444469876? + 1.083954101317711?*I, 1)]
            sage: p.roots(ring=ComplexIntervalField(200))
            [(1.167303978261418684256045899854842180720560371525489039140082?, 1), (-0.76488443360058472602982318770854173032899665194736756700778? - 0.35247154603172624931794709140258105439420648082424733283770?*I, 1), (-0.76488443360058472602982318770854173032899665194736756700778? + 0.35247154603172624931794709140258105439420648082424733283770?*I, 1), (0.18123244446987538390180023778112063996871646618462304743774? - 1.08395410131771066843034449298076657427364024315511565430114?*I, 1), (0.18123244446987538390180023778112063996871646618462304743774? + 1.08395410131771066843034449298076657427364024315511565430114?*I, 1)]
            sage: rts = p.roots(ring=QQbar); rts
            [(1.167303978261419?, 1), (-0.7648844336005847? - 0.3524715460317263?*I, 1), (-0.7648844336005847? + 0.3524715460317263?*I, 1), (0.1812324444698754? - 1.083954101317711?*I, 1), (0.1812324444698754? + 1.083954101317711?*I, 1)]
            sage: p.roots(ring=AA)
            [(1.167303978261419?, 1)]
            sage: p = (x - rts[4][0])^2 * (3*x^2 + x + 1)
            sage: p.roots(ring=QQbar)
            [(-0.1666666666666667? - 0.552770798392567?*I, 1), (-0.1666666666666667? + 0.552770798392567?*I, 1), (0.1812324444698754? + 1.083954101317711?*I, 2)]
            sage: p.roots(ring=CIF)
            [(-0.1666666666666667? - 0.552770798392567?*I, 1), (-0.1666666666666667? + 0.552770798392567?*I, 1), (0.1812324444698754? + 1.083954101317711?*I, 2)]

        Note that coefficients in a number field with defining polynomial
        `x^2 + 1` are considered to be Gaussian rationals (with the
        generator mapping to +I), if you ask for complex roots.

        ::

            sage: K.<im> = NumberField(x^2 + 1)
            sage: y = polygen(K)
            sage: p = y^4 - 2 - im
            sage: p.roots(ring=CC)
            [(-1.2146389322441... - 0.14142505258239...*I, 1), (-0.14142505258239... + 1.2146389322441...*I, 1), (0.14142505258239... - 1.2146389322441...*I, 1), (1.2146389322441... + 0.14142505258239...*I, 1)]
            sage: p = p^2 * (y^2 - 2)
            sage: p.roots(ring=CIF)
            [(-1.414213562373095?, 1), (1.414213562373095?, 1), (-1.214638932244183? - 0.141425052582394?*I, 2), (-0.141425052582394? + 1.214638932244183?*I, 2), (0.141425052582394? - 1.214638932244183?*I, 2), (1.214638932244183? + 0.141425052582394?*I, 2)]

        Note that one should not use NumPy when wanting high precision
        output as it does not support any of the high precision types::

            sage: R.<x> = RealField(200)[]
            sage: f = x^2 - R(pi)
            sage: f.roots()
            [(-1.7724538509055160272981674833411451827975494561223871282138, 1), (1.7724538509055160272981674833411451827975494561223871282138, 1)]
            sage: f.roots(algorithm='numpy')
            doctest... UserWarning: NumPy does not support arbitrary precision arithmetic.  The roots found will likely have less precision than you expect.
            [(-1.77245385090551..., 1), (1.77245385090551..., 1)]

        We can also find roots over number fields::

            sage: K.<z> = CyclotomicField(15)
            sage: R.<x> = PolynomialRing(K)
            sage: (x^2 + x + 1).roots()
            [(z^5, 1), (-z^5 - 1, 1)]

        There are many combinations of floating-point input and output
        types that work. (Note that some of them are quite pointless like using
        ``algorithm='numpy'`` with high-precision types.)

        ::

            sage: rflds = (RR, RDF, RealField(100))
            sage: cflds = (CC, CDF, ComplexField(100))
            sage: def cross(a, b):
            ....:     return list(cartesian_product_iterator([a, b]))
            sage: flds = cross(rflds, rflds) + cross(rflds, cflds) + cross(cflds, cflds)
            sage: for (fld_in, fld_out) in flds:
            ....:     x = polygen(fld_in)
            ....:     f = x^3 - fld_in(2)
            ....:     x2 = polygen(fld_out)
            ....:     f2 = x2^3 - fld_out(2)
            ....:     for algo in (None, 'pari', 'numpy'):
            ....:         rts = f.roots(ring=fld_out, multiplicities=False)
            ....:         if fld_in == fld_out and algo is None:
            ....:             print("{} {}".format(fld_in, rts))
            ....:         for rt in rts:
            ....:             assert(abs(f2(rt)) <= 1e-10)
            ....:             assert(rt.parent() == fld_out)
            Real Field with 53 bits of precision [1.25992104989487]
            Real Double Field [1.25992104989...]
            Real Field with 100 bits of precision [1.2599210498948731647672106073]
            Complex Field with 53 bits of precision [1.25992104989487, -0.62996052494743... - 1.09112363597172*I, -0.62996052494743... + 1.09112363597172*I]
            Complex Double Field [1.25992104989..., -0.629960524947... - 1.0911236359717...*I, -0.629960524947... + 1.0911236359717...*I]
            Complex Field with 100 bits of precision [1.2599210498948731647672106073, -0.62996052494743658238360530364 - 1.0911236359717214035600726142*I, -0.62996052494743658238360530364 + 1.0911236359717214035600726142*I]

        Note that we can find the roots of a polynomial with algebraic
        coefficients::

            sage: rt2 = sqrt(AA(2))
            sage: rt3 = sqrt(AA(3))
            sage: x = polygen(AA)
            sage: f = (x - rt2) * (x - rt3); f
                x^2 - 3.146264369941973?*x + 2.449489742783178?
            sage: rts = f.roots(); rts
            [(1.414213562373095?, 1), (1.732050807568878?, 1)]
            sage: rts[0][0] == rt2
            True
            sage: f.roots(ring=RealIntervalField(150))
            [(1.414213562373095048801688724209698078569671875376948073176679738?, 1), (1.732050807568877293527446341505872366942805253810380628055806980?, 1)]

        We can handle polynomials with huge coefficients.

        This number doesn't even fit in an IEEE double-precision float, but
        RR and CC allow a much larger range of floating-point numbers::

            sage: bigc = 2^1500
            sage: CDF(bigc)
            +infinity
            sage: CC(bigc)
            3.50746621104340e451

        Polynomials using such large coefficients can't be handled by
        numpy, but pari can deal with them::

            sage: x = polygen(QQ)
            sage: p = x + bigc
            sage: p.roots(ring=RR, algorithm='numpy')
            Traceback (most recent call last):
            ...
            LinAlgError: Array must not contain infs or NaNs
            sage: p.roots(ring=RR, algorithm='pari')
            [(-3.50746621104340e451, 1)]
            sage: p.roots(ring=AA)
            [(-3.5074662110434039?e451, 1)]
            sage: p.roots(ring=QQbar)
            [(-3.5074662110434039?e451, 1)]
            sage: p = bigc*x + 1
            sage: p.roots(ring=RR)
            [(0.000000000000000, 1)]
            sage: p.roots(ring=AA)
            [(-2.8510609648967059?e-452, 1)]
            sage: p.roots(ring=QQbar)
            [(-2.8510609648967059?e-452, 1)]
            sage: p = x^2 - bigc
            sage: p.roots(ring=RR)
            [(-5.92238652153286e225, 1), (5.92238652153286e225, 1)]
            sage: p.roots(ring=QQbar)
            [(-5.9223865215328558?e225, 1), (5.9223865215328558?e225, 1)]

        Algorithms used:

        For brevity, we will use RR to mean any RealField of any precision;
        similarly for RIF, CC, and CIF. Since Sage has no specific
        implementation of Gaussian rationals (or of number fields with
        embedding, at all), when we refer to Gaussian rationals below we
        will accept any number field with defining polynomial
        `x^2+1`, mapping the field generator to +I.

        We call the base ring of the polynomial K, and the ring given by
        the ring= argument L. (If ring= is not specified, then L is the
        same as K.)

        If K and L are floating-point (RDF, CDF, RR, or CC), then a
        floating-point root-finder is used. If L is RDF or CDF then we
        default to using NumPy's roots(); otherwise, we use PARI's
        polroots(). This choice can be overridden with
        algorithm='pari' or algorithm='numpy'. If the algorithm is
        unspecified and NumPy's roots() algorithm fails, then we fall
        back to pari (numpy will fail if some coefficient is infinite,
        for instance).

        If L is SR, then the roots will be radical expressions,
        computed as the solutions of a symbolic polynomial expression.
        At the moment this delegates to
        :meth:`sage.symbolic.expression.Expression.solve`
        which in turn uses Maxima to find radical solutions.
        Some solutions may be lost in this approach.
        Once :trac:`17516` gets implemented, all possible radical
        solutions should become available.

        If L is AA or RIF, and K is ZZ, QQ, or AA, then the root isolation
        algorithm sage.rings.polynomial.real_roots.real_roots() is used.
        (You can call real_roots() directly to get more control than this
        method gives.)

        If L is QQbar or CIF, and K is ZZ, QQ, AA, QQbar, or the Gaussian
        rationals, then the root isolation algorithm
        sage.rings.polynomial.complex_roots.complex_roots() is used. (You
        can call complex_roots() directly to get more control than this
        method gives.)

        If L is AA and K is QQbar or the Gaussian rationals, then
        complex_roots() is used (as above) to find roots in QQbar, then
        these roots are filtered to select only the real roots.

        If L is floating-point and K is not, then we attempt to change the
        polynomial ring to L (using .change_ring()) (or, if L is complex
        and K is not, to the corresponding real field). Then we use either
        PARI or numpy as specified above.

        For all other cases where K is different than L, we just use
        .change_ring(L) and proceed as below.

        The next method, which is used if K is an integral domain, is to
        attempt to factor the polynomial. If this succeeds, then for every
        degree-one factor a\*x+b, we add -b/a as a root (as long as this
        quotient is actually in the desired ring).

        If factoring over K is not implemented (or K is not an integral
        domain), and K is finite, then we find the roots by enumerating all
        elements of K and checking whether the polynomial evaluates to zero
        at that value.

        .. note::

           We mentioned above that polynomials with multiple roots are
           always ill-conditioned; if your input is given to n bits of
           precision, you should not expect more than n/k good bits
           for a k-fold root. (You can get solutions that make the
           polynomial evaluate to a number very close to zero;
           basically the problem is that with a multiple root, there
           are many such numbers, and it's difficult to choose between
           them.)

           To see why this is true, consider the naive floating-point
           error analysis model where you just pretend that all
           floating-point numbers are somewhat imprecise - a little
           'fuzzy', if you will.  Then the graph of a floating-point
           polynomial will be a fuzzy line.  Consider the graph of
           `(x-1)^3`; this will be a fuzzy line with a
           horizontal tangent at `x=1`, `y=0`. If the
           fuzziness extends up and down by about j, then it will
           extend left and right by about cube_root(j).

        TESTS::

            sage: K.<zeta> = CyclotomicField(2)
            sage: R.<x> = K[]
            sage: factor(x^3-1)
            (x - 1) * (x^2 + x + 1)

        This shows that the issue from :trac:`6237` is fixed::

            sage: R.<u> = QQ[]
            sage: g = -27*u^14 - 32*u^9
            sage: g.roots(CDF, multiplicities=False)  # abs tol 2e-15
            [-1.0345637159435719, 0.0, -0.3196977699902601 - 0.9839285635706636*I, -0.3196977699902601 + 0.9839285635706636*I, 0.8369796279620465 - 0.6081012947885318*I, 0.8369796279620465 + 0.6081012947885318*I]
            sage: g.roots(CDF)  # abs tol 2e-15
            [(-1.0345637159435719, 1), (0.0, 9), (-0.3196977699902601 - 0.9839285635706636*I, 1), (-0.3196977699902601 + 0.9839285635706636*I, 1), (0.8369796279620465 - 0.6081012947885318*I, 1), (0.8369796279620465 + 0.6081012947885318*I, 1)]

        This shows that the issue at :trac:`2418` is fixed::

            sage: x = polygen(QQ)
            sage: p = (x^50/2^100 + x^10 + x + 1).change_ring(ComplexField(106))
            sage: rts = (p/2^100).roots(multiplicities=False)
            sage: eps = 2^(-50)   # we test the roots numerically
            sage: [abs(p(rt)) < eps for rt in rts] == [True]*50
            True

        This shows that the issue at :trac:`10901` is fixed::

            sage: a = var('a'); R.<x> = SR[]
            sage: f = x - a
            sage: f.roots(RR)
            Traceback (most recent call last):
            ...
            TypeError: Cannot evaluate symbolic expression to a numeric value.
            sage: f.roots(CC)
            Traceback (most recent call last):
            ...
            TypeError: Cannot evaluate symbolic expression to a numeric value.

        We can find roots of polynomials defined over `\ZZ` or `\QQ`
        over the `p`-adics, see :trac:`15422`::

            sage: R.<x> = ZZ[]
            sage: pol = (x - 1)^2
            sage: pol.roots(Qp(3,5))
            [(1 + O(3^5), 2)]

        This doesn't work if we first change coefficients to `\QQ_p`::

            sage: pol.change_ring(Qp(3,5)).roots()
            Traceback (most recent call last):
            ...
            PrecisionError: p-adic factorization not well-defined since the discriminant is zero up to the requestion p-adic precision

            sage: (pol - 3^6).roots(Qp(3,5))
            [(1 + 2*3^3 + 2*3^4 + O(3^5), 1), (1 + 3^3 + O(3^5), 1)]
            sage: r = pol.roots(Zp(3,5), multiplicities=False); r
            [1 + O(3^5)]
            sage: parent(r[0])
            3-adic Ring with capped relative precision 5

        Spurious crash with pari-2.5.5, see :trac:`16165`::

            sage: f=(1+x+x^2)^3
            sage: f.roots(ring=CC)
            [(-0.500000000000000 - 0.866025403784439*I, 3),
             (-0.500000000000000 + 0.866025403784439*I, 3)]

        Test a crash reported at :trac:`19649`::

            sage: polRing.<x> = PolynomialRing(ZZ)
            sage: j = (x+1)^2 * (x-1)^7 * (x^2-x+1)^5
            sage: j.roots(CC)
            [(-1.00000000000000, 2),
             (1.00000000000000, 7),
             (0.500000000000000 - 0.866025403784439*I, 5),
             (0.500000000000000 + 0.866025403784439*I, 5)]
        """
        K = self.parent().base_ring()
        if hasattr(K, '_roots_univariate_polynomial'):
            return K._roots_univariate_polynomial(self, ring=ring, multiplicities=multiplicities, algorithm=algorithm, **kwds)

        if kwds:
            raise TypeError("roots() got unexpected keyword argument(s): {}".format(kwds.keys()))

        L = K if ring is None else ring

        late_import()

        input_fp = (is_RealField(K)
                    or is_ComplexField(K)
                    or is_RealDoubleField(K)
                    or is_ComplexDoubleField(K))
        output_fp = (is_RealField(L)
                     or is_ComplexField(L)
                     or is_RealDoubleField(L)
                     or is_ComplexDoubleField(L))
        input_complex = (is_ComplexField(K)
                         or is_ComplexDoubleField(K))
        output_complex = (is_ComplexField(L)
                          or is_ComplexDoubleField(L))
        input_gaussian = (isinstance(K, NumberField_quadratic)
                          and list(K.polynomial()) == [1, 0, 1])

        if input_fp and output_fp:
            # allow for possibly using a fast but less reliable
            # floating point algorithm from numpy
            low_prec = is_RealDoubleField(K) or is_ComplexDoubleField(K)
            if algorithm is None:
                if low_prec:
                    algorithm = 'either'
                else:
                    algorithm = 'pari'

            if algorithm != 'numpy' and algorithm != 'either' and algorithm != 'pari':
                raise ValueError("Unknown algorithm '%s'" % algorithm)

            # We should support GSL, too.  We could also support PARI's
            # old Newton-iteration algorithm.

            input_arbprec = (is_RealField(K) or
                             is_ComplexField(K))

            if algorithm == 'numpy' or algorithm == 'either':
                if K.prec() > 53 and L.prec() > 53:
                    from warnings import warn
                    warn('NumPy does not support arbitrary precision arithmetic.  ' +
                         'The roots found will likely have less precision than ' +
                         'you expect.')

                import numpy
                from numpy.linalg.linalg import LinAlgError
                numpy_dtype = ('complex' if input_complex else 'double')
                ty = (complex if input_complex else float)
                coeffs = self.list()
                numpy_array = numpy.array([ty(c) for c in reversed(coeffs)], dtype=numpy_dtype)
                try:
                    ext_rts1 = numpy.roots(numpy_array)
                    rts = []
                    for rt in ext_rts1:
                        rts.append(CDF(rt))
                    rts.sort()
                    ext_rts = rts
                except (ValueError, LinAlgError):
                    if algorithm == 'either':
                        algorithm = 'pari'
                    else:
                        raise

            if algorithm == 'pari':
                if not input_arbprec:
                    self = self.change_ring(CC if input_complex else RR)
                ext_rts = self._pari_().polroots(precision=L.prec())

            if output_complex:
                rts = sort_complex_numbers_for_display([L(root) for root in ext_rts])
            else:
                rts = sorted([L(root.real()) for root in ext_rts if root.imag() == 0])

            rts_mult = []
            j = 0
            while j < len(rts):
                rt = rts[j]
                mult = rts.count(rt)
                rts_mult.append((rt, mult))
                j += mult

            if multiplicities:
                return rts_mult
            else:
                return [rt for (rt, mult) in rts_mult]

        from sage.symbolic.ring import SR
        if L is SR:
            vname = 'do_not_use_this_name_in_a_polynomial_coefficient'
            var = SR(vname)
            expr = self(var)
            rts = expr.solve(var,
                             explicit_solutions=True,
                             multiplicities=multiplicities)
            if multiplicities:
                return [(rt.rhs(), mult) for rt, mult in zip(*rts)]
            else:
                return [rt.rhs() for rt in rts]

        if L != K or is_AlgebraicField_common(L):
            # So far, the only "special" implementations are for real
            # and complex root isolation and for p-adic factorization
            if (is_IntegerRing(K) or is_RationalField(K)
                or is_AlgebraicRealField(K)) and \
                (is_AlgebraicRealField(L) or is_RealIntervalField(L)):

                from sage.rings.polynomial.real_roots import real_roots

                if is_AlgebraicRealField(L):
                    rts = real_roots(self, retval='algebraic_real')
                else:
                    diam = ~(ZZ(1) << L.prec())
                    rts1 = real_roots(self, retval='interval', max_diameter=diam)

                    # We (essentially) promise in the docstring above
                    # that returned intervals will be at least the precision
                    # of the given ring.  But real_roots() does not guarantee
                    # this; for instance, if it returns exactly zero,
                    # it may return this with a low-precision
                    # RealIntervalFieldElement.

                    rts = []
                    for (rt, mult) in rts1:
                        if rt.prec() < L.prec():
                            rt = L(rt)
                        rts.append((rt, mult))

                if multiplicities:
                    return rts
                else:
                    return [rt for (rt, mult) in rts]

            if (is_IntegerRing(K) or is_RationalField(K)
                or is_AlgebraicField_common(K) or input_gaussian) and \
                (is_ComplexIntervalField(L) or is_AlgebraicField_common(L)):

                from sage.rings.polynomial.complex_roots import complex_roots

                if is_ComplexIntervalField(L):
                    rts = complex_roots(self, min_prec=L.prec())
                elif is_AlgebraicField(L):
                    rts = complex_roots(self, retval='algebraic')
                else:
                    rts = complex_roots(self, retval='algebraic_real')

                if multiplicities:
                    return rts
                else:
                    return [rt for (rt, mult) in rts]

            if output_fp and output_complex and not input_gaussian:
                # If we want the complex roots, and the input is not
                # floating point, we convert to a real polynomial
                # (except when the input coefficients are Gaussian rationals).
                if is_ComplexDoubleField(L):
                    real_field = RDF
                else:
                    real_field = RealField(L.prec())

                return self.change_ring(real_field).roots(ring=L, multiplicities=multiplicities, algorithm=algorithm)
            elif is_pAdicRing(L) or is_pAdicField(L):
                p = L.prime()
                n = L.precision_cap()
                try:
                    F = self.factor_padic(p, n)
                except AttributeError:
                    pass
                else:
                    return self.change_ring(L)._roots_from_factorization(F, multiplicities)

            return self.change_ring(L).roots(multiplicities=multiplicities, algorithm=algorithm)

        try:
            if K.is_integral_domain():
                if not K.is_field():
                    try:
                        # get rid of the content of self since we don't need it
                        # and we really don't want to factor it if it's a huge
                        # integer
                        c = self.content()
                        self = self//c
                    except AttributeError:
                        pass
                return self._roots_from_factorization(self.factor(), multiplicities)
            else:
                raise NotImplementedError
        except NotImplementedError:
            if K.is_finite():
                if multiplicities:
                    raise NotImplementedError("root finding with multiplicities for this polynomial not implemented (try the multiplicities=False option)")
                else:
                    return [a for a in K if not self(a)]

            raise NotImplementedError("root finding for this polynomial not implemented")

    def _roots_from_factorization(self, F, multiplicities):
        """
        Given a factorization ``F`` of the polynomial ``self``, return
        the roots of ``self``.

        EXAMPLES::

            sage: R.<x> = ZZ[]
            sage: pol = 20*x^3 - 50*x^2 + 20*x
            sage: F = pol.factor(); F
            2 * 5 * (x - 2) * x * (2*x - 1)
            sage: pol._roots_from_factorization(F, multiplicities=True)
            [(2, 1), (0, 1)]
            sage: pol.change_ring(QQ)._roots_from_factorization(F, multiplicities=False)
            [2, 0, 1/2]
        """
        seq = []
        K = self.parent().base_ring()
        for fac in F:
            g = fac[0]
            if g.degree() == 1:
                rt = -g[0]/g[1]
                # We need to check that this root is actually in K;
                # otherwise we'd return roots in the fraction field of K.
                if rt in K:
                    rt = K(rt)
                    if multiplicities:
                        seq.append((rt,fac[1]))
                    else:
                        seq.append(rt)
        return seq

    def real_roots(self):
        """
        Return the real roots of this polynomial, without multiplicities.

        Calls self.roots(ring=RR), unless this is a polynomial with
        floating-point real coefficients, in which case it calls
        self.roots().

        EXAMPLES::

            sage: x = polygen(ZZ)
            sage: (x^2 - x - 1).real_roots()
            [-0.618033988749895, 1.61803398874989]

        TESTS::

            sage: x = polygen(RealField(100))
            sage: (x^2 - x - 1).real_roots()[0].parent()
                Real Field with 100 bits of precision
            sage: x = polygen(RDF)
            sage: (x^2 - x - 1).real_roots()[0].parent()
            Real Double Field

            sage: x=polygen(ZZ,'x'); v=(x^2-x-1).real_roots()
            sage: v[0].parent() is RR
            True
        """
        K = self.base_ring()
        if is_RealField(K) or is_RealDoubleField(K):
            return self.roots(multiplicities=False)

        return self.roots(ring=RR, multiplicities=False)

    def complex_roots(self):
        """
        Return the complex roots of this polynomial, without
        multiplicities.

        Calls self.roots(ring=CC), unless this is a polynomial with
        floating-point coefficients, in which case it is uses the
        appropriate precision from the input coefficients.

        EXAMPLES::

            sage: x = polygen(ZZ)
            sage: (x^3 - 1).complex_roots()   # note: low order bits slightly different on ppc.
            [1.00000000000000, -0.500000000000000 - 0.86602540378443...*I, -0.500000000000000 + 0.86602540378443...*I]

        TESTS::

            sage: x = polygen(RR)
            sage: (x^3 - 1).complex_roots()[0].parent()
            Complex Field with 53 bits of precision
            sage: x = polygen(RDF)
            sage: (x^3 - 1).complex_roots()[0].parent()
            Complex Double Field
            sage: x = polygen(RealField(200))
            sage: (x^3 - 1).complex_roots()[0].parent()
            Complex Field with 200 bits of precision
            sage: x = polygen(CDF)
            sage: (x^3 - 1).complex_roots()[0].parent()
            Complex Double Field
            sage: x = polygen(ComplexField(200))
            sage: (x^3 - 1).complex_roots()[0].parent()
            Complex Field with 200 bits of precision
            sage: x=polygen(ZZ,'x'); v=(x^2-x-1).complex_roots()
            sage: v[0].parent() is CC
            True
        """
        K = self.base_ring()
        if is_RealField(K):
            return self.roots(ring=ComplexField(K.prec()), multiplicities=False)
        if is_RealDoubleField(K):
            return self.roots(ring=CDF, multiplicities=False)
        if is_ComplexField(K) or is_ComplexDoubleField(K):
            return self.roots(multiplicities=False)

        return self.roots(ring=CC, multiplicities=False)

    def number_of_roots_in_interval(self, a=None, b=None):
        r"""
        Return the number of roots of this polynomial in the interval 
        [a,b], counted without multiplicity. The endpoints a, b default to
        -Infinity, Infinity (which are also valid input values).

        Calls the PARI routine polsturm. Note that as of version 2.8, PARI
        includes the left endpoint of the interval (and no longer uses
        Sturm's algorithm on exact inputs). polsturm requires a polynomial
        with real coefficients; in case PARI returns an error, we try again
        after taking the GCD of `self` with its complex conjugate.
        
        EXAMPLES::

            sage: R.<x> = PolynomialRing(ZZ)
            sage: pol = (x-1)^2 * (x-2)^2 * (x-3)
            sage: pol.number_of_roots_in_interval(1, 2)
            2
            sage: pol.number_of_roots_in_interval(1.01, 2)
            1
            sage: pol.number_of_roots_in_interval(None, 2)
            2
            sage: pol.number_of_roots_in_interval(1, Infinity)
            3
            sage: pol.number_of_roots_in_interval()
            3
            sage: pol = (x-1)*(x-2)*(x-3)
            sage: pol2 = pol.change_ring(CC)
            sage: pol2.number_of_roots_in_interval()
            3
            sage: R.<x> = PolynomialRing(CC)
            sage: pol = (x-1)*(x-CC(I))
            sage: pol.number_of_roots_in_interval(0,2)
            1

        TESTS::
        
            sage: R.<x> = PolynomialRing(ZZ)
            sage: pol = (x-1)^2 * (x-2)^2 * (x-3)
            sage: pol.number_of_roots_in_interval(1, 2)
            2
            sage: pol = chebyshev_T(5,x)
            sage: pol.number_of_roots_in_interval(-1,2)
            5
            sage: pol.number_of_roots_in_interval(0,2)
            3

        """
        pol = self // self.gcd(self.derivative()) #squarefree part
        if a is None:
            a1 = -infinity.infinity
        else:
            a1 = a
        if b is None:
            b1 = infinity.infinity
        else:
            b1 = b
        try:
            return(pari(pol).polsturm([a1,b1]))
        except PariError:
            # Take GCD with the conjugate, to extract the maximum factor
            # with real coefficients.
            pol2 = pol.gcd(pol.map_coefficients(lambda z: z.conjugate()))
            return(pari(pol2).polsturm([a1,b1]))

    def number_of_real_roots(self):
        r"""
        Return the number of real roots of this polynomial, counted
        without multiplicity. 
        
        EXAMPLES::

            sage: R.<x> = PolynomialRing(ZZ)
            sage: pol = (x-1)^2 * (x-2)^2 * (x-3)
            sage: pol.number_of_real_roots()
            3
            sage: pol = (x-1)*(x-2)*(x-3)
            sage: pol2 = pol.change_ring(CC)
            sage: pol2.number_of_real_roots()
            3
            sage: R.<x> = PolynomialRing(CC)
            sage: pol = (x-1)*(x-CC(I))
            sage: pol.number_of_real_roots()
            1
        """
        return self.number_of_roots_in_interval()

    def all_roots_in_interval(self, a=None, b=None):
        r"""
        Return True if the roots of this polynomial are all real and 
        contained in the given interval.
    
        EXAMPLES::

            sage: R.<x> = PolynomialRing(ZZ)
            sage: pol = (x-1)^2 * (x-2)^2 * (x-3)
            sage: pol.all_roots_in_interval(1, 3)
            True
            sage: pol.all_roots_in_interval(1.01, 3)
            False
            sage: pol = chebyshev_T(5,x)
            sage: pol.all_roots_in_interval(-1,1)
            True        
            sage: pol = chebyshev_T(5,x/2)
            sage: pol.all_roots_in_interval(-1,1)
            False
            sage: pol.all_roots_in_interval()
            True
        """
        pol = self // self.gcd(self.derivative())
        return(pol.number_of_roots_in_interval(a,b) == pol.degree())

    def is_real_rooted(self):
        r"""
        Return True if the roots of this polynomial are all real.
    
        EXAMPLES::

            sage: R.<x> = PolynomialRing(ZZ)
            sage: pol = chebyshev_T(5, x)
            sage: pol.is_real_rooted()
            True
            sage: pol = x^2 + 1
            sage: pol.is_real_rooted()
            False
        """
        return self.all_roots_in_interval()

    def variable_name(self):
        """
        Return name of variable used in this polynomial as a string.

        OUTPUT: string

        EXAMPLES::

            sage: R.<t> = QQ[]
            sage: f = t^3 + 3/2*t + 5
            sage: f.variable_name()
            't'
        """
        return self.parent().variable_name()

    @coerce_binop
    def xgcd(self, other):
        r"""
        Return an extended gcd of this polynomial and ``other``.

        INPUT:

        - ``other`` -- a polynomial in the same ring as this polynomial

        OUTPUT:

        A tuple ``(r, s, t)`` where ``r`` is a greatest common divisor
        of this polynomial and ``other``, and ``s`` and ``t`` are such
        that ``r = s*self + t*other`` holds.

        .. NOTE::

            The actual algorithm for computing the extended gcd depends on the
            base ring underlying the polynomial ring. If the base ring defines
            a method ``_xgcd_univariate_polynomial``, then this method will be
            called (see examples below).

        EXAMPLES::

            sage: R.<x> = QQbar[]
            sage: (2*x^2).gcd(2*x)
            x
            sage: R.zero().gcd(0)
            0
            sage: (2*x).gcd(0)
            x

        One can easily add xgcd functionality to new rings by providing a
        method ``_xgcd_univariate_polynomial``::

            sage: R.<x> = QQ[]
            sage: S.<y> = R[]
            sage: h1 = y*x
            sage: h2 = y^2*x^2
            sage: h1.xgcd(h2)
            Traceback (most recent call last):
            ...
            NotImplementedError: Univariate Polynomial Ring in x over Rational Field does not provide an xgcd implementation for univariate polynomials
            sage: T.<x,y> = QQ[]
            sage: def poor_xgcd(f,g):
            ....:     ret = S(T(f).gcd(g))
            ....:     if ret == f: return ret,S.one(),S.zero()
            ....:     if ret == g: return ret,S.zero(),S.one()
            ....:     raise NotImplementedError
            sage: R._xgcd_univariate_polynomial = poor_xgcd
            sage: h1.xgcd(h2)
            (x*y, 1, 0)
            sage: del R._xgcd_univariate_polynomial

        """
        if hasattr(self.base_ring(), '_xgcd_univariate_polynomial'):
            return self.base_ring()._xgcd_univariate_polynomial(self, other)
        else:
            raise NotImplementedError("%s does not provide an xgcd implementation for univariate polynomials"%self.base_ring())

    def variables(self):
        """
        Returns the tuple of variables occurring in this polynomial.

        EXAMPLES::

            sage: R.<x> = QQ[]
            sage: x.variables()
            (x,)

        A constant polynomial has no variables.

        ::

            sage: R(2).variables()
            ()
        """
        if self.is_constant():
            return ()
        else:
            return self._parent.gens()

    def args(self):
        """
        Returns the generator of this polynomial ring, which is the (only)
        argument used when calling self.

        EXAMPLES::

            sage: R.<x> = QQ[]
            sage: x.args()
            (x,)

        A constant polynomial has no variables, but still takes a single
        argument.

        ::

            sage: R(2).args()
            (x,)
        """
        return self._parent.gens()

    def valuation(self, p=None):
        r"""
        If `f = a_r x^r + a_{r+1}x^{r+1} + \cdots`, with
        `a_r` nonzero, then the valuation of `f` is
        `r`. The valuation of the zero polynomial is
        `\infty`.

        If a prime (or non-prime) `p` is given, then the valuation
        is the largest power of `p` which divides self.

        The valuation at `\infty` is -self.degree().

        EXAMPLES::

            sage: P.<x> = ZZ[]
            sage: (x^2+x).valuation()
            1
            sage: (x^2+x).valuation(x+1)
            1
            sage: (x^2+1).valuation()
            0
            sage: (x^3+1).valuation(infinity)
            -3
            sage: P(0).valuation()
            +Infinity
        """
        cdef int k

        if not self:
            return infinity.infinity

        if p is infinity.infinity:
            return -self.degree()

        if p is None:
            for k from 0 <= k <= self.degree():
                if self[k]:
                    return ZZ(k)
        if isinstance(p, Polynomial):
            p = self.parent().coerce(p)
        elif is_Ideal(p) and p.ring() is self.parent(): # eventually need to handle fractional ideals in the fraction field
            if self.parent().base_ring().is_field(): # common case
                p = p.gen()
            else:
                raise NotImplementedError
        else:
            from sage.rings.fraction_field import is_FractionField
            if is_FractionField(p.parent()) and self.parent().has_coerce_map_from(p.parent().ring()):
                p = self.parent().coerce(p.parent().ring()(p)) # here we require that p be integral.
            else:
                raise TypeError("The polynomial, p, must have the same parent as self.")

        if p.degree() == 0:
            raise ArithmeticError("The polynomial, p, must have positive degree.")
        k = 0
        while self % p == 0:
            k = k + 1
            self //= p
        return sage.rings.integer.Integer(k)

    def ord(self, p=None):
        r"""
        This is the same as the valuation of self at p. See the
        documentation for ``self.valuation``.

        EXAMPLES::

            sage: R.<x> = ZZ[]
            sage: (x^2+x).ord(x+1)
            1
        """
        return self.valuation(p)

    def add_bigoh(self, prec):
        r"""
        Returns the power series of precision at most prec got by adding
        `O(q^\text{prec})` to self, where q is its variable.

        EXAMPLES::

            sage: R.<x> = ZZ[]
            sage: f = 1 + 4*x + x^3
            sage: f.add_bigoh(7)
            1 + 4*x + x^3 + O(x^7)
            sage: f.add_bigoh(2)
            1 + 4*x + O(x^2)
            sage: f.add_bigoh(2).parent()
            Power Series Ring in x over Integer Ring
        """
        return self.parent().completion(self.parent().gen())(self).add_bigoh(prec)

    def is_irreducible(self):
        """
        Return True precisely if this polynomial is irreducible over its
        base ring.

        Testing irreducibility over `\ZZ/n\ZZ` for composite `n` is not
        implemented.

        EXAMPLES::

            sage: R.<x> = ZZ[]
            sage: (x^3 + 1).is_irreducible()
            False
            sage: (x^2 - 1).is_irreducible()
            False
            sage: (x^3 + 2).is_irreducible()
            True
            sage: R(0).is_irreducible()
            False

        See :trac:`5140`,

        ::

            sage: R(1).is_irreducible()
            False
            sage: R(4).is_irreducible()
            False
            sage: R(5).is_irreducible()
            True

        The base ring does matter:  for example, 2x is irreducible as a
        polynomial in QQ[x], but not in ZZ[x],

        ::

            sage: R.<x> = ZZ[]
            sage: R(2*x).is_irreducible()
            False
            sage: R.<x> = QQ[]
            sage: R(2*x).is_irreducible()
            True

        TESTS::

            sage: F.<t> = NumberField(x^2-5)
            sage: Fx.<xF> = PolynomialRing(F)
            sage: f = Fx([2*t - 5, 5*t - 10, 3*t - 6, -t, -t + 2, 1])
            sage: f.is_irreducible()
            False
            sage: f = Fx([2*t - 3, 5*t - 10, 3*t - 6, -t, -t + 2, 1])
            sage: f.is_irreducible()
            True
        """
        if self.is_zero():
            return False
        if self.is_unit():
            return False
        if self.degree() == 0:
            return self.base_ring()(self).is_irreducible()

        F = self.factor()
        if len(F) > 1 or F[0][1] > 1:
            return False
        return True

    def shift(self, n):
        r"""
        Returns this polynomial multiplied by the power `x^n`. If
        `n` is negative, terms below `x^n` will be
        discarded. Does not change this polynomial (since polynomials are
        immutable).

        EXAMPLES::

            sage: R.<x> = QQ[]
            sage: p = x^2 + 2*x + 4
            sage: p.shift(0)
             x^2 + 2*x + 4
            sage: p.shift(-1)
             x + 2
            sage: p.shift(-5)
             0
            sage: p.shift(2)
             x^4 + 2*x^3 + 4*x^2

        One can also use the infix shift operator::

            sage: f = x^3 + x
            sage: f >> 2
            x
            sage: f << 2
            x^5 + x^3

        TESTS::

            sage: p = R(0)
            sage: p.shift(3).is_zero()
            True
            sage: p.shift(-3).is_zero()
            True

        AUTHORS:

        - David Harvey (2006-08-06)

        - Robert Bradshaw (2007-04-18): Added support for infix
          operator.
        """
        if n == 0 or self.degree() < 0:
            return self   # safe because immutable.
        if n > 0:
            output = [self.base_ring().zero()] * n
            output.extend(self.coefficients(sparse=False))
            return self._parent(output, check=False)
        if n < 0:
            if n > self.degree():
                return self._parent([])
            else:
                return self._parent(self.coefficients(sparse=False)[-int(n):], check=False)

    def __lshift__(self, k):
        """
        EXAMPLE::

            sage: R.<x> = ZZ[]
            sage: f = x + 2
            sage: f << 3
            x^4 + 2*x^3
        """
        return self.shift(k)

    def __rshift__(self, k):
        """
        EXAMPLES::

            sage: R.<x> = ZZ[]
            sage: f = x^4 + 2*x^3
            sage: f >> 3
            x + 2
        """
        return self.shift(-k)

    cpdef Polynomial truncate(self, long n):
        r"""
        Returns the polynomial of degree ` < n` which is equivalent
        to self modulo `x^n`.

        EXAMPLES::

            sage: R.<x> = ZZ[]; S.<y> = PolynomialRing(R, sparse=True)
            sage: f = y^3 + x*y -3*x; f
            y^3 + x*y - 3*x
            sage: f.truncate(2)
            x*y - 3*x
            sage: f.truncate(1)
            -3*x
            sage: f.truncate(0)
            0
        """
        # __getitem__ already returns a polynomial!!
        # We must not have check=False, since 0 must not have __coeffs = [0].
        return <Polynomial>self._parent(self[:n])#, check=False)

    cdef _inplace_truncate(self, long prec):
        return self.truncate(prec)

    def is_nth_power(self, n):
        """
        Return whether this polynomial is an ``n``-th power in the polynomial ring.

        INPUT:

        - ``n`` -- an integer

        EXAMPLES::

            sage: R.<x> = GF(3)[]
            sage: x.is_nth_power(1)
            True
            sage: x.is_nth_power(2)
            False
            sage: (x^3).is_nth_power(3)
            True
            sage: R(2).is_nth_power(-3)
            True

        """
        if n == 0:
            return self.is_one()
        if n < 0:
            return self.is_unit() and (~(self[0])).is_nth_power(-n)
        return all([n.divides(e) for e in self.exponents()]) and all([c.is_nth_power(n) for c in self.coefficients()])

    def nth_root(self, n):
        """
        Return a polynomial ``a`` such that this polynomial equals ``a^n``.

        INPUT:

        - ``n`` -- an integer

        EXAMPLES::

            sage: R.<x> = GF(3)[]
            sage: x.nth_root(1)
            x
            sage: x.nth_root(2)
            Traceback (most recent call last):
            ...
            ValueError: element is not an n-th power.
            sage: (x^3).nth_root(3)
            x
            sage: R(2).nth_root(-3)
            2

        """
        if not self.is_nth_power(n):
            raise ValueError("element is not an n-th power.")

        if n < 0:
            return self.parent()(self[0].nth_root(-n))
        if n == 0:
            return self.parent().one()
        return self.parent()([c.nth_root(n) for c in self.coeffs()[::n]])

    def is_squarefree(self):
        """
        Return False if this polynomial is not square-free, i.e., if there is a
        non-unit `g` in the polynomial ring such that `g^2` divides ``self``.

        .. WARNING::

            This method is not consistent with
            :meth:`.squarefree_decomposition` since the latter does not factor
            the content of a polynomial. See the examples below.

        EXAMPLES::

            sage: R.<x> = QQ[]
            sage: f = (x-1)*(x-2)*(x^2-5)*(x^17-3); f
            x^21 - 3*x^20 - 3*x^19 + 15*x^18 - 10*x^17 - 3*x^4 + 9*x^3 + 9*x^2 - 45*x + 30
            sage: f.is_squarefree()
            True
            sage: (f*(x^2-5)).is_squarefree()
            False

        A generic implementation is available, which relies on gcd
        computations::

            sage: R.<x> = ZZ[]
            sage: (2*x).is_squarefree()
            True
            sage: (4*x).is_squarefree()
            False
            sage: (2*x^2).is_squarefree()
            False
            sage: R(0).is_squarefree()
            False
            sage: S.<y> = QQ[]
            sage: R.<x> = S[]
            sage: (2*x*y).is_squarefree()
            True
            sage: (2*x*y^2).is_squarefree()
            False

        In positive characteristic, we compute the square-free
        decomposition or a full factorization, depending on which is
        available::

            sage: K.<t> = FunctionField(GF(3))
            sage: R.<x> = K[]
            sage: (x^3-x).is_squarefree()
            True
            sage: (x^3-1).is_squarefree()
            False
            sage: (x^3+t).is_squarefree()
            True
            sage: (x^3+t^3).is_squarefree()
            False

        In the following example, `t^2` is a unit in the base field::

            sage: R(t^2).is_squarefree()
            True

        This method is not consistent with :meth:`.squarefree_decomposition`::

            sage: R.<x> = ZZ[]
            sage: f = 4 * x
            sage: f.is_squarefree()
            False
            sage: f.squarefree_decomposition()
            (4) * x

        If you want this method equally not to consider the content, you can
        remove it as in the following example::

            sage: c = f.content()
            sage: (f/c).is_squarefree()
            True

        If the base ring is not an integral domain, the question is not
        mathematically well-defined::

            sage: R.<x> = IntegerModRing(9)[]
            sage: pol = (x + 3)*(x + 6); pol
            x^2
            sage: pol.is_squarefree()
            Traceback (most recent call last):
            ...
            TypeError: is_squarefree() is not defined for polynomials over Ring of integers modulo 9
        """
        B = self.parent().base_ring()
        if B not in sage.categories.integral_domains.IntegralDomains():
            raise TypeError("is_squarefree() is not defined for polynomials over {}".format(B))

        # a square-free polynomial has a square-free content
        if not B.is_field():
            content = self.content()
            if content not in self.parent().base_ring():
                content = content.gen()
            if not content.is_squarefree():
                return False

        # separable polynomials are square-free
        if self.derivative().gcd(self).is_constant():
            return True

        # for characteristic zero rings, square-free polynomials have to be separable
        if B.characteristic().is_zero():
            return False

        # over rings of positive characteristic, we rely on the square-free decomposition if available
        try:
            F = self.squarefree_decomposition()
        # We catch:
        # - NotImplementedError in case squarefree decomposition is not implemented
        # - AttributeError in case p-th roots are not (or do not exist)
        except (NotImplementedError, AttributeError):
            F = self.factor()
        return all([e<=1 for (f,e) in F])

    def radical(self):
        """
        Returns the radical of self; over a field, this is the product of
        the distinct irreducible factors of self. (This is also sometimes
        called the "square-free part" of self, but that term is ambiguous;
        it is sometimes used to mean the quotient of self by its maximal
        square factor.)

        EXAMPLES::

            sage: P.<x> = ZZ[]
            sage: t = (x^2-x+1)^3 * (3*x-1)^2
            sage: t.radical()
            3*x^3 - 4*x^2 + 4*x - 1
            sage: radical(12 * x^5)
            6*x

        If self has a factor of multiplicity divisible by the characteristic (see :trac:`8736`)::

            sage: P.<x> = GF(2)[]
            sage: (x^3 + x^2).radical()
            x^2 + x
        """
        P = self.parent()
        R = P.base_ring()
        p = R.characteristic()
        if p == 0 or p > self.degree():
            if R.is_field():
                return self // self.gcd(self.derivative())
            else:
                # Be careful with the content: return the
                # radical of the content times the radical of
                # (self/content)
                content = self.content()
                self_1 = (self//content)
                return (self_1 // self_1.gcd(self_1.derivative())) * content.radical()
        else:  # The above method is not always correct (see Trac 8736)
            return self.factor().radical_value()

    def content(self):
        """
        Return the content of ``self``, which is the ideal generated by the coefficients of ``self``.

        EXAMPLES::

            sage: R.<x> = IntegerModRing(4)[]
            sage: f = x^4 + 3*x^2 + 2
            sage: f.content()
            Ideal (2, 3, 1) of Ring of integers modulo 4
        """
        return self.base_ring().ideal(self.coefficients())

    def norm(self, p):
        r"""
        Return the `p`-norm of this polynomial.

        DEFINITION: For integer `p`, the `p`-norm of a
        polynomial is the `p`\th root of the sum of the
        `p`\th powers of the absolute values of the coefficients of
        the polynomial.

        INPUT:


        -  ``p`` - (positive integer or +infinity) the degree
           of the norm


        EXAMPLES::

            sage: R.<x> = RR[]
            sage: f = x^6 + x^2 + -x^4 - 2*x^3
            sage: f.norm(2)
            2.64575131106459
            sage: (sqrt(1^2 + 1^2 + (-1)^2 + (-2)^2)).n()
            2.64575131106459

        ::

            sage: f.norm(1)
            5.00000000000000
            sage: f.norm(infinity)
            2.00000000000000

        ::

            sage: f.norm(-1)
            Traceback (most recent call last):
            ...
            ValueError: The degree of the norm must be positive

        TESTS::

            sage: R.<x> = RR[]
            sage: f = x^6 + x^2 + -x^4 -x^3
            sage: f.norm(int(2))
            2.00000000000000

        Check that :trac:`18600` is fixed::

            sage: R.<x> = PolynomialRing(ZZ, sparse=True)
            sage: (x^2^100 + 1).norm(1)
            2.00000000000000

        AUTHORS:

        - Didier Deshommes
        - William Stein: fix bugs, add definition, etc.
        """
        if p <= 0 :
            raise ValueError("The degree of the norm must be positive")

        coeffs = self.coefficients()
        if p == infinity.infinity:
            return RR(max([abs(i) for i in coeffs]))

        p = sage.rings.integer.Integer(p)  # because we'll do 1/p below.

        if p == 1:
            return RR(sum([abs(i) for i in coeffs]))

        return RR(sum([abs(i)**p for i in coeffs]))**(1/p)

    def number_of_terms(self):
        """
        Returns the number of non-zero coefficients of self. Also called weight,
        hamming weight or sparsity.

        EXAMPLES::

            sage: R.<x> = ZZ[]
            sage: f = x^3 - x
            sage: f.number_of_terms()
            2
            sage: R(0).number_of_terms()
            0
            sage: f = (x+1)^100
            sage: f.number_of_terms()
            101
            sage: S = GF(5)['y']
            sage: S(f).number_of_terms()
            5
            sage: cyclotomic_polynomial(105).number_of_terms()
            33

        The method :meth:`hamming_weight` is an alias::

            sage: f.hamming_weight()
            101
        """
        cdef long w = 0
        for a in self.coefficients(sparse=False):
            if a:
                w += 1
        return w

    # alias hamming_weight for number_of_terms:
    hamming_weight = number_of_terms

    def map_coefficients(self, f, new_base_ring = None):
        """
        Returns the polynomial obtained by applying ``f`` to the non-zero
        coefficients of self.

        If ``f`` is a :class:`sage.categories.map.Map`, then the resulting
        polynomial will be defined over the codomain of ``f``. Otherwise, the
        resulting polynomial will be over the same ring as self. Set
        ``new_base_ring`` to override this behaviour.

        INPUT:

        - ``f`` -- a callable that will be applied to the coefficients of self.

        - ``new_base_ring`` (optional) -- if given, the resulting polynomial
          will be defined over this ring.

        EXAMPLES::

            sage: R.<x> = SR[]
            sage: f = (1+I)*x^2 + 3*x - I
            sage: f.map_coefficients(lambda z: z.conjugate())
            (-I + 1)*x^2 + 3*x + I
            sage: R.<x> = ZZ[]
            sage: f = x^2 + 2
            sage: f.map_coefficients(lambda a: a + 42)
            43*x^2 + 44
            sage: R.<x> = PolynomialRing(SR, sparse=True)
            sage: f = (1+I)*x^(2^32) - I
            sage: f.map_coefficients(lambda z: z.conjugate())
            (-I + 1)*x^4294967296 + I
            sage: R.<x> = PolynomialRing(ZZ, sparse=True)
            sage: f = x^(2^32) + 2
            sage: f.map_coefficients(lambda a: a + 42)
            43*x^4294967296 + 44

        Examples with different base ring::

            sage: R.<x> = ZZ[]
            sage: k = GF(2)
            sage: residue = lambda x: k(x)
            sage: f = 4*x^2+x+3
            sage: g = f.map_coefficients(residue); g
            x + 1
            sage: g.parent()
            Univariate Polynomial Ring in x over Integer Ring
            sage: g = f.map_coefficients(residue, new_base_ring = k); g
            x + 1
            sage: g.parent()
            Univariate Polynomial Ring in x over Finite Field of size 2 (using NTL)
            sage: residue = k.coerce_map_from(ZZ)
            sage: g = f.map_coefficients(residue); g
            x + 1
            sage: g.parent()
            Univariate Polynomial Ring in x over Finite Field of size 2 (using NTL)
        """
        R = self.parent()
        if new_base_ring is not None:
            R = R.change_ring(new_base_ring)
        elif isinstance(f, Map):
            R = R.change_ring(f.codomain())
        return R(dict([(k,f(v)) for (k,v) in self.dict().items()]))

    def is_cyclotomic(self, certificate=False, algorithm="pari"):
        r"""
        Test if this polynomial is a cyclotomic polynomial.

        A *cyclotomic polynomial* is a monic, irreducible polynomial such that
        all roots are roots of unity.

        By default the answer is a boolean. But if ``certificate`` is ``True``,
        the result is a non-negative integer: it is ``0`` if ``self`` is not
        cyclotomic, and a positive integer ``n`` if ``self`` is the `n`-th
        cyclotomic polynomial.

        .. SEEALSO::

            :meth:`is_cyclotomic_product`
            :meth:`cyclotomic_part`

        INPUT:

        - ``certificate`` -- boolean, default to ``False``. Only works with
          ``algorithm`` set to "pari".

        - ``algorithm`` -- either "pari" or "sage" (default is "pari")

        ALGORITHM:

        The native algorithm implemented in Sage uses the first algorithm of
        [BD89]_. The algorithm in pari is more subtle since it does compute the
        inverse of the Euler `\phi` function to determine the `n` such that the
        polynomial is the `n`-th cyclotomic polynomial.

        EXAMPLES:

        Quick tests::

            sage: P.<x> = ZZ['x']
            sage: (x - 1).is_cyclotomic()
            True
            sage: (x + 1).is_cyclotomic()
            True
            sage: (x^2 - 1).is_cyclotomic()
            False
            sage: (x^2 + x + 1).is_cyclotomic(certificate=True)
            3
            sage: (x^2 + 2*x + 1).is_cyclotomic(certificate=True)
            0

        Test first 100 cyclotomic polynomials::

            sage: all(cyclotomic_polynomial(i).is_cyclotomic() for i in xrange(1,101))
            True

        Some more tests::

            sage: (x^16 + x^14 - x^10 + x^8 - x^6 + x^2 + 1).is_cyclotomic(algorithm="pari")
            False
            sage: (x^16 + x^14 - x^10 + x^8 - x^6 + x^2 + 1).is_cyclotomic(algorithm="sage")
            False

            sage: (x^16 + x^14 - x^10 - x^8 - x^6 + x^2 + 1).is_cyclotomic(algorithm="pari")
            True
            sage: (x^16 + x^14 - x^10 - x^8 - x^6 + x^2 + 1).is_cyclotomic(algorithm="sage")
            True

            sage: y = polygen(QQ)
            sage: (y/2 - 1/2).is_cyclotomic()
            False
            sage: (2*(y/2 - 1/2)).is_cyclotomic()
            True

        Invalid arguments::

            sage: (x - 3).is_cyclotomic(algorithm="sage", certificate=True)
            Traceback (most recent call last):
            ...
            ValueError: no implementation of the certificate within Sage

        Test using other rings::

            sage: z = polygen(GF(5))
            sage: (z - 1).is_cyclotomic()
            Traceback (most recent call last):
            ...
            NotImplementedError: not implemented in non-zero characteristic

        TESTS::

            sage: R = ZZ['x']
            sage: for _ in range(20):
            ....:     p = R.random_element(degree=randint(10,20))
            ....:     ans_pari = p.is_cyclotomic(algorithm="pari")
            ....:     ans_sage = p.is_cyclotomic(algorithm="sage")
            ....:     assert ans_pari == ans_sage, "problem with p={}".format(p)
            sage: for d in range(2,20):
            ....:     p = cyclotomic_polynomial(d)
            ....:     assert p.is_cyclotomic(algorithm="pari"), "pari problem with p={}".format(p)
            ....:     assert p.is_cyclotomic(algorithm="sage"), "sage problem with p={}".format(p)

        Test the output type when ``certificate=True``::

            sage: type((x^2 - 2).is_cyclotomic(certificate=True))
            <type 'sage.rings.integer.Integer'>
            sage: type((x -1).is_cyclotomic(certificate=True))
            <type 'sage.rings.integer.Integer'>

        Check that the arguments are forwarded when the input is not a
        polynomial with coefficients in `\ZZ`::

            sage: x = polygen(QQ)
            sage: (x-1).is_cyclotomic(certificate=True)
            1

        REFERENCES:

        .. [BD89] \R. J. Bradford and J. H. Davenport, Effective tests
           for cyclotomic polynomials, Symbolic and Algebraic Computation (1989)
           pp. 244 -- 251, :doi:`10.1007/3-540-51084-2_22`
        """
        S = self.base_ring()
        if S.characteristic() != 0:
            raise NotImplementedError("not implemented in non-zero characteristic")
        if S != ZZ:
            try:
                f = self.change_ring(ZZ)
            except TypeError:
                return False
            return f.is_cyclotomic(certificate=certificate, algorithm=algorithm)

        if algorithm == "pari":
            ans = self._pari_().poliscyclo()
            return Integer(ans) if certificate else bool(ans)

        elif algorithm != "sage":
            raise ValueError("algorithm must be either 'pari' or 'sage'")

        elif certificate:
            raise ValueError("no implementation of the certificate within Sage")

        if not self.is_monic():
            return False

        P = self.parent()
        gen = P.gen()

        if self == gen - 1:  # the first cyc. pol. is treated apart
            return True

        if self.constant_coefficient() != 1:
            return False

        if not self.is_irreducible():
            return False

        coefs = self.coefficients(sparse=False)

        # compute the graeffe transform of self
        po_odd = P(coefs[1::2])
        po_even = P(coefs[0::2])
        f1  = po_even*po_even - gen*(po_odd*po_odd)

        # first case
        if f1 == self:
            return True

        # second case
        selfminus = self(-gen)
        if f1 == selfminus:
            if selfminus.leading_coefficient() < 0 and (-selfminus).is_cyclotomic(algorithm="sage"):
                return True
            elif selfminus.is_cyclotomic(algorithm="sage"):
                return True

        # third case, we need to take a square root
        ans, ff1 = f1.is_square(True)
        return ans and ff1.is_cyclotomic(algorithm="sage")

    def is_cyclotomic_product(self):
        r"""
        Test whether this polynomial is a product of cyclotomic polynomials.

        This method simply calls the function ``poliscycloprod`` from the Pari
        library.

        .. SEEALSO::

            :meth:`is_cyclotomic`
            :meth:`cyclotomic_part`

        EXAMPLES::

            sage: x = polygen(ZZ)
            sage: (x^5 - 1).is_cyclotomic_product()
            True
            sage: (x^5 + x^4 - x^2 + 1).is_cyclotomic_product()
            False

            sage: p = prod(cyclotomic_polynomial(i) for i in [2,5,7,12])
            sage: p.is_cyclotomic_product()
            True

            sage: (x^5 - 1/3).is_cyclotomic_product()
            False

            sage: x = polygen(Zmod(5))
            sage: (x-1).is_cyclotomic_product()
            Traceback (most recent call last):
            ...
            NotImplementedError: not implemented in non-zero characteristic
        """
        if self.base_ring().characteristic() != 0:
            raise NotImplementedError("not implemented in non-zero characteristic")
        if self.base_ring() != ZZ:
            try:
                f = self.change_ring(ZZ)
            except TypeError:
                return False
            return f.is_cyclotomic_product()

        return bool(self._pari_().poliscycloprod())

    def cyclotomic_part(self):
        """
        Return the product of the irreducible factors of this polynomial
        which are cyclotomic polynomials.

        .. SEEALSO::

            :meth:`is_cyclotomic`
            :meth:`is_cyclotomic_product`

        EXAMPLES::

            sage: P.<x> = PolynomialRing(Integers())
            sage: pol = 2*(x^4 + 1)
            sage: pol.cyclotomic_part()
            x^4 + 1
            sage: pol = x^4 + 2
            sage: pol.cyclotomic_part()
            1
            sage: pol = (x^4 + 1)^2 * (x^4 + 2)
            sage: pol.cyclotomic_part()
            x^8 + 2*x^4 + 1

            sage: P.<x> = PolynomialRing(QQ)
            sage: pol = (x^4 + 1)^2 * (x^4 + 2)
            sage: pol.cyclotomic_part()
            x^8 + 2*x^4 + 1

            sage: P.<x> = PolynomialRing(RR)
            sage: pol = (x^4 + 1)^2 * (x^4 + 2)
            sage: pol.cyclotomic_part()
            Traceback (most recent call last):
            ...
            NotImplementedError: not implemented for inexact base rings

            sage: x = polygen(Zmod(5))
            sage: (x-1).cyclotomic_part()
            Traceback (most recent call last):
            ...
            NotImplementedError: not implemented in non-zero characteristic
        """
        S = self.base_ring()
        if S.characteristic() != 0:
            raise NotImplementedError("not implemented in non-zero characteristic")
        if not S.is_exact():
            raise NotImplementedError("not implemented for inexact base rings")
        R = self.parent()
        x = R.gen()
        # Extract Phi_n when n is odd.
        t1 = self
        while True:
            t2 = t1.gcd(t1(x**2))
            if t1.degree() == t2.degree(): break
            t1 = t2
        ans = t1
        # Extract Phi_n when v_2(n) = 1, 2, ...
        t0 = self // t1
        i = 0
        while t0.degree() > 0:
            t1 = t0
            while True:
                t2 = t1.gcd(t1(-x**2))
                if t1.degree() == t2.degree(): break
                t1 = t2
            ans *= t1(x**(2**i))
            t0 = t0 // t1
            t1 = t0.gcd(t0(-x))
            t0 = R(list(t1)[::2])
            i += 1
        return(ans // ans.leading_coefficient())

    def homogenize(self, var='h'):
        r"""
        Return the homogenization of this polynomial.

        The polynomial itself is returned if it is homogeneous already. Otherwise,
        its monomials are multiplied with the smallest powers of ``var`` such
        that they all have the same total degree.

        INPUT:

        - ``var`` -- a variable in the polynomial ring (as a string, an element
          of the ring, or ``0``) or a name for a new variable (default:
          ``'h'``)

        OUTPUT:

        If ``var`` specifies the variable in the polynomial ring, then a
        homogeneous element in that ring is returned. Otherwise, a homogeneous
        element is returned in a polynomial ring with an extra last variable
        ``var``.

        EXAMPLES::

            sage: R.<x> = QQ[]
            sage: f = x^2 + 1
            sage: f.homogenize()
            x^2 + h^2

        The parameter ``var`` can be used to specify the name of the variable::

            sage: g = f.homogenize('z'); g
            x^2 + z^2
            sage: g.parent()
            Multivariate Polynomial Ring in x, z over Rational Field

        However, if the polynomial is homogeneous already, then that parameter
        is ignored and no extra variable is added to the polynomial ring::

            sage: f = x^2
            sage: g = f.homogenize('z'); g
            x^2
            sage: g.parent()
            Univariate Polynomial Ring in x over Rational Field

        For compatibility with the multivariate case, if ``var`` specifies the
        variable of the polynomial ring, then the monomials are multiplied with
        the smallest powers of ``var`` such that the result is homogeneous; in
        other words, we end up with a monomial whose leading coefficient is the
        sum of the coefficients of the polynomial::

            sage: f = x^2 + x + 1
            sage: f.homogenize('x')
            3*x^2

        In positive characterstic, the degree can drop in this case::

            sage: R.<x> = GF(2)[]
            sage: f = x + 1
            sage: f.homogenize(x)
            0

        For compatibility with the multivariate case, the parameter ``var`` can
        also be 0 to specify the variable in the polynomial ring::

            sage: R.<x> = QQ[]
            sage: f = x^2 + x + 1
            sage: f.homogenize(0)
            3*x^2

        """
        if self.is_homogeneous():
            return self

        x, = self.variables()

        if isinstance(var, int) or isinstance(var, Integer):
            if var:
                raise TypeError("Variable index %d must be < 1." % var)
            else:
                return sum(self.coefficients())*x**self.degree()

        x_name = self.variable_name()
        var = str(var)

        if var == x_name:
            return sum(self.coefficients())*x**self.degree()

        P = PolynomialRing(self.base_ring(), [x_name, var])
        return P(self)._homogenize(1)

    def is_homogeneous(self):
        r"""
        Return ``True`` if this polynomial is homogeneous.

        EXAMPLES::

            sage: P.<x> = PolynomialRing(QQ)
            sage: x.is_homogeneous()
            True
            sage: P(0).is_homogeneous()
            True
            sage: (x+1).is_homogeneous()
            False
        """
        return len(self.exponents()) < 2

    def nth_root(self, n):
        r"""
        Return a `n`-th root of this polynomial.

        This is computed using Newton method in the ring of power series. This
        method works only when the base ring is an integral domain. Morever, for
        polynomial whose coefficient of lower degree is different from 1, the
        elements of the base ring should have a method ``nth_root`` implemented.

        EXAMPLES::

            sage: R.<x> = ZZ[]
            sage: a = 27 * (x+3)**6 * (x+5)**3
            sage: a.nth_root(3)
            3*x^3 + 33*x^2 + 117*x + 135

            sage: b = 25 * (x^2 + x + 1)
            sage: b.nth_root(2)
            Traceback (most recent call last):
            ...
            ValueError: not a 2nd power
            sage: R(0).nth_root(3)
            0
            sage: R.<x> = QQ[]
            sage: a = 1/4 * (x/7 + 3/2)^2 * (x/2 + 5/3)^4
            sage: a.nth_root(2)
            1/56*x^3 + 103/336*x^2 + 365/252*x + 25/12

            sage: K.<sqrt2> = QuadraticField(2)
            sage: R.<x> = K[]
            sage: a = (x + sqrt2)^3 * ((1+sqrt2)*x - 1/sqrt2)^6
            sage: b = a.nth_root(3); b
            (2*sqrt2 + 3)*x^3 + (2*sqrt2 + 2)*x^2 + (-2*sqrt2 - 3/2)*x + 1/2*sqrt2
            sage: b^3 == a
            True

            sage: R.<x> = QQbar[]
            sage: p = x**3 + QQbar(2).sqrt() * x - QQbar(3).sqrt()
            sage: r = (p**5).nth_root(5)
            sage: r * p[0] == p * r[0]
            True
            sage: p = (x+1)^20 + x^20
            sage: p.nth_root(20)
            Traceback (most recent call last):
            ...
            ValueError: not a 20th power

            sage: z = GF(4).gen()
            sage: R.<x> = GF(4)[]
            sage: p = z*x**4 + 2*x - 1
            sage: r = (p**15).nth_root(15)
            sage: r * p[0] == p * r[0]
            True
            sage: ((x+1)**2).nth_root(2)
            x + 1
            sage: ((x+1)**4).nth_root(4)
            x + 1
            sage: ((x+1)**12).nth_root(12)
            x + 1
            sage: (x^4 + x^3 + 1).nth_root(2)
            Traceback (most recent call last):
            ...
            ValueError: not a 2nd power
            sage: p = (x+1)^17 + x^17
            sage: r = p.nth_root(17)
            Traceback (most recent call last):
            ...
            ValueError: not a 17th power

            sage: R1.<x> = QQ[]
            sage: R2.<y> = R1[]
            sage: R3.<z> = R2[]
            sage: (((y**2+x)*z^2 + x*y*z + 2*x)**3).nth_root(3)
            (y^2 + x)*z^2 + x*y*z + 2*x
            sage: ((x+y+z)**5).nth_root(5)
            z + y + x

        Here we consider a base ring without ``nth_root`` method. The third
        example with a non-trivial coefficient of lowest degree raises an error::

            sage: R.<x> = QQ[]
            sage: R2 = R.quotient(x**2 + 1)
            sage: x = R2.gen()
            sage: R3.<y> = R2[]
            sage: (y**2 - 2*y + 1).nth_root(2)
            -y + 1
            sage: (y**3).nth_root(3)
            y
            sage: (y**2 + x).nth_root(2)
            Traceback (most recent call last):
            ...
            AttributeError: ... has no attribute 'nth_root'

        TESTS::

            sage: R.<x> = ZZ[]
            sage: (x^12).nth_root(6)
            x^2
            sage: parent(R.one().nth_root(3))
            Univariate Polynomial Ring in x over Integer Ring
            sage: p = (x+1)**20 + x^20
            sage: p.nth_root(20)
            Traceback (most recent call last):
            ...
            ValueError: not a 20th power
            sage: (x^3 - 1).nth_root(2)
            Traceback (most recent call last):
            ...
            ValueError: not a 2nd power
            sage: (x^3 - 1).nth_root(2)
            Traceback (most recent call last):
            ...
            ValueError: not a 2nd power

            sage: Zmod(4)['x'].one().nth_root(4)
            Traceback (most recent call last):
            ...
            ValueError: n-th root of polynomials over rings with zero divisors
            not implemented

        Some random tests::

            sage: for R in [QQ['x'], GF(4)['x']]:
            ....:     for _ in range(30):
            ....:         p = R.random_element(degree=randint(10,20))
            ....:         n = ZZ.random_element(2,20)
            ....:         r = (p**n).nth_root(n)
            ....:         assert r.parent() is R, "R={}\nn={}\np={}".format(R,n,p)
            ....:         pl = p.leading_coefficient()
            ....:         rl = r.leading_coefficient()
            ....:         assert p == r * pl/rl, "R={}\np={}\nr={}".format(R,p,r)
        """
        cdef Integer c, cc, e, m
        cdef Polynomial p, q, qi, r

        R = self.base_ring()
        if R not in sage.categories.integral_domains.IntegralDomains():
            raise ValueError("n-th root of polynomials over rings with zero divisors not implemented")

        m = ZZ.coerce(n)
        if m <= 0:
            raise ValueError("n (={}) must be positive".format(m))
        elif m.is_one() or self.is_zero() or self.is_one():
            return self
        elif self.degree() % m:
            raise ValueError("not a %s power"%m.ordinal_str())
        elif self[0].is_zero():
            # p = x^k q
            # p^(1/n) = x^(k/n) q^(1/n)
            i = self.valuation()
            if i%m:
                raise ValueError("not a %s power"%m.ordinal_str())
            S = self.parent()
            return S.gen()**(i//m) * (self>>i).nth_root(m)
        else:
            c = R.characteristic()
            if c and not n%c:
                # characteristic divides n
                e = m.valuation(c)
                cc = c**e
                ans = {}
                for i in range(self.degree()+1):
                    if self[i]:
                        if i%cc:
                            raise ValueError("not a %s power"%m.ordinal_str())
                        ans[i//cc] = self[i].nth_root(cc)
                p = self.parent()(ans)
                m = m // cc
                if m.is_one():
                    return p
            else:
                p = self

            # beginning of Newton method
            Sorig = p.parent()
            if p[0].is_one():
                q = Sorig.one()
            else:
                q = Sorig(p[0].nth_root(m))

            R = R.fraction_field()
            p = p.change_ring(R)
            q = q.change_ring(R)

            from sage.misc.misc import newton_method_sizes
            x = p.parent().gen()
            for i in newton_method_sizes(p.degree()//m+1):
                qi = q._power_trunc(m-1, i).inverse_series_trunc(i)
                q = ((m-1) * q + qi._mul_trunc_(p,i)) / m

                # NOTE: if we knew that p was a n-th power we could remove the check
                # below and just return q after the whole loop
                r = q**m - p
                if not r:
                    return Sorig(q)
                elif not r.truncate(i).is_zero():
                    raise ValueError("not a %s power"%m.ordinal_str())
            raise ValueError("not a %s power"%m.ordinal_str())

# ----------------- inner functions -------------
# Cython can't handle function definitions inside other function

cdef do_schoolbook_product(x, y):
    """
    Compute the multiplication of two polynomials represented by lists, using
    the schoolbook algorithm.

    This is the core of _mul_generic and the code that is used by
    _mul_karatsuba bellow a threshold.

    TESTS:

    Doctested indirectly in _mul_generic and _mul_karatsuba. For the doctest we
    use a ring such that default multiplication calls external libraries::

        sage: K = ZZ['x']
        sage: f = K.random_element(8)
        sage: g = K.random_element(8)
        sage: f*g - f._mul_generic(g)
        0
    """
    cdef Py_ssize_t i, k, start, end
    cdef Py_ssize_t d1 = len(x)-1, d2 = len(y)-1
    if d1 == -1:
        return x
    elif d2 == -1:
        return y
    elif d1 == 0:
        c = x[0]
        return [c*a for a in y] # beware of noncommutative rings
    elif d2 == 0:
        c = y[0]
        return [a*c for a in x] # beware of noncommutative rings
    coeffs = []
    for k from 0 <= k <= d1+d2:
        start = 0 if k <= d2 else k-d2  # max(0, k-d2)
        end =   k if k <= d1 else d1    # min(k, d1)
        sum = x[start] * y[k-start]
        for i from start < i <= end:
            sum = sum + x[i] * y[k-i]
        coeffs.append(sum)
    return coeffs

cdef do_karatsuba_different_size(left, right, Py_ssize_t K_threshold):
    """
    Multiply two polynomials of different degrees by splitting the one of
    largest degree in chunks that are multiplied with the other using the
    Karatsuba algorithm, as explained in _mul_karatsuba.

    INPUT:

        - `left`: a list representing a polynomial
        - `right`: a list representing a polynomial
        - `K_threshold`: an Integer, a threshold to pass to the classical
          quadratic algorithm. During Karatsuba recursion, if one of the lists
          has length <= K_threshold the classical product is used instead.

    TESTS:

    This method is indirectly doctested in _mul_karatsuba.

    Here, we use Fibonacci numbers that need deepest recursion in this method.

        sage: K = ZZ['x']
        sage: f = K.random_element(21)
        sage: g = K.random_element(34)
        sage: f*g - f._mul_karatsuba(g,0)
        0
    """
    cdef Py_ssize_t n = len(left), m = len(right)
    cdef Py_ssize_t r, q, i, j, mi
    if n == 0 or m == 0:
        return []
    if n == 1:
        c = left[0]
        return [c*a for a in right]
    if m == 1:
        c = right[0]
        return [a*c for a in left] # beware of noncommutative rings
    if n <= K_threshold or m <= K_threshold:
        return do_schoolbook_product(left,right)
    if n == m:
        return do_karatsuba(left, right, K_threshold, 0, 0, n)
    if n > m:
        # left is the bigger list
        # n is the bigger number
        q = n // m
        r = n % m
        output = do_karatsuba(left, right, K_threshold, 0, 0, m)
        for i from 1 <= i < q:
            mi = m*i
            carry = do_karatsuba(left, right, K_threshold, mi, 0, m)
            for j from 0 <= j < m-1:
                output[mi+j] = output[mi+j] + carry[j]
            output.extend(carry[m-1:])
        if r:
            mi = m*q
            carry = do_karatsuba_different_size(left[mi:], right, K_threshold)
            for j from 0 <= j < m-1:
                output[mi+j] = output[mi+j] + carry[j]
            output.extend(carry[m-1:])
        return output
    else:
        # n < m, I need to repeat the code due to the case
        # of noncommutative rings.
        q = m // n
        r = m % n
        output = do_karatsuba(left, right, K_threshold, 0, 0, n)
        for i from 1 <= i < q:
            mi = n*i
            carry = do_karatsuba(left, right, K_threshold, 0, mi, n)
            for j from 0 <= j < n-1:
                output[mi+j] = output[mi+j] + carry[j]
            output.extend(carry[n-1:])
        if r:
            mi = n*q
            carry = do_karatsuba_different_size(left, right[mi:], K_threshold)
            for j from 0 <= j < n-1:
                output[mi+j] = output[mi+j] + carry[j]
            output.extend(carry[n-1:])
        return output

cdef do_karatsuba(left, right, Py_ssize_t K_threshold,Py_ssize_t start_l, Py_ssize_t start_r,Py_ssize_t num_elts):
    """
    Core routine for Karatsuba multiplication. This function works for two
    polynomials of the same degree.

    Input:

        - left: a list containing a slice representing a polynomial
        - right: a list containing the slice representing a polynomial with the
          same length as left
        - K_threshold: an integer. For lists of length <= K_threshold, the
          quadratic polynomial multiplication is used.
        - start_l: the index of left where the actual polynomial starts
        - start_r: the index of right where the actual polynomial starts
        - num_elts: the length of the polynomials.

    Thus, the actual polynomials we want to multiply are represented by the
    slices: left[ start_l: start_l+num_elts ], right[ right_l: right_l+num_elts ].
    We use this representation in order to avoid creating slices of lists and
    create smaller lists.

    Output:

        - a list representing the product of the polynomials

    Doctested indirectly in _mul_karatsuba

    TESTS::

        sage: K.<x> = ZZ[]
        sage: f = K.random_element(50) + x^51
        sage: g = K.random_element(50) + x^51
        sage: f*g - f._mul_karatsuba(g,0)
        0

    Notes on the local variables:

    - ac will always be a list of length lenac
    - bd will always be a list of length lenbd
    - a_m_b and c_m_d are lists of length ne, we only make necessary additions
    - tt1 has length lenac
    """
    cdef Py_ssize_t e, ne, lenac, lenbd, start_le, start_re, i
    if num_elts == 0:
        return []
    if num_elts == 1:
        return [left[start_l]*right[start_r]]
    if num_elts <= K_threshold:
        # Special case of degree 2, no loop, no function call
        if num_elts == 2:
            b = left[start_l]
            a = left[start_l+1]
            d = right[start_r]
            c = right[start_r+1]
            return [b*d, a*d+b*c, a*c]
        return do_schoolbook_product(left[start_l:start_l+num_elts], right[start_r:start_r+num_elts])
    if num_elts == 2:
        # beware of noncommutative rings
        b = left[start_l]
        a = left[start_l+1]
        d = right[start_r]
        c = right[start_r+1]
        ac = a*c
        bd = b*d
        return [bd, (a+b)*(c+d)-ac-bd, ac]
    e = num_elts//2
    ne = num_elts-e
    lenac = 2*ne-1
    lenbd = 2*e-1
    start_le = start_l+e
    start_re = start_r+e
    ac = do_karatsuba(left, right, K_threshold, start_le, start_re, ne)
    bd = do_karatsuba(left, right, K_threshold, start_l,  start_r,  e)
    a_m_b = left[start_le:start_le+ne]
    c_m_d = right[start_re:start_re+ne]
    for i from 0 <= i < e:
        a_m_b[i] = a_m_b[i] + left[start_l+i]
        c_m_d[i] = c_m_d[i] + right[start_r+i]
    tt1 = do_karatsuba(a_m_b, c_m_d, K_threshold, 0, 0, ne)
    # bd might be shorter than ac, we divide the operations in two loops
    for i from 0 <= i < lenbd:
        tt1[i] = tt1[i] - (ac[i]+bd[i])
    for i from lenbd <= i < lenac:
        tt1[i] = tt1[i] - ac[i]
    # Reconstruct the product from the lists bd, tt1, ac.
    for i from 0 <= i < e-1:
        bd[e+i] = bd[e+i] + tt1[i]
    bd.append(tt1[e-1])
    for i from 0 <= i < lenac -e:
        ac[i] = ac[i] + tt1[e+i]
    return bd + ac


cdef class Polynomial_generic_dense(Polynomial):
    """
    A generic dense polynomial.

    EXAMPLES::

        sage: f = QQ['x']['y'].random_element()
        sage: loads(f.dumps()) == f
        True

    TESTS::

        sage: from sage.rings.polynomial.polynomial_element_generic import Polynomial_generic_dense
        sage: isinstance(f, Polynomial_generic_dense)
        True
        sage: f = CC['x'].random_element()
        sage: isinstance(f, Polynomial_generic_dense)
        True

    """
    def __init__(self, parent, x=None, int check=1, is_gen=False, int construct=0, **kwds):
        Polynomial.__init__(self, parent, is_gen=is_gen)
        if x is None:
            self.__coeffs = []
            return

        R = parent.base_ring()
        if isinstance(x, list):
            if check:
                self.__coeffs = [R(t) for t in x]
                self.__normalize()
            else:
                self.__coeffs = x
            return

        if sage.rings.fraction_field_element.is_FractionFieldElement(x):
            if x.denominator() != 1:
                raise TypeError("denominator must be 1")
            else:
                x = x.numerator()

        if isinstance(x, Polynomial):
            if (<Element>x)._parent is self._parent:
                x = list(x.list())
            elif R.has_coerce_map_from((<Element>x)._parent):# is R or (<Element>x)._parent == R:
                try:
                    if x.is_zero():
                        self.__coeffs = []
                        return
                except (AttributeError, TypeError):
                    pass
                x = [x]
            else:
                self.__coeffs = [R(a, **kwds) for a in x.list()]
                if check:
                    self.__normalize()
                return

        elif isinstance(x, int) and x == 0:
            self.__coeffs = []
            return

        elif isinstance(x, dict):
            x = self._dict_to_list(x, R.zero())

        elif isinstance(x, pari_gen):
            x = [R(w, **kwds) for w in x.list()]
            check = 0
        elif not isinstance(x, list):
            # We trust that the element constructors do not send x=0
#            if x:
            x = [x]   # constant polynomials
#            else:
#                x = []    # zero polynomial
        if check:
            self.__coeffs = [R(z, **kwds) for z in x]
            self.__normalize()
        else:
            self.__coeffs = x

    cdef Polynomial_generic_dense _new_c(self, list coeffs, Parent P):
        cdef type t = type(self)
        cdef Polynomial_generic_dense f = <Polynomial_generic_dense>t.__new__(t)
        f._parent = P
        f.__coeffs = coeffs
        return f

    cpdef Polynomial _new_constant_poly(self, a, Parent P):
        """
        Create a new constant polynomial in P with value a.

        ASSUMPTION:

        The given value **must** be an element of the base ring. That
        assumption is not verified.

        EXAMPLES::

            sage: S.<y> = QQ[]
            sage: R.<x> = S[]
            sage: x._new_constant_poly(y+1, R)
            y + 1
            sage: parent(x._new_constant_poly(y+1, R))
            Univariate Polynomial Ring in x over Univariate Polynomial Ring in y over Rational Field
        """
        if a:
            return self._new_c([a],P)
        else:
            return self._new_c([],P)

    def __reduce__(self):
        """
        For pickling.

        TESTS::

            sage: R.<x> = QQ['a,b']['x']
            sage: f = x^3-x
            sage: loads(dumps(f)) == f
            True

        Make sure we're testing the right method::

            sage: type(f)
            <type 'sage.rings.polynomial.polynomial_element.Polynomial_generic_dense'>
        """
        return make_generic_polynomial, (self._parent, self.__coeffs)

    def __nonzero__(self):
        return len(self.__coeffs) > 0

    cdef int __normalize(self) except -1:
        """
        TESTS:

        Check that exceptions are propagated correctly (:trac:`18274`)::

            sage: class BrokenRational(Rational):
            ....:     def __nonzero__(self):
            ....:         raise NotImplementedError("cannot check whether number is non-zero")
            sage: z = BrokenRational()
            sage: R.<x> = QQ[]
            sage: from sage.rings.polynomial.polynomial_element import Polynomial_generic_dense
            sage: Polynomial_generic_dense(R, [z])
            Traceback (most recent call last):
            ...
            NotImplementedError: cannot check whether number is non-zero
        """
        cdef list x = self.__coeffs
        cdef Py_ssize_t n = len(x) - 1
        while n >= 0 and not x[n]:
            del x[n]
            n -= 1

    def __hash__(self):
        return self._hash_c()

    @cython.boundscheck(False)
    @cython.wraparound(False)
    cdef get_unsafe(self, Py_ssize_t n):
        """
        Return the `n`-th coefficient of ``self``.

        EXAMPLES::

            sage: R.<x> = RDF[]
            sage: f = (1+2*x)^5; f
            32.0*x^5 + 80.0*x^4 + 80.0*x^3 + 40.0*x^2 + 10.0*x + 1.0
            sage: f[-1]
            0.0
            sage: f[2]
            40.0
            sage: f[6]
            0.0
            sage: f[:3]
            40.0*x^2 + 10.0*x + 1.0
        """
        return self.__coeffs[n]

    def _unsafe_mutate(self, n, value):
        """
        Never use this unless you really know what you are doing.

        .. warning::

           This could easily introduce subtle bugs, since Sage assumes
           everywhere that polynomials are immutable. It's OK to use
           this if you really know what you're doing.

        EXAMPLES::

            sage: R.<x> = ZZ[]
            sage: f = (1+2*x)^2; f
            4*x^2 + 4*x + 1
            sage: f._unsafe_mutate(1, -5)
            sage: f
            4*x^2 - 5*x + 1
        """
        n = int(n)
        value = self.base_ring()(value)
        if n >= 0 and n < len(self.__coeffs):
            self.__coeffs[n] = value
            if n == len(self.__coeffs) and value == 0:
                self.__normalize()
        elif n < 0:
            raise IndexError("polynomial coefficient index must be nonnegative")
        elif value != 0:
            zero = self.base_ring().zero()
            for _ in xrange(len(self.__coeffs), n):
                self.__coeffs.append(zero)
            self.__coeffs.append(value)

    def __floordiv__(self, right):
        """
        Return the quotient upon division (no remainder).

        EXAMPLES::

            sage: R.<x> = QQbar[]
            sage: f = (1+2*x)^3 + 3*x; f
            8*x^3 + 12*x^2 + 9*x + 1
            sage: g = f // (1+2*x); g
            4*x^2 + 4*x + 5/2
            sage: f - g * (1+2*x)
            -3/2
            sage: f.quo_rem(1+2*x)
            (4*x^2 + 4*x + 5/2, -3/2)

        TESTS:

        Check that :trac:`13048` and :trac:`2034` are fixed::

            sage: R.<x> = QQbar[]
            sage: x // x
            1
            sage: x // 1
            x
            sage: x // int(1)
            x
            sage: x //= int(1); x
            x
            sage: int(1) // x  # check that this doesn't segfault
            Traceback (most recent call last):
            ...
            AttributeError: type object 'int' has no attribute 'base_ring'
        """
        if have_same_parent(self, right):
            return (<Polynomial_generic_dense>self)._floordiv_(<Polynomial_generic_dense>right)
        P = parent(self)
        d = P.base_ring()(right)
        cdef Polynomial_generic_dense res = (<Polynomial_generic_dense>self)._new_c([c // d for c in (<Polynomial_generic_dense>self).__coeffs], P)
        res.__normalize()
        return res

    cpdef _add_(self, right):
        r"""
        Add two polynomials.

        EXAMPLES::

            sage: R.<y> = QQ[]
            sage: S.<x> = R[]
            sage: S([0,1,y,2*y]) + S([1,-2*y,3])   # indirect doctest
            2*y*x^3 + (y + 3)*x^2 + (-2*y + 1)*x + 1
        """
        cdef Polynomial_generic_dense res
        cdef Py_ssize_t check=0, i, min
        x = (<Polynomial_generic_dense>self).__coeffs
        y = (<Polynomial_generic_dense>right).__coeffs
        if len(x) > len(y):
            min = len(y)
            high = x[min:]
        elif len(x) < len(y):
            min = len(x)
            high = y[min:]
        else:
            min = len(x)
        cdef list low = [x[i] + y[i] for i from 0 <= i < min]
        if len(x) == len(y):
            res = self._new_c(low, self._parent)
            res.__normalize()
            return res
        else:
            return self._new_c(low + high, self._parent)

    cpdef _sub_(self, right):
        cdef Polynomial_generic_dense res
        cdef Py_ssize_t check=0, i, min
        x = (<Polynomial_generic_dense>self).__coeffs
        y = (<Polynomial_generic_dense>right).__coeffs
        if len(x) > len(y):
            min = len(y)
            high = x[min:]
        elif len(x) < len(y):
            min = len(x)
            high = [-y[i] for i from min <= i < len(y)]
        else:
            min = len(x)
        low = [x[i] - y[i] for i from 0 <= i < min]
        if len(x) == len(y):
            res = self._new_c(low, self._parent)
            res.__normalize()
            return res
        else:
            return self._new_c(low + high, self._parent)

    cpdef _rmul_(self, RingElement c):
        if len(self.__coeffs) == 0:
            return self
        if c._parent is not (<Element>self.__coeffs[0])._parent:
            c = (<Element>self.__coeffs[0])._parent._coerce_c(c)
        v = [c * a for a in self.__coeffs]
        cdef Polynomial_generic_dense res = self._new_c(v, self._parent)
        #if not v[len(v)-1]:
        # "normalize" checks this anyway...
        res.__normalize()
        return res

    cpdef _lmul_(self, RingElement c):
        if len(self.__coeffs) == 0:
            return self
        if c._parent is not (<Element>self.__coeffs[0])._parent:
            c = (<Element>self.__coeffs[0])._parent._coerce_c(c)
        v = [a * c for a in self.__coeffs]
        cdef Polynomial_generic_dense res = self._new_c(v, self._parent)
        #if not v[len(v)-1]:
        # "normalize" checks this anyway...
        res.__normalize()
        return res

    cpdef constant_coefficient(self):
        """
        Return the constant coefficient of this polynomial.

        OUTPUT:
            element of base ring

        EXAMPLES:
            sage: R.<t> = QQ[]
            sage: S.<x> = R[]
            sage: f = x*t + x + t
            sage: f.constant_coefficient()
            t
        """
        if len(self.__coeffs) == 0:
            return self.base_ring().zero()
        else:
            return self.__coeffs[0]

    def list(self, copy=True):
        """
        Return a new copy of the list of the underlying elements of self.

        EXAMPLES::

            sage: R.<x> = GF(17)[]
            sage: f = (1+2*x)^3 + 3*x; f
            8*x^3 + 12*x^2 + 9*x + 1
            sage: f.list()
            [1, 9, 12, 8]
        """
        if copy:
            return list(self.__coeffs)
        else:
            return self.__coeffs

    def degree(self, gen=None):
        """
        EXAMPLES::

            sage: R.<x> = RDF[]
            sage: f = (1+2*x^7)^5
            sage: f.degree()
            35

        TESTS:

        Check that :trac:`12552` is fixed::

            sage: type(f.degree())
            <type 'sage.rings.integer.Integer'>

        """
        return smallInteger(len(self.__coeffs) - 1)

    def shift(self, Py_ssize_t n):
        r"""
        Returns this polynomial multiplied by the power `x^n`. If
        `n` is negative, terms below `x^n` will be
        discarded. Does not change this polynomial.

        EXAMPLES::

            sage: R.<x> = PolynomialRing(PolynomialRing(QQ,'y'), 'x')
            sage: p = x^2 + 2*x + 4
            sage: type(p)
            <type 'sage.rings.polynomial.polynomial_element.Polynomial_generic_dense'>
            sage: p.shift(0)
             x^2 + 2*x + 4
            sage: p.shift(-1)
             x + 2
            sage: p.shift(2)
             x^4 + 2*x^3 + 4*x^2

        TESTS::

            sage: p = R(0)
            sage: p.shift(3).is_zero()
            True
            sage: p.shift(-3).is_zero()
            True

        AUTHORS:

        - David Harvey (2006-08-06)
        """
        if n == 0 or self.degree() < 0:
            return self
        if n > 0:
            output = [self.base_ring().zero()] * n
            output.extend(self.__coeffs)
            return self._new_c(output, self._parent)
        if n < 0:
            if n > len(self.__coeffs) - 1:
                return self._parent([])
            else:
                return self._new_c(self.__coeffs[-int(n):], self._parent)

    @coerce_binop
    def quo_rem(self, other):
        """
        Returns the quotient and remainder of the Euclidean division of
        ``self`` and ``other``.

        Raises ZerodivisionError if ``other`` is zero. Raises ArithmeticError if the division is not exact.

        AUTHORS:

        - Kwankyu Lee (2013-06-02)

        - Bruno Grenet (2014-07-13)

        EXAMPLES::

            sage: P.<x> = QQ[]
            sage: R.<y> = P[]
            sage: f = R.random_element(10)
            sage: g = y^5+R.random_element(4)
            sage: q,r = f.quo_rem(g)
            sage: f == q*g + r
            True
            sage: g = x*y^5
            sage: f.quo_rem(g)
            Traceback (most recent call last):
            ...
            ArithmeticError: Division non exact (consider coercing to polynomials over the fraction field)
            sage: g = 0
            sage: f.quo_rem(g)
            Traceback (most recent call last):
            ...
            ZeroDivisionError: Division by zero polynomial

        TESTS:

        The following shows that :trac:`16649` is indeed fixed. ::

            sage: P.<x> = QQ[]
            sage: R.<y> = P[]
            sage: f = (2*x^3+1)*y^2 + (x^2-x+3)*y + (3*x+2)
            sage: g = (-1/13*x^2 - x)*y^2 + (-x^2 + 3*x - 155/4)*y - x - 1
            sage: h = f * g
            sage: h.quo_rem(f)
            ((-1/13*x^2 - x)*y^2 + (-x^2 + 3*x - 155/4)*y - x - 1, 0)
            sage: h += (2/3*x^2-3*x+1)*y + 7/17*x+6/5
            sage: q,r = h.quo_rem(f)
            sage: h == q*f + r and r.degree() < f.degree()
            True
        """
        if other.is_zero():
            raise ZeroDivisionError("Division by zero polynomial")
        if self.is_zero():
            return self, self

        R = self.parent().base_ring()
        x = (<Polynomial_generic_dense>self).__coeffs[:] # make a copy
        y = (<Polynomial_generic_dense>other).__coeffs
        m = len(x)  # deg(self)=m-1
        n = len(y)  # deg(other)=n-1
        if m < n:
            return self.parent()(0), self

        quo = list()
        for k from m-n >= k >= 0:
            try:
                q = R(x[n+k-1]/y[n-1])
            except TypeError:
                raise ArithmeticError("Division non exact (consider coercing to polynomials over the fraction field)")
            x[n+k-1] = R.zero()
            for j from n+k-2 >= j >= k:
                x[j] -= q * y[j-k]
            quo.insert(0,q)

        return self._new_c(quo,self._parent), self._new_c(x,self._parent)._inplace_truncate(n-1)

    cpdef Polynomial truncate(self, long n):
        r"""
        Returns the polynomial of degree ` < n` which is equivalent
        to self modulo `x^n`.

        EXAMPLES::

            sage: S.<q> = QQ['t']['q']
            sage: f = (1+q^10+q^11+q^12).truncate(11); f
            q^10 + 1
            sage: f = (1+q^10+q^100).truncate(50); f
            q^10 + 1
            sage: f.degree()
            10
            sage: f = (1+q^10+q^100).truncate(500); f
            q^100 + q^10 + 1

        TESTS:

        Make sure we're not actually testing a specialized
        implementation.

        ::

            sage: type(f)
            <type 'sage.rings.polynomial.polynomial_element.Polynomial_generic_dense'>
        """
        l = len(self.__coeffs)
        if n > l:
            n = l
        while n > 0 and not self.__coeffs[n-1]:
            n -= 1
        return self._new_c(self.__coeffs[:n], self._parent)

    cdef _inplace_truncate(self, long n):
        if n < len(self.__coeffs):
            while n > 0 and not self.__coeffs[n-1]:
                n -= 1
        self.__coeffs = self.__coeffs[:n]
        return self

def make_generic_polynomial(parent, coeffs):
    return parent(coeffs)


@cached_function
def universal_discriminant(n):
    r"""
    Return the discriminant of the 'universal' univariate polynomial
    `a_n x^n + \cdots + a_1 x + a_0` in `\ZZ[a_0, \ldots, a_n][x]`.

    INPUT:

    - ``n`` - degree of the polynomial

    OUTPUT:

    The discriminant as a polynomial in `n + 1` variables over `\ZZ`.
    The result will be cached, so subsequent computations of
    discriminants of the same degree will be faster.

    EXAMPLES::

        sage: from sage.rings.polynomial.polynomial_element import universal_discriminant
        sage: universal_discriminant(1)
        1
        sage: universal_discriminant(2)
        a1^2 - 4*a0*a2
        sage: universal_discriminant(3)
        a1^2*a2^2 - 4*a0*a2^3 - 4*a1^3*a3 + 18*a0*a1*a2*a3 - 27*a0^2*a3^2
        sage: universal_discriminant(4).degrees()
        (3, 4, 4, 4, 3)

    .. SEEALSO::
        :meth:`Polynomial.discriminant`
    """
    pr1 = PolynomialRing(ZZ, n + 1, 'a')
    pr2 = PolynomialRing(pr1, 'x')
    p = pr2(list(pr1.gens()))
    return (1 - (n&2))*p.resultant(p.derivative())//pr1.gen(n)

cpdef Polynomial generic_power_trunc(Polynomial p, Integer n, long prec):
    r"""
    Generic truncated power algorithm

    INPUT:

    - ``p`` - a polynomial

    - ``n`` - an integer (of type :class:`sage.rings.integer.Integer`)

    - ``prec`` - a precision (should fit into a C long)

    TESTS:

    Comparison with flint for polynomials over integers and finite field::

        sage: from sage.rings.polynomial.polynomial_element import generic_power_trunc

        sage: for S in [ZZ, GF(3)]:
        ....:     R = PolynomialRing(S, 'x')
        ....:     for _ in range(100):
        ....:         p = R.random_element()
        ....:         n = ZZ.random_element(0, 100)
        ....:         prec = ZZ.random_element(0, 100)
        ....:         assert p.power_trunc(n, prec) == generic_power_trunc(p, n, prec), "p = {} n = {} prec = {}".format(p, n, prec)
    """
    if mpz_sgn(n.value) < 0:
        raise ValueError("n must be a non-negative integer")
    elif prec <= 0:
        return p._parent.zero()

    if mpz_cmp_ui(n.value, 4) < 0:
        # These cases will probably be called often
        # and don't benefit from the code below
        if mpz_cmp_ui(n.value, 0) == 0:
            return p.parent().one()
        elif mpz_cmp_ui(n.value, 1) == 0:
            return p.truncate(prec)
        elif mpz_cmp_ui(n.value, 2) == 0:
            return p._mul_trunc_(p, prec)
        elif mpz_cmp_ui(n.value, 3) == 0:
            return p._mul_trunc_(p, prec)._mul_trunc_(p, prec)

    # check for idempotence, and store the result otherwise
    cdef Polynomial a = p.truncate(prec)
    cdef Polynomial aa = a._mul_trunc_(a, prec)
    if aa == a:
        return a

    # since we've computed a^2, let's start squaring there
    # so, let's keep the least-significant bit around, just
    # in case.
    cdef int mul_to_do = mpz_tstbit(n.value, 0)
    cdef mp_bitcnt_t i = 1
    cdef mp_bitcnt_t size = mpz_sizeinbase(n.value, 2)

    # One multiplication can be saved by starting with
    # the second-smallest power needed rather than with 1
    # we've already squared a, so let's start there.
    cdef Polynomial apow = aa
    while not mpz_tstbit(n.value, i):
        apow = apow._mul_trunc_(apow, prec)
        i += 1
    cdef Polynomial power = apow
    i += 1

    # now multiply that least-significant bit in...
    if mul_to_do:
        power = power._mul_trunc_(a, prec)

    # and this is straight from the book.
    while i < size:
        apow = apow._mul_trunc_(apow, prec)
        if mpz_tstbit(n.value, i):
            power = power._mul_trunc_(apow, prec)
        i += 1

    return power


cdef class Polynomial_generic_dense_inexact(Polynomial_generic_dense):
    """
    A dense polynomial over an inexact ring.

    AUTHOR:

    - Xavier Caruso (2013-03)
    """
    cdef int __normalize(self) except -1:
        r"""
        TESTS::

        Coefficients indistinguishable from 0 are not removed.

            sage: R = Zp(5)
            sage: S.<x> = R[]
            sage: S([1,R(0,20)])
            (O(5^20))*x + (1 + O(5^20))
        """
        cdef list x = self.__coeffs
        cdef Py_ssize_t n = len(x) - 1
        cdef RingElement c
        while n >= 0:
            c = x[n]
            if c.is_zero() and c.precision_absolute() is infinity.Infinity:
                del x[n]
                n -= 1
            else:
                break

    def degree(self, secure=False):
        r"""
        INPUT:

        - secure  -- a boolean (default: False)

        OUTPUT:

        The degree of self.

        If ``secure`` is True and the degree of this polynomial
        is not determined (because the leading coefficient is
        indistinguishable from 0), an error is raised

        If ``secure`` is False, the returned value is the largest
        $n$ so that the coefficient of $x^n$ does not compare equal
        to `0`.

        EXAMPLES::

            sage: K = Qp(3,10)
            sage: R.<T> = K[]
            sage: f = T + 2; f
            (1 + O(3^10))*T + (2 + O(3^10))
            sage: f.degree()
            1
            sage: (f-T).degree()
            0
            sage: (f-T).degree(secure=True)
            Traceback (most recent call last):
            ...
            PrecisionError: the leading coefficient is indistinguishable from 0

            sage: x = O(3^5)
            sage: li = [3^i * x for i in range(0,5)]; li
            [O(3^5), O(3^6), O(3^7), O(3^8), O(3^9)]
            sage: f = R(li); f
            (O(3^9))*T^4 + (O(3^8))*T^3 + (O(3^7))*T^2 + (O(3^6))*T + (O(3^5))
            sage: f.degree()
            -1
            sage: f.degree(secure=True)
            Traceback (most recent call last):
            ...
            PrecisionError: the leading coefficient is indistinguishable from 0

        AUTHOR:

        - Xavier Caruso (2013-03)
        """
        coeffs = self.__coeffs
        d = len(coeffs) - 1
        while d >= 0:
            c = coeffs[d]
            if c.is_zero():
                if secure:
                    from sage.rings.padics.precision_error import PrecisionError
                    raise PrecisionError("the leading coefficient is indistinguishable from 0")
                else:
                    d -= 1
            else:
                break
        return d

    def prec_degree(self):
        r"""
        Returns the largest `n` so that precision information is
        stored about the coefficient of `x^n`.

        Always greater than or equal to degree.

        EXAMPLES::

            sage: K = Qp(3,10)
            sage: R.<T> = K[]
            sage: f = T + 2; f
            (1 + O(3^10))*T + (2 + O(3^10))
            sage: f.degree()
            1
            sage: f.prec_degree()
            1

            sage: g = f - T; g
            (O(3^10))*T + (2 + O(3^10))
            sage: g.degree()
            0
            sage: g.prec_degree()
            1

        AUTHOR:

        - Xavier Caruso (2013-03)
        """
        return len(self.__coeffs) - 1


cdef class ConstantPolynomialSection(Map):
    """
    This class is used for conversion from a polynomial ring to its base ring.

    Since :trac:`9944`, it calls the constant_coefficient method,
    which can be optimized for a particular polynomial type.

    EXAMPLES::

        sage: P0.<y_1> = GF(3)[]
        sage: P1.<y_2,y_1,y_0> = GF(3)[]
        sage: P0(-y_1)    # indirect doctest
        2*y_1

        sage: phi = GF(3).convert_map_from(P0); phi
        Generic map:
          From: Univariate Polynomial Ring in y_1 over Finite Field of size 3
          To:   Finite Field of size 3
        sage: type(phi)
        <type 'sage.rings.polynomial.polynomial_element.ConstantPolynomialSection'>
        sage: phi(P0.one())
        1
        sage: phi(y_1)
        Traceback (most recent call last):
        ...
        TypeError: not a constant polynomial
    """
    cpdef Element _call_(self, x):
        """
        TESTS::

            sage: from sage.rings.polynomial.polynomial_element import ConstantPolynomialSection
            sage: R.<x> = QQ[]
            sage: m = ConstantPolynomialSection(R, QQ); m
            Generic map:
              From: Univariate Polynomial Ring in x over Rational Field
              To:   Rational Field
            sage: m(x-x+1/2) # implicit
            1/2
            sage: m(x-x)
            0
            sage: m(x)
            Traceback (most recent call last):
            ...
            TypeError: not a constant polynomial
        """
        if x.degree() <= 0:
            try:
                return <Element>(x.constant_coefficient())
            except AttributeError:
                return <Element>((<Polynomial>x).constant_coefficient())
        else:
            raise TypeError("not a constant polynomial")

cdef class PolynomialBaseringInjection(Morphism):
    """
    This class is used for conversion from a ring to a polynomial
    over that ring.

    It calls the _new_constant_poly method on the generator,
    which should be optimized for a particular polynomial type.

    Technically, it should be a method of the polynomial ring, but
    few polynomial rings are cython classes, and so, as a method
    of a cython polynomial class, it is faster.

    EXAMPLES:

    We demonstrate that most polynomial ring classes use
    polynomial base injection maps for coercion. They are
    supposed to be the fastest maps for that purpose. See
    :trac:`9944`. ::

        sage: R.<x> = Qp(3)[]
        sage: R.coerce_map_from(R.base_ring())
        Polynomial base injection morphism:
          From: 3-adic Field with capped relative precision 20
          To:   Univariate Polynomial Ring in x over 3-adic Field with capped relative precision 20
        sage: R.<x,y> = Qp(3)[]
        sage: R.coerce_map_from(R.base_ring())
        Polynomial base injection morphism:
          From: 3-adic Field with capped relative precision 20
          To:   Multivariate Polynomial Ring in x, y over 3-adic Field with capped relative precision 20
        sage: R.<x,y> = QQ[]
        sage: R.coerce_map_from(R.base_ring())
        Polynomial base injection morphism:
          From: Rational Field
          To:   Multivariate Polynomial Ring in x, y over Rational Field
        sage: R.<x> = QQ[]
        sage: R.coerce_map_from(R.base_ring())
        Polynomial base injection morphism:
          From: Rational Field
          To:   Univariate Polynomial Ring in x over Rational Field

    By :trac:`9944`, there are now only very few exceptions::

        sage: PolynomialRing(QQ,names=[]).coerce_map_from(QQ)
        Generic morphism:
          From: Rational Field
          To:   Multivariate Polynomial Ring in no variables over Rational Field
    """

    cdef RingElement _an_element
    cdef object _new_constant_poly_

    def __init__(self, domain, codomain):
        """
        TESTS::

            sage: from sage.rings.polynomial.polynomial_element import PolynomialBaseringInjection
            sage: PolynomialBaseringInjection(QQ, QQ['x'])
            Polynomial base injection morphism:
              From: Rational Field
              To:   Univariate Polynomial Ring in x over Rational Field
            sage: PolynomialBaseringInjection(ZZ, QQ['x'])
            Traceback (most recent call last):
            ...
            AssertionError: domain must be basering

        ::

            sage: R.<t> = Qp(2)[]
            sage: f = R.convert_map_from(R.base_ring())    # indirect doctest
            sage: f(Qp(2).one()*3)
            (1 + 2 + O(2^20))
            sage: (Qp(2).one()*3)*t
            (1 + 2 + O(2^20))*t
        """
        assert codomain.base_ring() is domain, "domain must be basering"
        Morphism.__init__(self, domain, codomain)
        self._an_element = codomain.gen()
        self._repr_type_str = "Polynomial base injection"
        self._new_constant_poly_ = self._an_element._new_constant_poly

    cdef dict _extra_slots(self, dict _slots):
        """
        EXAMPLES::

            sage: phi = QQ['x'].coerce_map_from(QQ)   # indirect doctest
            sage: phi
            Polynomial base injection morphism:
              From: Rational Field
              To:   Univariate Polynomial Ring in x over Rational Field
            sage: phi(3/1)
            3
        """
        _slots['_an_element'] = self._an_element
        _slots['_new_constant_poly_'] = self._new_constant_poly_
        return Morphism._extra_slots(self, _slots)

    cdef _update_slots(self, dict _slots):
        """
        EXAMPLES::

            sage: phi = QQ['x'].coerce_map_from(QQ)  # indirect doctest
            sage: phi
            Polynomial base injection morphism:
              From: Rational Field
              To:   Univariate Polynomial Ring in x over Rational Field
            sage: phi(3/1)
            3
        """
        Morphism._update_slots(self, _slots)
        self._an_element = _slots['_an_element']
        self._new_constant_poly_ = _slots['_new_constant_poly_']

    cpdef Element _call_(self, x):
        """
        TESTS::

            sage: from sage.rings.polynomial.polynomial_element import PolynomialBaseringInjection
            sage: m = PolynomialBaseringInjection(ZZ, ZZ['x']); m
            Polynomial base injection morphism:
              From: Integer Ring
              To:   Univariate Polynomial Ring in x over Integer Ring
            sage: m(2) # indirect doctest
            2
            sage: parent(m(2))
            Univariate Polynomial Ring in x over Integer Ring
        """
        return self._new_constant_poly_(x, self._codomain)

    cpdef Element _call_with_args(self, x, args=(), kwds={}):
        """
        TESTS::

            sage: from sage.rings.polynomial.polynomial_element import PolynomialBaseringInjection
            sage: m = PolynomialBaseringInjection(Qp(5), Qp(5)['x'])
            sage: m(1 + O(5^11), absprec = 5)   # indirect doctest
            (1 + O(5^11))
        """
        try:
            return self._codomain._element_constructor_(x, *args, **kwds)
        except AttributeError:
            # if there is no element constructor,
            # there is a custom call method.
            return self._codomain(x, *args, **kwds)

    def section(self):
        """
        TESTS::

            sage: from sage.rings.polynomial.polynomial_element import PolynomialBaseringInjection
            sage: m = PolynomialBaseringInjection(RDF, RDF['x'])
            sage: m.section()
            Generic map:
              From: Univariate Polynomial Ring in x over Real Double Field
              To:   Real Double Field
            sage: type(m.section())
            <type 'sage.rings.polynomial.polynomial_element.ConstantPolynomialSection'>
        """
        return ConstantPolynomialSection(self._codomain, self.domain())
