r"""
Function Field Elements

AUTHORS:

- William Stein: initial version

- Robert Bradshaw (2010-05-27): cythonize function field elements

- Julian Rueth (2011-06-28): treat zero correctly

- Maarten Derickx (2011-09-11): added doctests, fixed pickling
"""
#*****************************************************************************
#       Copyright (C) 2010 William Stein <wstein@gmail.com>
#       Copyright (C) 2010 Robert Bradshaw <robertwb@math.washington.edu>
#       Copyright (C) 2011 Julian Rueth <julian.rueth@gmail.com>
#       Copyright (C) 2011 Maarten Derickx <m.derickx.student@gmail.com>
#
#  Distributed under the terms of the GNU General Public License (GPL)
#  as published by the Free Software Foundation; either version 2 of
#  the License, or (at your option) any later version.
#                  http://www.gnu.org/licenses/
#*****************************************************************************

include "sage/ext/stdsage.pxi"

from sage.structure.element cimport FieldElement, RingElement, ModuleElement, Element

from sage.misc.cachefunc import cached_in_parent_method

def is_FunctionFieldElement(x):
    r"""
    Return True if x is any type of function field element.

    EXAMPLES::

        sage: t = FunctionField(QQ,'t').gen()
        sage: sage.rings.function_field.function_field_element.is_FunctionFieldElement(t)
        True
        sage: sage.rings.function_field.function_field_element.is_FunctionFieldElement(0)
        False
    """
    if isinstance(x, FunctionFieldElement): return True
    from function_field import is_FunctionField
    return is_FunctionField(x.parent())

def make_FunctionFieldElement(parent, element_class, representing_element):
    r"""
    Used for unpickling FunctionFieldElement objects (and subclasses).

    EXAMPLES::

        sage: from sage.rings.function_field.function_field_element import make_FunctionFieldElement
        sage: K.<x> = FunctionField(QQ)
        sage: make_FunctionFieldElement(K, K._element_class, (x+1)/x)
        (x + 1)/x
    """
    return element_class(parent, representing_element, reduce=False)

cdef class FunctionFieldElement(FieldElement):
    r"""
    The abstract base class for function field elements.

    EXAMPLES::

        sage: t = FunctionField(QQ,'t').gen()
        sage: isinstance(t, sage.rings.function_field.function_field_element.FunctionFieldElement)
        True
    """

    cdef readonly object _x
    cdef readonly object _matrix

    def _vector_(self, base_field=None):
        r"""
        Return the coefficients of the linear combination of self with coefficients in base.

        EXAMPLES::

            sage: K.<x> = FunctionField(QQ); R.<y> = K[]; L.<y> = K.extension(y^2-x)
            sage: R.<z> = L[]; M.<z> = L.extension(z^2-y)
            sage: (x+y+z).vector(M)             # x+y+z = (x+y+z)*1
            [z + y + x]
            sage: (x+y+z).vector(L) # x+y+z = (x+y)*1 + 1*z
            [y + x, 1]
            sage: (x+y+z).vector(K) # x+y+z = x*1 + 1*y + 1*z + 0*yz
            [x, 1, 1, 0]
        """
        if base_field is None:
            base_field = self.parent().base()
        result = [[self]]
        from itertools import chain
        for d in [f.degree() for f in self.parent()._intermediate_fields(base_field)[:-1]]:
           result = [list(chain.from_iterable([item.element().padded_list(d) for item in row])) for row in result]

        return list(chain.from_iterable(result))


    def pth_root(self):
        p = self.parent().characteristic()
        if p == 0:
            raise ValueError()
        return self.nth_root(p)

    def __reduce__(self):
        r"""
        EXAMPLES::

            sage: K = FunctionField(QQ,'x')
            sage: f = K.random_element()
            sage: loads(f.dumps()) == f
            True
        """
        return (make_FunctionFieldElement,
                (self._parent, type(self), self._x))

    cdef FunctionFieldElement _new_c(self):
        cdef type t = type(self)
        cdef FunctionFieldElement x = <FunctionFieldElement>t.__new__(t)
        x._parent = self._parent
        return x

    def _pari_(self):
        r"""
        Coerce this element to PARI.

        PARI does not know about general function field elements, so this
        raises an Exception.

        TESTS:

        Check that :trac:`16369` has been resolved::

            sage: K.<a> = FunctionField(QQ)
            sage: R.<b> = K[]
            sage: L.<b> = K.extension(b^2-a)
            sage: b._pari_()
            Traceback (most recent call last):
            ...
            NotImplementedError: PARI does not support general function field elements.

        """
        raise NotImplementedError("PARI does not support general function field elements.")

    def _latex_(self):
        r"""
        EXAMPLES::

            sage: K.<t> = FunctionField(QQ)
            sage: latex((t+1)/t)
            \frac{t + 1}{t}
            sage: latex((t+1)/t^67)
            \frac{t + 1}{t^{67}}
            sage: latex((t+1/2)/t^67)
            \frac{t + \frac{1}{2}}{t^{67}}
        """
        return self._x._latex_()

    def matrix(self, base=None):
        r"""
        Return the matrix of multiplication by self, interpreting self as an element
        of a vector space over its base field.

        EXAMPLES:

        A rational function field::

            sage: K.<t> = FunctionField(QQ)
            sage: t.matrix()
            [t]
            sage: (1/(t+1)).matrix()
            [1/(t + 1)]

        Now an example in a nontrivial extension of a rational function field::

            sage: K.<x> = FunctionField(QQ); R.<y> = K[]
            sage: L.<y> = K.extension(y^2 - x*y + 4*x^3)
            sage: y.matrix()
            [     0      1]
            [-4*x^3      x]
            sage: y.matrix().charpoly('Z')
            Z^2 - x*Z + 4*x^3

        An example in a relative extension, where neither function
        field is rational::

            sage: K.<x> = FunctionField(QQ); R.<y> = K[]
            sage: L.<y> = K.extension(y^2 - x*y + 4*x^3)
            sage: M.<T> = L[]; Z.<alpha> = L.extension(T^3 - y^2*T + x)
            sage: alpha.matrix()
            [          0           1           0]
            [          0           0           1]
            [         -x x*y - 4*x^3           0]

        We show that this matrix does indeed work as expected when making a
        vector space from a function field::

            sage: K.<x>=FunctionField(QQ)
            sage: R.<y> = K[]
            sage: L.<y> = K.extension(y^5 - (x^3 + 2*x*y + 1/x))
            sage: V, from_V, to_V = L.vector_space()
            sage: y5 = to_V(y^5); y5
            ((x^4 + 1)/x, 2*x, 0, 0, 0)
            sage: y4y = to_V(y^4) * y.matrix(); y4y
            ((x^4 + 1)/x, 2*x, 0, 0, 0)
            sage: y5 == y4y
            True
        """
        if base is None:
            base = self.parent().base_ring()

        from sage.matrix.constructor import matrix
        if base is not self.parent().base_ring():
            return self._matrix_over_base(base)

        if self._matrix is None:
            self._matrix = self._matrix_over_base(base)
        return self._matrix

    def _matrix_over_base(self, base):
        r"""
        Return the matrix of self over base, a subfield of self.parent().
        The base needs to be a field that embeds in the parent of self.
        
        EXAMPLES::
        
            sage: K.<x> = FunctionField(QQ); R.<y> = K[]; L.<y> = K.extension(y^2-x)
            sage: R.<z> = L[]; M.<z> = L.extension(z^2-y)
            sage: z._matrix_over_base(M)
            [z]
            sage: z._matrix_over_base(L)
            [0 1]
            [y 0]
            sage: z._matrix_over_base(K)
            [0 0 1 0]
            [0 0 0 1]
            [0 1 0 0]
            [x 0 0 0]
            sage: M(y)._matrix_over_base(K)
            [0 1 0 0]
            [x 0 0 0]
            [0 0 0 1]
            [0 0 x 0]
            sage: K.<x> = FunctionField(QQ); R.<y> = K[]
            sage: L.<y> = K.extension(y^2 - x*y + 4*x^3)
            sage: M.<T> = L[]; Z.<alpha> = L.extension(T^3 - y^2*T + x)
            sage: alpha._matrix_over_base(K).minpoly('T')
            T^6 + (8*x^3 - x^2)*T^4 + 2*x*T^3 + 16*x^6*T^2 + (8*x^4 - x^3)*T + x^2
        """
        fields = self.parent()._intermediate_fields(base)

        degrees = [f.degree() for f in fields[:-1]]
        from sage.misc.misc_c import prod
        total_degree = prod(degrees)

        # the basis 1,x,x^2,x*y,y,x*y,x^2*y,y^2,...
        from itertools import product
        basis = [prod([fields[i].gen()**exponents[i] for i in range(len(degrees))]) for exponents in product(*[range(d) for d in degrees])]

        from sage.matrix.matrix_space import MatrixSpace
        return MatrixSpace(base,total_degree)([(self*b)._vector_(base) for b in basis])

    def trace(self):
        r"""
        Return the trace of this function field element.

        EXAMPLES::

            sage: K.<x> = FunctionField(QQ); R.<y> = K[]
            sage: L.<y> = K.extension(y^2 - x*y + 4*x^3)
            sage: y.trace()
            x
        """
        return self.matrix().trace()

    def norm(self):
        r"""
        Return the norm of this function field element.

        EXAMPLES::

            sage: K.<x> = FunctionField(QQ); R.<y> = K[]
            sage: L.<y> = K.extension(y^2 - x*y + 4*x^3)
            sage: y.norm()
            4*x^3

        The norm is relative::

            sage: K.<x> = FunctionField(QQ); R.<y> = K[]
            sage: L.<y> = K.extension(y^2 - x*y + 4*x^3); R.<z> = L[]
            sage: M.<z> = L.extension(z^3 - y^2*z + x)
            sage: z.norm()
            -x
            sage: z.norm().parent()
            Function field in y defined by y^2 - x*y + 4*x^3
        """
        return self.matrix().determinant()

    def characteristic_polynomial(self, *args, **kwds):
        r"""
        Return the characteristic polynomial of this function field
        element.  Give an optional input string to name the variable
        in the characteristic polynomial.

        EXAMPLES::

            sage: K.<x> = FunctionField(QQ); R.<y> = K[]
            sage: L.<y> = K.extension(y^2 - x*y + 4*x^3); R.<z> = L[]
            sage: M.<z> = L.extension(z^3 - y^2*z + x)
            sage: x.characteristic_polynomial('W')
            W - x
            sage: y.characteristic_polynomial('W')
            W^2 - x*W + 4*x^3
            sage: z.characteristic_polynomial('W')
            W^3 + (-x*y + 4*x^3)*W + x
        """
        return self.matrix().characteristic_polynomial(*args, **kwds)

    charpoly = characteristic_polynomial

    def minimal_polynomial(self, *args, **kwds):
        r"""
        Return the minimal polynomial of this function field element.
        Give an optional input string to name the variable in the
        characteristic polynomial.

        EXAMPLES::

            sage: K.<x> = FunctionField(QQ); R.<y> = K[]
            sage: L.<y> = K.extension(y^2 - x*y + 4*x^3); R.<z> = L[]
            sage: M.<z> = L.extension(z^3 - y^2*z + x)
            sage: x.minimal_polynomial('W')
            W - x
            sage: y.minimal_polynomial('W')
            W^2 - x*W + 4*x^3
            sage: z.minimal_polynomial('W')
            W^3 + (-x*y + 4*x^3)*W + x
        """
        return self.matrix().minimal_polynomial(*args, **kwds)

    minpoly = minimal_polynomial

    def is_integral(self):
        r"""
        Determine if self is integral over the maximal order of the base field.

        EXAMPLES::

            sage: K.<x> = FunctionField(QQ); R.<y> = K[]
            sage: L.<y> = K.extension(y^2 - x*y + 4*x^3)
            sage: y.is_integral()
            True
            sage: (y/x).is_integral()
            True
            sage: (y/x)^2 - (y/x) + 4*x
            0
            sage: (y/x^2).is_integral()
            False
            sage: (y/x).minimal_polynomial('W')
            W^2 - W + 4*x
        """
        R = self.parent().base_field().maximal_order()
        return all([a in R for a in self.minimal_polynomial()])

cdef class FunctionFieldElement_polymod(FunctionFieldElement):
    r"""
    Elements of a finite extension of a function field.

    EXAMPLES::

        sage: K.<x> = FunctionField(QQ); R.<y> = K[]
        sage: L.<y> = K.extension(y^2 - x*y + 4*x^3)
        sage: x*y + 1/x^3
        x*y + 1/x^3
    """
    def is_constant(self):
        e = self.element()
        return e==0 or (e.degree()==0 and e[0].is_constant())

    def __init__(self, parent, x, reduce=True):
        r"""
        EXAMPLES::

            sage: K.<x> = FunctionField(QQ); R.<y> = K[]
            sage: L.<y> = K.extension(y^2 - x*y + 4*x^3)
            sage: type(y)
            <type 'sage.rings.function_field.function_field_element.FunctionFieldElement_polymod'>
        """
        FieldElement.__init__(self, parent)
        if reduce:
            self._x = x % self._parent.polynomial()
        else:
            self._x = x

    def element(self):
        r"""
        Return the underlying polynomial that represents this element.

        EXAMPLES::

            sage: K.<x> = FunctionField(QQ); R.<T> = K[]
            sage: L.<y> = K.extension(T^2 - x*T + 4*x^3)
            sage: f = y/x^2 + x/(x^2+1); f
            1/x^2*y + x/(x^2 + 1)
            sage: f.element()
            1/x^2*y + x/(x^2 + 1)
            sage: type(f.element())
            <class 'sage.rings.polynomial.polynomial_element_generic.Polynomial_generic_dense_field'>
        """
        return self._x

    def _repr_(self):
        r"""
        EXAMPLES::

            sage: K.<x> = FunctionField(QQ); R.<y> = K[]
            sage: L.<y> = K.extension(y^2 - x*y + 4*x^3)
            sage: y._repr_()
            'y'
        """
        return self._x._repr(name=self.parent().variable_name())

    def __nonzero__(self):
        r"""
        EXAMPLES::

            sage: K.<x> = FunctionField(QQ); R.<y> = K[]
            sage: L.<y> = K.extension(y^2 - x*y + 4*x^3)
            sage: bool(y)
            True
            sage: bool(L(0))
            False
            sage: bool(L.coerce(L.polynomial()))
            False
        """
        return not not self._x

    cdef int _cmp_c_impl(self, Element other) except -2:
        r"""
        EXAMPLES::

            sage: K.<x> = FunctionField(QQ); R.<y> = K[]
            sage: L.<y> = K.extension(y^2 - x*y + 4*x^3)
            sage: cmp(L(0), 0)
            0
            sage: cmp(y, L(2)) != 0
            True
        """
        cdef FunctionFieldElement left = <FunctionFieldElement>self
        cdef FunctionFieldElement right = <FunctionFieldElement>other
        return cmp(left._x, right._x)

    cpdef ModuleElement _add_(self, ModuleElement right):
        r"""
        EXAMPLES::

            sage: K.<x> = FunctionField(QQ); R.<y> = K[]
            sage: L.<y> = K.extension(y^2 - x*y + 4*x^3)
            sage: (2*y + x/(1+x^3))  +  (3*y + 5*x*y)         # indirect doctest
            (5*x + 5)*y + x/(x^3 + 1)
            sage: (y^2 - x*y + 4*x^3)==0                      # indirect doctest
            True
            sage: -y+y
            0
        """
        cdef FunctionFieldElement res = self._new_c()
        res._x = self._x + (<FunctionFieldElement>right)._x
        return res

    cpdef ModuleElement _sub_(self, ModuleElement right):
        r"""
        EXAMPLES::

            sage: K.<x> = FunctionField(QQ); R.<y> = K[]
            sage: L.<y> = K.extension(y^2 - x*y + 4*x^3)
            sage: (2*y + x/(1+x^3))  -  (3*y + 5*x*y)         # indirect doctest
            (-5*x - 1)*y + x/(x^3 + 1)
            sage: y-y
            0
        """
        cdef FunctionFieldElement res = self._new_c()
        res._x = self._x - (<FunctionFieldElement>right)._x
        return res

    cpdef RingElement _mul_(self, RingElement right):
        r"""
        EXAMPLES::

            sage: K.<x> = FunctionField(QQ); R.<y> = K[]
            sage: L.<y> = K.extension(y^2 - x*y + 4*x^3)
            sage: y  *  (3*y + 5*x*y)                          # indirect doctest
            (5*x^2 + 3*x)*y - 20*x^4 - 12*x^3
        """
        cdef FunctionFieldElement res = self._new_c()
        res._x = (self._x * (<FunctionFieldElement>right)._x) % self._parent.polynomial()
        return res

    cpdef RingElement _div_(self, RingElement right):
        r"""
        EXAMPLES::

            sage: K.<x> = FunctionField(QQ); R.<y> = K[]
            sage: L.<y> = K.extension(y^2 - x*y + 4*x^3)
            sage: (2*y + x/(1+x^3))  /  (2*y + x/(1+x^3))       # indirect doctest
            1
            sage: 1 / (y^2 - x*y + 4*x^3)                       # indirect doctest
            Traceback (most recent call last):
            ...
            ZeroDivisionError: Cannot invert 0
        """
        return self * ~right

    def __invert__(self):
        r"""
        EXAMPLES::

            sage: K.<x> = FunctionField(QQ); R.<y> = K[]
            sage: L.<y> = K.extension(y^2 - x*y + 4*x^3)
            sage: a = ~(2*y + 1/x); a                           # indirect doctest
            (-x^2/(8*x^5 + x^2 + 1/2))*y + (2*x^3 + x)/(16*x^5 + 2*x^2 + 1)
            sage: a*(2*y + 1/x)
            1
        """
        if self.is_zero():
            raise ZeroDivisionError, "Cannot invert 0"
        P = self._parent
        return P(self._x.xgcd(P._polynomial)[1])

    def nth_root(self, n):
        r"""
        Compute an ``n``-th root of this element in the function field.

        INPUT:

        - ``n`` -- an integer

        OUTPUT:

        Returns an element ``a`` in the function field such that this element
        equals `a^n`. Raises an error if no such element exists.

        ALGORITHM:

        If ``n`` is a power of the characteristic of the field and the constant
        base field is perfect, then this uses the algorithm described in
        Proposition 12 of [GiTr1996].

        REFERENCES:

        .. [GiTr1996] P. Gianni, B. Trager. Square-Free Algorithms in Positive
           Characteristic. Applicable Algebra In Engineering, Communication And
           Computing, 7(1), p. 1-14.

        .. SEEALSO::

            :meth:`is_nth_power`

        EXAMPLES::

            sage: K.<x> = FunctionField(GF(3))
            sage: R.<y> = K[]
            sage: L.<y> = K.extension(y^2 - x)
            sage: L(y^3).nth_root(3)
            y
            sage: L(y^9).nth_root(-9)
            1/x*y

        This also works for inseparable extensions::

            sage: K.<x> = FunctionField(GF(3))
            sage: R.<y> = K[]
            sage: L.<y> = K.extension(y^3 - x^2)
            sage: L(x).nth_root(3)^3
            x
            sage: L(x^9).nth_root(-27)^-27
            x^9

        """
        if n == 1:
            return self
        if n < 0:
            return (~self).nth_root(-n)
        if n == 0:
            if not self.is_one():
                raise ValueError("element is not an n-th power.")
            return self

        # reduce to the separable case
        if not self.parent().polynomial().gcd(self.parent().polynomial().derivative()).is_one():
            L,from_L,to_L = self.parent().separable_model(('t','w'))
            return from_L(to_L(self).nth_root(n))

        p = self.parent().characteristic()
        if p.divides(n) and self.parent().constant_base_field().is_perfect():
            return self.__pth_root().nth_root(n//p)

        raise NotImplementedError("nth_root() not implemented for this n")

    def is_nth_power(self, n):
        if n == 0:
            return self.is_one()
        if n == 1:
            return True
        if n < 0:
            return self.is_unit() and (~self).is_nth_power(-n)

        # reduce to the separable case
        if not self.parent().polynomial().gcd(self.parent().polynomial().derivative()).is_one():
            L,from_L,to_L = self.parent().separable_model(('t','w'))
            return to_L(self).is_nth_power(n)

        p = self.parent().characteristic()
        if p.divides(n) and self.parent().constant_base_field().is_perfect():
            return self.parent().derivation()(self).is_zero() and self.__pth_root().is_nth_power(n//p)

        raise NotImplementedError("nth_root() not implemented for this n")

    def __pth_root(self):
        r"""
        Helper method for :meth:`nth_root` which computes a `p`-th root if the
        characteristic is `p` and the constant base field is perfect.

        EXAMPLES::

            sage: K.<x> = FunctionField(GF(3))
            sage: R.<y> = K[]
            sage: L.<y> = K.extension(y^2 - x)
            sage: (y^3).nth_root(3) # indirect doctest
            y

        """
        if self.parent().degree() == 1:
            return self.parent()(self.element()[0].nth_root(self.parent().characteristic()))

        from function_field import RationalFunctionField
        if not isinstance(self.base_ring(), RationalFunctionField):
            raise NotImplementedError("only implemented for simple extensions of function fields.")
        # compute a representation of the generator y of the field in terms of
        # powers of y^p
        v = []
        yp = self.parent().gen()**self.parent().characteristic()
        x = self.parent().one()
        for i in range(self.parent().degree()):
            v += x.list()
            x *= yp
        import sage.matrix.matrix_space
        MS = sage.matrix.matrix_space.MatrixSpace(self.parent().base_ring(), self.parent().degree())
        M = MS(v)
        y = self.parent().base_ring().polynomial_ring()(M.solve_left(MS.column_space()([0,1]+[0]*(self.parent().degree()-2))).list())

        f = self.element()(y).map_coefficients(lambda c:c.nth_root(self.parent().characteristic()))
        return self.parent()(f)

    def list(self):
        r"""
        Return a list of coefficients of self, i.e., if self is an element of
        a function field `K[y]/(f(y))`, then return the coefficients of the
        reduced presentation as a polynomial in `K[y]`.

        EXAMPLES::

            sage: K.<x> = FunctionField(QQ); R.<y> = K[]
            sage: L.<y> = K.extension(y^2 - x*y + 4*x^3)
            sage: a = ~(2*y + 1/x); a
            (-x^2/(8*x^5 + x^2 + 1/2))*y + (2*x^3 + x)/(16*x^5 + 2*x^2 + 1)
            sage: a.list()
            [(2*x^3 + x)/(16*x^5 + 2*x^2 + 1), -x^2/(8*x^5 + x^2 + 1/2)]
            sage: (x*y).list()
            [0, x]
        """
        return self._x.padded_list(self.parent().degree())

    def is_nth_power(self, n):
        if n == 0:
            return self.is_one()
        if n == 1:
            return True
        if n < 0:
            return self.is_unit() and (~self).is_nth_power(-n)

        # reduce to the separable case
        if not self.parent().polynomial().gcd(self.parent().polynomial().derivative()).is_one():
            L,from_L,to_L = self.parent().separable_model(names=('t','w'))
            return from_L(to_L(self).is_nth_power(n))

        p = self.parent().characteristic()
        if p.divides(n) and self.parent().constant_base_field().is_perfect():
            return self.parent().derivation()(self).is_zero() and self.__pth_root().is_nth_power(n//p)

        raise NotImplementedError("nth_root() not implemented for this n")

    @cached_in_parent_method
    def nth_root(self, n):
        r"""
        Compute an ``n``-th root of this element in the function field.

        INPUT:

        - ``n`` -- an integer

        OUTPUT:

        Returns an element ``a`` in the function field such that this element
        equals `a^n`. Raises an error if no such element exists.

        ALGORITHM:

        If ``n`` is a power of the characteristic of the field and the constant
        base field is perfect, then this uses the algorithm described in
        Proposition 12 of [GiTr1996].

        .. SEEALSO::

            :meth:`is_nth_power`

        EXAMPLES::

            sage: K.<x> = FunctionField(GF(3))
            sage: R.<y> = K[]
            sage: L.<y> = K.extension(y^2 - x)
            sage: L(y^3).nth_root(3)
            y
            sage: L(y^9).nth_root(-9)
            1/x*y

        This also works for inseparable extensions::

            sage: K.<x> = FunctionField(GF(3))
            sage: R.<y> = K[]
            sage: L.<y> = K.extension(y^3 - x^2)
            sage: L(x).nth_root(3)^3
            x
            sage: L(x^9).nth_root(-27)^-27
            x^9

        """
        if n == 1:
            return self
        if n < 0:
            return (~self).nth_root(-n)
        if n == 0:
            if not self.is_one():
                raise ValueError("element is not an n-th power.")
            return self

        # reduce to the separable case
        if not self.parent().polynomial().gcd(self.parent().polynomial().derivative()).is_one():
            L,from_L,to_L = self.parent().separable_model(names=('t','w'))
            return from_L(to_L(self).nth_root(n))

        p = self.parent().characteristic()
        if p.divides(n) and self.parent().constant_base_field().is_perfect():
            return self.__pth_root().nth_root(n//p)

        raise NotImplementedError("nth_root() not implemented for this n")

    def __pth_root(self):
        r"""
        Helper method for :meth:`nth_root` which computes a `p`-th root if the
        characteristic is `p` and the constant base field is perfect.

        EXAMPLES::

            sage: K.<x> = FunctionField(GF(3))
            sage: R.<y> = K[]
            sage: L.<y> = K.extension(y^2 - x)
            sage: (y^3).nth_root(3) # indirect doctest
            y

        """
        from function_field import RationalFunctionField
        if not isinstance(self.base_ring(), RationalFunctionField):
            L, from_L, to_L = self.parent().simple_model()
            return from_L(to_L(self).pth_root())
        if self.parent().degree() == 1:
            return self.parent()(self.norm().pth_root())

        f = self.element()(self.parent()._pth_root_generator_rep()).map_coefficients(lambda c:c.nth_root(self.parent().characteristic()))
        return self.parent()(f)

cdef class FunctionFieldElement_rational(FunctionFieldElement):
    r"""
    Elements of a rational function field.

    EXAMPLES::

        sage: K.<t> = FunctionField(QQ); K
        Rational function field in t over Rational Field
    """
    def __init__(self, parent, x, reduce=True):
        r"""
        EXAMPLES::

            sage: FunctionField(QQ,'t').gen()^3
            t^3
        """
        FieldElement.__init__(self, parent)
        self._x = x
        if hasattr(x,'reduce'):
            x.reduce()

    def map_coefficients(self, f, ring=None):
        if hasattr(f,'codomain'):
            ring = f.codomain()
        from sage.categories.fields import Fields
        if f in Fields():
            ring = f
        if ring is None:
            ring = self.parent().constant_base_field()

        from constructor import FunctionField
        parent = FunctionField(ring, names=self.parent().variable_names())
        return parent._field(self.element().numerator().map_coefficients(f, ring), self.element().denominator().map_coefficients(f, ring))

    def is_constant(self):
        r"""
        Return True if self is a member of the constant base field.

        EXAMPLES::

            sage: K.<x> = FunctionField(QQ)
            sage: K(1).is_constant()
            True
            sage: K(0).is_constant()
            True
            sage: x.is_constant()
            False
            sage: (1/x).is_constant()
            False
        """
        return len(self.numerator().coeffs())<=1 and len(self.denominator().coeffs())<=1

    def element(self):
        r"""
        Return the underlying fraction field element that represents this element.

        EXAMPLES::

            sage: K.<t> = FunctionField(GF(7))
            sage: t.element()
            t
            sage: type(t.element())
            <type 'sage.rings.fraction_field_FpT.FpTElement'>

            sage: K.<t> = FunctionField(GF(131101))
            sage: t.element()
            t
            sage: type(t.element())
            <class 'sage.rings.fraction_field_element.FractionFieldElement_1poly_field'>
        """
        return self._x

    def list(self):
        r"""
        Return a list of coefficients of self, i.e., if self is an element of
        a function field K[y]/(f(y)), then return the coefficients of the
        reduced presentation as a polynomial in K[y].
        Since self is a member of a rational function field, this simply returns
        the list `[self]`.

        EXAMPLES::

            sage: K.<t> = FunctionField(QQ)
            sage: t.list()
            [t]
        """
        return [self]

    def _repr_(self):
        r"""
        EXAMPLES::

            sage: K.<t> = FunctionField(QQ)
            sage: t._repr_()
            't'
        """
        if hasattr(self._x,'reduce'):
            self._x.reduce()
        return repr(self._x)

    def __nonzero__(self):
        r"""
        EXAMPLES::

            sage: K.<t> = FunctionField(QQ)
            sage: bool(t)
            True
            sage: bool(K(0))
            False
            sage: bool(K(1))
            True
        """
        return not not self._x

    cdef int _cmp_c_impl(self, Element other) except -2:
        r"""
        EXAMPLES::

            sage: K.<t> = FunctionField(QQ)
            sage: cmp(t, 0)
            1
            sage: cmp(t, t^2)
            -1
        """
        cdef int c = cmp(type(self), type(other))
        if c: return c
        cdef FunctionFieldElement left = <FunctionFieldElement>self
        cdef FunctionFieldElement right = <FunctionFieldElement>other
        c = cmp(left._parent, right._parent)
        return c or cmp(left._x, right._x)

    cpdef ModuleElement _add_(self, ModuleElement right):
        r"""
        EXAMPLES::

            sage: K.<t> = FunctionField(QQ)
            sage: t + (3*t^3)                      # indirect doctest
            3*t^3 + t
        """
        cdef FunctionFieldElement res = self._new_c()
        res._x = self._x + (<FunctionFieldElement>right)._x
        return res

    cpdef ModuleElement _sub_(self, ModuleElement right):
        r"""
        EXAMPLES::

            sage: K.<t> = FunctionField(QQ)
            sage: t - (3*t^3)                      # indirect doctest
            -3*t^3 + t
        """
        cdef FunctionFieldElement res = self._new_c()
        res._x = self._x - (<FunctionFieldElement>right)._x
        return res

    cpdef RingElement _mul_(self, RingElement right):
        r"""
        EXAMPLES::

            sage: K.<t> = FunctionField(QQ)
            sage: (t+1) * (t^2-1)                  # indirect doctest
            t^3 + t^2 - t - 1
        """
        cdef FunctionFieldElement res = self._new_c()
        res._x = self._x * (<FunctionFieldElement>right)._x
        return res

    cpdef RingElement _div_(self, RingElement right):
        r"""
        EXAMPLES::

            sage: K.<t> = FunctionField(QQ)
            sage: (t+1) / (t^2 - 1)                # indirect doctest
            1/(t - 1)
        """
        cdef FunctionFieldElement res = self._new_c()
        res._parent = self._parent.fraction_field()
        res._x = self._x / (<FunctionFieldElement>right)._x
        return res

    def numerator(self):
        r"""
        EXAMPLES::

            sage: K.<t> = FunctionField(QQ)
            sage: f = (t+1) / (t^2 - 1/3); f
            (t + 1)/(t^2 - 1/3)
            sage: f.numerator()
            t + 1
        """
        return self._x.numerator()

    def denominator(self):
        r"""
        EXAMPLES::

            sage: K.<t> = FunctionField(QQ)
            sage: f = (t+1) / (t^2 - 1/3); f
            (t + 1)/(t^2 - 1/3)
            sage: f.denominator()
            t^2 - 1/3
        """
        return self._x.denominator()

    def valuation(self, v):
        r"""
        EXAMPLES::

            sage: K.<t> = FunctionField(QQ)
            sage: f = (t-1)^2 * (t+1) / (t^2 - 1/3)^3
            sage: f.valuation(t-1)
            2
            sage: f.valuation(t)
            0
            sage: f.valuation(t^2 - 1/3)
            -3
        """
        R = self._parent._ring
        return self._x.valuation(R(self._parent(v)._x))

    def is_square(self):
        r"""
        Returns whether self is a square.

        EXAMPLES::

            sage: K.<t> = FunctionField(QQ)
            sage: t.is_square()
            False
            sage: (t^2/4).is_square()
            True
            sage: f = 9 * (t+1)^6 / (t^2 - 2*t + 1); f.is_square()
            True

            sage: K.<t> = FunctionField(GF(5))
            sage: (-t^2).is_square()
            True
            sage: (-t^2).sqrt()
            2*t
        """
        return self._x.is_square()

    def sqrt(self, all=False):
        r"""
        Returns the square root of self.

        EXAMPLES::

            sage: K.<t> = FunctionField(QQ)
            sage: f = t^2 - 2 + 1/t^2; f.sqrt()
            (t^2 - 1)/t
            sage: f = t^2; f.sqrt(all=True)
            [t, -t]

        TESTS::

            sage: K(4/9).sqrt()
            2/3
            sage: K(0).sqrt(all=True)
            [0]
        """
        if all:
            return [self._parent(r) for r in self._x.sqrt(all=True)]
        else:
            return self._parent(self._x.sqrt())

    def factor(self):
        r"""
        Factor this rational function.

        EXAMPLES::

            sage: K.<t> = FunctionField(QQ)
            sage: f = (t+1) / (t^2 - 1/3)
            sage: f.factor()
            (t + 1) * (t^2 - 1/3)^-1
            sage: (7*f).factor()
            (7) * (t + 1) * (t^2 - 1/3)^-1
            sage: ((7*f).factor()).unit()
            7
            sage: (f^3).factor()
            (t + 1)^3 * (t^2 - 1/3)^-3
        """
        P = self.parent()
        F = self._x.factor()
        from sage.structure.factorization import Factorization
        return Factorization([(P(a),e) for a,e in F], unit=F.unit())

    def is_nth_power(self, n):
        r"""
        Return whether this element is an ``n``-th power in the rational
        function field.

        INPUT:

        - ``n`` -- an integer

        OUTPUT:

        Returns ``True`` if there is an element `a` in the function field such
        that this element equals `a^n`.

        ALGORITHM:

        If ``n`` is a power of the characteristic of the field and the constant
        base field is perfect, then this uses the algorithm described in Lemma
        3 of [GiTr1996].

        .. SEEALSO::

            :meth:`nth_root`

        EXAMPLES::

            sage: K.<x> = FunctionField(GF(3))
            sage: f = (x+1)/(x-1)
            sage: f.is_nth_power(1)
            True
            sage: f.is_nth_power(3)
            False
            sage: (f^3).is_nth_power(3)
            True
            sage: (f^9).is_nth_power(-9)
            True

        """
        if n == 1:
            return True
        if n < 0:
            return (~self).is_nth_power(-n)

        p = self.parent().characteristic()
        if n == p:
            return self.parent().derivation()(self).is_zero()
        if p.divides(n):
            return self.is_nth_power(p) and self.nth_root(p).is_nth_power(n//p)

        raise NotImplementedError("is_nth_power() not implemented for the given n")

    def nth_root(self, n):
        r"""
        Compute an ``n``-th root of this element in the function field.

        INPUT:

        - ``n`` -- an integer

        OUTPUT:

        Returns an element ``a`` in the rational function field such that this
        element equals `a^n`. Raises an error if no such element exists.

        ALGORITHM:

        If ``n`` is a power of the characteristic of the field and the constant
        base field is perfect, then this uses the algorithm described in
        Corllary 3 of [GiTr1996].

        .. SEEALSO::

            :meth:`is_nth_power`

        EXAMPLES::

            sage: K.<x> = FunctionField(GF(3))
            sage: f = (x+1)/(x+2)
            sage: f.nth_root(1)
            (x + 1)/(x + 2)
            sage: f.nth_root(3)
            Traceback (most recent call last):
            ...
            ValueError: element is not an n-th power.
            sage: (f^3).nth_root(3)
            (x + 1)/(x + 2)
            sage: (f^9).nth_root(-9)
            (x + 2)/(x + 1)

        """
        if n == 0:
            assert self.is_one() # self is 1 - otherwise it can't be an n-th power
            return self
        if n == 1:
            return self
        if n < 0:
            return (~self).nth_root(-n)

        p = self.parent().characteristic()
        if p.divides(n):
            if not self.is_nth_power(p):
                raise ValueError("element is not an n-th power.")
            return self.parent()(self.numerator().nth_root(p) / self.denominator().nth_root(p)).nth_root(n//p)

        raise NotImplementedError("nth_root() not implemented for this n.")

    def inverse_mod(self, I):
        r"""
        Return an inverse of self modulo the integral ideal `I`, if
        defined, i.e., if `I` and self together generate the unit
        ideal.

        EXAMPLES::

            sage: K.<x> = FunctionField(QQ)
            sage: O = K.maximal_order(); I = O.ideal(x^2+1)
            sage: t = O(x+1).inverse_mod(I); t
            -1/2*x + 1/2
            sage: (t*(x+1) - 1) in I
            True
        """
        assert  len(I.gens()) == 1
        f = I.gens()[0]._x
        assert f.denominator() == 1
        assert self._x.denominator() == 1
        return self.parent()(self._x.numerator().inverse_mod(f.numerator()))

    #@cached_in_parent_method
    def is_nth_power(self, n):
        r"""
        Return whether this element is an ``n``-th power in the rational
        function field.

        INPUT:

        - ``n`` -- an integer

        OUTPUT:

        Returns ``True`` if there is an element `a` in the function field such
        that this element equals `a^n`.

        ALGORITHM:

        If ``n`` is a power of the characteristic of the field and the constant
        base field is perfect, then this uses the algorithm described in Lemma
        3 of [GiTr1996].

        .. SEEALSO::

            :meth:`nth_root`

        EXAMPLES::

            sage: K.<x> = FunctionField(GF(3))
            sage: f = (x+1)/(x-1)
            sage: f.is_nth_power(1)
            True
            sage: f.is_nth_power(3)
            False
            sage: (f^3).is_nth_power(3)
            True
            sage: (f^9).is_nth_power(-9)
            True

        """
        if n == 1:
            return True
        if n < 0:
            return (~self).is_nth_power(-n)

        p = self.parent().characteristic()
        if n == p:
            return self.parent().derivation()(self).is_zero()
        if p.divides(n):
            return self.is_nth_power(p) and self.nth_root(p).is_nth_power(n//p)

        raise NotImplementedError("is_nth_power() not implemented for the given n")

    def nth_root(self, n):
        r"""
        Compute an ``n``-th root of this element in the function field.

        INPUT:

        - ``n`` -- an integer

        OUTPUT:

        Returns an element ``a`` in the rational function field such that this
        element equals `a^n`. Raises an error if no such element exists.

        ALGORITHM:

        If ``n`` is a power of the characteristic of the field and the constant
        base field is perfect, then this uses the algorithm described in
        Corllary 3 of [GiTr1996].

        .. SEEALSO::

            :meth:`is_nth_power`

        EXAMPLES::

            sage: K.<x> = FunctionField(GF(3))
            sage: f = (x+1)/(x+2)
            sage: f.nth_root(1)
            (x + 1)/(x + 2)
            sage: f.nth_root(3)
            Traceback (most recent call last):
            ...
            ValueError: element is not an n-th power.
            sage: (f^3).nth_root(3)
            (x + 1)/(x + 2)
            sage: (f^9).nth_root(-9)
            (x + 2)/(x + 1)

        """
        if n == 0:
            assert self.is_one() # self is 1 - otherwise it can't be an n-th power
            return self
        if n == 1:
            return self
        if n < 0:
            return (~self).nth_root(-n)
        p = self.parent().characteristic()
        if p.divides(n):
            if not self.is_nth_power(p):
                raise ValueError("element is not an n-th power.")
            return self.parent()(self.numerator().nth_root(p) / self.denominator().nth_root(p)).nth_root(n//p)

        raise NotImplementedError("nth_root() not implemented for this n.")

