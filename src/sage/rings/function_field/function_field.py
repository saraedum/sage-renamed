"""
Function Fields

AUTHORS:

- William Stein (2010): initial version

- Robert Bradshaw (2010-05-30): added is_finite()

- Julian Rueth (2011-06-08, 2011-09-14, 2014-06-23, 2014-06-24): fixed hom(), extension(); use @cached_method; added derivation(); added support for relative vector spaces

- Maarten Derickx (2011-09-11): added doctests

- Syed Ahmad Lavasani (2011-12-16): added genus(), is_RationalFunctionField()

- Simon King (2014-10-29): Use the same generator names for a function field
  extension and the underlying polynomial ring.

EXAMPLES:

We create an extension of a rational function fields, and do some
simple arithmetic in it::

    sage: K.<x> = FunctionField(GF(5^2,'a')); K
    Rational function field in x over Finite Field in a of size 5^2
    sage: R.<y> = K[]
    sage: L.<y> = K.extension(y^3 - (x^3 + 2*x*y + 1/x)); L
    Function field in y defined by y^3 + 3*x*y + (4*x^4 + 4)/x
    sage: y^2
    y^2
    sage: y^3
    2*x*y + (x^4 + 1)/x
    sage: a = 1/y; a
    (4*x/(4*x^4 + 4))*y^2 + 2*x^2/(4*x^4 + 4)
    sage: a * y
    1

We next make an extension of the above function field, illustrating
that arithmetic with a tower of 3 fields is fully supported::

    sage: S.<t> = L[]
    sage: M.<t> = L.extension(t^2 - x*y)
    sage: M
    Function field in t defined by t^2 + 4*x*y
    sage: t^2
    x*y
    sage: 1/t
    ((1/(x^4 + 1))*y^2 + 2*x/(4*x^4 + 4))*t
    sage: M.base_field()
    Function field in y defined by y^3 + 3*x*y + (4*x^4 + 4)/x
    sage: M.base_field().base_field()
    Rational function field in x over Finite Field in a of size 5^2

TESTS::

    sage: TestSuite(K).run()
    sage: TestSuite(L).run()  # long time (8s on sage.math, 2012)
    sage: TestSuite(M).run()  # long time (52s on sage.math, 2012)

The following two test suites do not pass ``_test_elements`` yet since
``R.an_element()`` has a ``_test_category`` method wich it should not have.
It is not the fault of the function field code so this will
be fixed in another ticket::

    sage: TestSuite(R).run(skip = '_test_elements')
    sage: TestSuite(S).run(skip = '_test_elements')
"""
#*****************************************************************************
#       Copyright (C) 2010 William Stein <wstein@gmail.com>
#       Copyright (C) 2010 Robert Bradshaw <robertwb@math.washington.edu>
#       Copyright (C) 2011-2014 Julian Rueth <julian.rueth@gmail.com>
#       Copyright (C) 2011 Maarten Derickx <m.derickx.student@gmail.com>
#
#  Distributed under the terms of the GNU General Public License (GPL)
#  as published by the Free Software Foundation; either version 2 of
#  the License, or (at your option) any later version.
#                  http://www.gnu.org/licenses/
#*****************************************************************************

from sage.rings.ring import Field
from function_field_element import FunctionFieldElement, FunctionFieldElement_rational, FunctionFieldElement_polymod

from sage.misc.cachefunc import cached_method

#is needed for genus computation
from sage.rings.polynomial.polynomial_ring_constructor import PolynomialRing
from sage.interfaces.all import singular

from sage.categories.function_fields import FunctionFields
CAT = FunctionFields()

def is_FunctionField(x):
    """
    Return True if ``x`` is of function field type.

    EXAMPLES::

        sage: from sage.rings.function_field.function_field import is_FunctionField
        sage: is_FunctionField(QQ)
        False
        sage: is_FunctionField(FunctionField(QQ,'t'))
        True
    """
    if isinstance(x, FunctionField): return True
    return x in FunctionFields()

class FunctionField(Field):
    """
    The abstract base class for all function fields.

    EXAMPLES::

        sage: K.<x> = FunctionField(QQ)
        sage: isinstance(K, sage.rings.function_field.function_field.FunctionField)
        True
    """
    def is_perfect(self):
        r"""
        Return whether this field is perfect, i.e., its characteristic is `p=0`
        or every element has a `p`-th root.

        EXAMPLES::

            sage: FunctionField(QQ, 'x').is_perfect()
            True
            sage: FunctionField(GF(2), 'x').is_perfect()
            False

        """
        return self.characteristic() == 0

    @cached_method
    def _pth_root_generator_rep(self):
        # compute a representation of the generator y of the field in terms of
        # powers of y^p
        v = []
        yp = self.gen()**self.characteristic()
        x = self.one()
        for i in range(self.degree()):
            v += x.list()
            x *= yp
        import sage.matrix.matrix_space
        MS = sage.matrix.matrix_space.MatrixSpace(self.base_ring(), self.degree())
        M = MS(v)
        return self.base_ring().polynomial_ring()(M.solve_left(MS.column_space()([0,1]+[0]*(self.degree()-2))).list())

    def _intermediate_fields(self, base):
        r"""
        Return the fields between self and base including both fields themselves.

        EXAMPLES::

            sage: K.<x> = FunctionField(QQ); R.<y> = K[]
            sage: L.<y> = K.extension(y^2-x); RR.<z> = L[]
            sage: M.<z> = L.extension(z^2-y)
            sage: K._intermediate_fields(K)
            [Rational function field in x over Rational Field]
            sage: L._intermediate_fields(K)
            [Function field in y defined by y^2 - x, Rational function field in x over Rational Field]
            sage: M._intermediate_fields(K)
            [Function field in z defined by z^2 - y, Function field in y defined by y^2 - x, Rational function field in x over Rational Field]
            sage: K._intermediate_fields(M)
            Traceback (most recent call last):
            ...
            ValueError: Function field in z defined by z^2 - y does not qualify as a subfield of Rational function field in x over Rational Field
        """
        fields = [self]
        while fields[-1] is not base:
            fields+=[fields[-1].base_ring()]
            if fields[-1] is fields[-2]:
                raise ValueError("%s does not qualify as a subfield of %s"%(base,self))
        return fields

    def some_elements(self):
         """
         Return a list of elements in the function field.

         EXAMPLES::

            sage: K.<x> = FunctionField(QQ)
            sage: elements = K.some_elements()
            sage: elements # random output
            [(x - 3/2)/(x^2 - 12/5*x + 1/18)]
            sage: False in [e in K for e in elements]
            False
         """
         return [self.random_element(), self.random_element(), self.random_element()]

    def characteristic(self):
        """
        Return the characteristic of this function field.

        EXAMPLES::

            sage: K.<x> = FunctionField(QQ)
            sage: K.characteristic()
            0
            sage: K.<x> = FunctionField(GF(7))
            sage: K.characteristic()
            7
            sage: R.<y> = K[]
            sage: L.<y> = K.extension(y^2-x)
            sage: L.characteristic()
            7
        """
        return self.constant_base_field().characteristic()

    def is_finite(self):
        """
        Return whether this function field is finite, which it is not.

        EXAMPLES::

            sage: R.<t> = FunctionField(QQ)
            sage: R.is_finite()
            False
            sage: R.<t> = FunctionField(GF(7))
            sage: R.is_finite()
            False
        """
        return False

    def extension(self, f, names=None):
        """
        Create an extension L = K[y]/(f(y)) of a function field,
        defined by a univariate polynomial in one variable over this
        function field K.

        INPUT:

            - ``f`` -- a univariate polynomial over self
            - ``names`` -- None or string or length-1 tuple

        OUTPUT:

        a function field

        EXAMPLES::

            sage: K.<x> = FunctionField(QQ); R.<y> = K[]
            sage: K.extension(y^5 - x^3 - 3*x + x*y)
            Function field in y defined by y^5 + x*y - x^3 - 3*x

        A nonintegral defining polynomial::

            sage: K.<t> = FunctionField(QQ); R.<y> = K[]
            sage: K.extension(y^3 + (1/t)*y + t^3/(t+1))
            Function field in y defined by y^3 + 1/t*y + t^3/(t + 1)

        The defining polynomial need not be monic or integral::

            sage: K.extension(t*y^3 + (1/t)*y + t^3/(t+1))
            Function field in y defined by t*y^3 + 1/t*y + t^3/(t + 1)
        """
        from constructor import FunctionField_polymod as FunctionField_polymod_Constructor
        return FunctionField_polymod_Constructor(f, names)

    def order_with_basis(self, basis, check=True):
        """
        Return the order with given basis over the maximal order of
        the base field.

        INPUT:

           - ``basis`` -- a list of elements of self
           - ``check`` -- bool (default: True); if True, check that
             the basis is really linearly independent and that the
             module it spans is closed under multiplication, and
             contains the identity element.

        OUTPUT:

        an order in this function field

        EXAMPLES::

            sage: K.<x> = FunctionField(QQ); R.<y> = K[]; L.<y> = K.extension(y^3 + x^3 + 4*x + 1)
            sage: O = L.order_with_basis([1, y, y^2]); O
            Order in Function field in y defined by y^3 + x^3 + 4*x + 1
            sage: O.basis()
            (1, y, y^2)

        Note that 1 does not need to be an element of the basis, as long it is in the module spanned by it::

            sage: O = L.order_with_basis([1+y, y, y^2]); O
            Order in Function field in y defined by y^3 + x^3 + 4*x + 1
            sage: O.basis()
            (y + 1, y, y^2)

        The following error is raised when the module spanned by the basis is not closed under multiplication::

            sage: O = L.order_with_basis([1, x^2 + x*y, (2/3)*y^2]); O
            Traceback (most recent call last):
            ...
            ValueError: The module generated by basis [1, x*y + x^2, 2/3*y^2] must be closed under multiplication

        and this happens when the identity is not in the module spanned by the basis::

            sage: O = L.order_with_basis([x, x^2 + x*y, (2/3)*y^2])
            Traceback (most recent call last):
            ...
            ValueError: The identity element must be in the module spanned by basis [x, x*y + x^2, 2/3*y^2]
        """
        from function_field_order import FunctionFieldOrder_basis
        return FunctionFieldOrder_basis([self(a) for a in basis], check=check)

    def order(self, x, check=True):
        """
        Return the order in this function field generated over the
        maximal order by x or the elements of x if x is a list.

        INPUT:

           - ``x`` -- element of self, or a list of elements of self
           - ``check`` -- bool (default: True); if True, check that
             x really generates an order

        EXAMPLES::

            sage: K.<x> = FunctionField(QQ); R.<y> = K[]; L.<y> = K.extension(y^3 + x^3 + 4*x + 1)
            sage: O = L.order(y); O
            Order in Function field in y defined by y^3 + x^3 + 4*x + 1
            sage: O.basis()
            (1, y, y^2)

            sage: Z = K.order(x); Z
            Order in Rational function field in x over Rational Field
            sage: Z.basis()
            (1,)

        Orders with multiple generators, not yet supported::

            sage: Z = K.order([x,x^2]); Z
            Traceback (most recent call last):
            ...
            NotImplementedError
        """
        if not isinstance(x, (list, tuple)):
            x = [x]
        if len(x) == 1:
            g = x[0]
            basis = [self(1)]
            for i in range(self.degree()-1):
                basis.append(basis[-1]*g)
        else:
            raise NotImplementedError
        return self.order_with_basis(basis, check=check)

    def _coerce_map_from_(self, R):
        """
        Return True if there is a coerce map from R to self.

        EXAMPLES::

            sage: K.<x> = FunctionField(QQ); R.<y> = K[]; L.<y> = K.extension(y^3 + x^3 + 4*x + 1)
            sage: L.equation_order()
            Order in Function field in y defined by y^3 + x^3 + 4*x + 1
            sage: L._coerce_map_from_(L.equation_order())
            True
            sage: L._coerce_map_from_(GF(7))
            False
        """
        from function_field_order import FunctionFieldOrder
        if isinstance(R, FunctionFieldOrder) and R.fraction_field() == self:
            return True
        return False

    def _intermediate_fields(self, base):
        r"""
        Return the fields which lie in between ``base`` and this field in the
        tower of function fields.

        INPUT:

        - ``base`` -- a function field, either this field or a field from which
          this field has been created as an extension

        OUTPUT:

        A list of fields. The first entry is ``base``, the last entry is this field.

        EXAMPLES::

            sage: K.<x> = FunctionField(QQ)
            sage: K._intermediate_fields(K)
            [Rational function field in x over Rational Field]

            sage: R.<y> = K[]
            sage: L.<y> = K.extension(y^2-x)
            sage: L._intermediate_fields(K)
            [Function field in y defined by y^2 - x, Rational function field in x over Rational Field]

            sage: R.<z> = L[]
            sage: M.<z> = L.extension(z^2-y)
            sage: M._intermediate_fields(L)
            [Function field in z defined by z^2 - y, Function field in y defined by y^2 - x]
            sage: M._intermediate_fields(K)
            [Function field in z defined by z^2 - y, Function field in y defined by y^2 - x, Rational function field in x over Rational Field]

        TESTS::

            sage: K._intermediate_fields(M)
            Traceback (most recent call last):
            ...
            ValueError: field has not been constructed as a finite extension of base
            sage: K._intermediate_fields(QQ)
            Traceback (most recent call last):
            ...
            TypeError: base must be a function field

        """
        if not is_FunctionField(base):
            raise TypeError("base must be a function field")

        ret = [self]
        while ret[-1] is not base:
            ret.append(ret[-1].base_field())
            if ret[-1] is ret[-2]:
                raise ValueError("field has not been constructed as a finite extension of base")
        return ret

class FunctionField_polymod(FunctionField):
    """
    A function field defined by a univariate polynomial, as an
    extension of the base field.

    EXAMPLES:

    We make a function field defined by a degree 5 polynomial over the
    rational function field over the rational numbers::

        sage: K.<x> = FunctionField(QQ)
        sage: R.<y> = K[]
        sage: L.<y> = K.extension(y^5 - (x^3 + 2*x*y + 1/x)); L
        Function field in y defined by y^5 - 2*x*y + (-x^4 - 1)/x

    We next make a function field over the above nontrivial function
    field L::

        sage: S.<z> = L[]
        sage: M.<z> = L.extension(z^2 + y*z + y); M
        Function field in z defined by z^2 + y*z + y
        sage: 1/z
        ((x/(-x^4 - 1))*y^4 - 2*x^2/(-x^4 - 1))*z - 1
        sage: z * (1/z)
        1

    We drill down the tower of function fields::

        sage: M.base_field()
        Function field in y defined by y^5 - 2*x*y + (-x^4 - 1)/x
        sage: M.base_field().base_field()
        Rational function field in x over Rational Field
        sage: M.base_field().base_field().constant_field()
        Rational Field
        sage: M.constant_base_field()
        Rational Field

    .. WARNING::

        It is not checked if the polynomial used to define this function field is irreducible
        Hence it is not guaranteed that this object really is a field!
        This is illustrated below.

    ::

        sage: K.<x>=FunctionField(QQ)
        sage: R.<y> = K[]
        sage: L.<y>=K.extension(x^2-y^2)
        sage: (y-x)*(y+x)
        0
        sage: 1/(y-x)
        1
        sage: y-x==0; y+x==0
        False
        False
    """
    def __init__(self, polynomial, names,
            element_class = FunctionFieldElement_polymod,
            category=CAT):
        """
        Create a function field defined as an extension of another
        function field by adjoining a root of a univariate polynomial.

        INPUT:

            - ``polynomial`` -- a univariate polynomial over a function field
            - ``names`` -- variable names (as a tuple of length 1 or string)
            - ``category`` -- a category (defaults to category of function fields)

        EXAMPLES:

        We create an extension of a function field::

            sage: K.<x> = FunctionField(QQ); R.<y> = K[]
            sage: L = K.extension(y^5 - x^3 - 3*x + x*y); L
            Function field in y defined by y^5 + x*y - x^3 - 3*x

        Note the type::

            sage: type(L)
            <class 'sage.rings.function_field.function_field.FunctionField_polymod_with_category'>

        We can set the variable name, which doesn't have to be y::

            sage: L.<w> = K.extension(y^5 - x^3 - 3*x + x*y); L
            Function field in w defined by w^5 + x*w - x^3 - 3*x

        TESTS:

        Test that :trac:`17033` is fixed::

            sage: K.<t> = FunctionField(QQ)
            sage: R.<x> = QQ[]
            sage: M.<z> = K.extension(x^7-x-t)
            sage: M(x)
            z
            sage: M('z')
            z
            sage: M('x')
            Traceback (most recent call last):
            ...
            TypeError: unable to convert string

        """
        from sage.rings.polynomial.polynomial_element import is_Polynomial
        if polynomial.parent().ngens()>1 or not is_Polynomial(polynomial):
            raise TypeError("polynomial must be univariate a polynomial")
        if names is None:
            names = (polynomial.variable_name(), )
        elif names != polynomial.variable_name():
            polynomial = polynomial.change_variable_name(names)
        if polynomial.degree() <= 0:
            raise ValueError("polynomial must have positive degree")
        base_field = polynomial.base_ring()
        if not isinstance(base_field, FunctionField):
            raise TypeError("polynomial must be over a FunctionField")
        self._element_class = element_class
        self._element_init_pass_parent = False
        self._base_field = base_field
        self._polynomial = polynomial

        Field.__init__(self, base_field,
                                names=names, category = category)

        self._ring = self._polynomial.parent()
        self._populate_coercion_lists_(coerce_list=[base_field, self._ring])
        self._gen = self(self._ring.gen())

    def rational_function_field(self):
        """
        Return the rational function field underlying self.

        EXAMPLES::

            sage: K.<x> = FunctionField(QQ); R.<y> = K[]
            sage: L.<y> = K.extension(y^2-x); RR.<z> = L[]
            sage: M.<z> = L.extension(z^2-y)
            sage: K.rational_function_field()
            Rational function field in x over Rational Field
            sage: L.rational_function_field()
            Rational function field in x over Rational Field
            sage: M.rational_function_field()
            Rational function field in x over Rational Field
        """
        return self.base_field().rational_function_field()

    def __reduce__(self):
        """
        Returns the arguments which were used to create this instance. The rationale for this is explained in the documentation of ``UniqueRepresentation``.

        EXAMPLES::

            sage: K.<x> = FunctionField(QQ); R.<y> = K[]
            sage: L = K.extension(y^2-x)
            sage: clazz,args = L.__reduce__()
            sage: clazz(*args)
            Function field in y defined by y^2 - x
        """
        from constructor import FunctionField_polymod as FunctionField_polymod_Constructor
        return  FunctionField_polymod_Constructor, (self._polynomial, self._names)

    def __hash__(self):
        """
        Return hash of this function field.

        The hash value is equal to the hash of the defining polynomial.

        EXAMPLES::

            sage: K.<x> = FunctionField(QQ); R.<y> = K[]
            sage: L = K.extension(y^5 - x^3 - 3*x + x*y)
            sage: hash(L) == hash(L.polynomial())
            True

        """
        return hash(self.polynomial())

    def _cache_key(self):
        return self.base(), self.polynomial(), self.names()

    @cached_method
    def monic_integral_model(self, names):
        """
        Return a function field isomorphic to self, but with defining
        polynomial that is monic and integral over the base field.

        INPUT:

            - ``names`` -- name of the generator of the new field this function constructs

        EXAMPLES::

            sage: K.<x> = FunctionField(QQ); R.<y> = K[]
            sage: L.<y> = K.extension(x^2*y^5 - 1/x); L
            Function field in y defined by x^2*y^5 - 1/x
            sage: A, from_A, to_A = L.monic_integral_model('z')
            sage: A
            Function field in z defined by z^5 - x^12
            sage: from_A
            Function Field morphism:
              From: Function field in z defined by z^5 - x^12
              To:   Function field in y defined by x^2*y^5 - 1/x
              Defn: z |--> x^3*y
            sage: to_A
            Function Field morphism:
              From: Function field in y defined by x^2*y^5 - 1/x
              To:   Function field in z defined by z^5 - x^12
              Defn: y |--> 1/x^3*z
            sage: to_A(y)
            1/x^3*z
            sage: from_A(to_A(y))
            y
            sage: from_A(to_A(1/y))
            x^3*y^4
            sage: from_A(to_A(1/y)) == 1/y
            True
        """
        g, d = self._make_monic_integral(self.polynomial())
        R = self.base_field()
        K = R.extension(g, names=names)
        to_K = self.hom(K.gen() / d)
        from_K = K.hom(self.gen() * d)
        return K, from_K, to_K

    def _make_monic_integral(self, f):
        r"""
        Let y be a root of ``f``.  This function returns a monic
        integral polynomial g and an element d of the base field such
        that g(y*d)=0.

        EXAMPLES::

            sage: K.<x> = FunctionField(QQ); R.<y> = K[];
            sage: L.<y> = K.extension(x^2*y^5 - 1/x)
            sage: g, d = L._make_monic_integral(L.polynomial()); g,d
            (y^5 - x^12, x^3)
            sage: (y*d).is_integral()
            True
            sage: g.is_monic()
            True
            sage: g(y*d)
            0
        """
        R = f.base_ring()
        if not isinstance(R, RationalFunctionField):
            raise NotImplementedError

        # make f monic
        n = f.degree()
        c = f.leading_coefficient()
        if c != 1:
            f = f / c

        # find lcm of denominators
        from sage.rings.arith import lcm
        # would be good to replace this by minimal...
        d = lcm([b.denominator() for b in f.list() if b])
        if d != 1:
            x = f.parent().gen()
            g = (d**n) * f(x/d)
        else:
            g = f
        return g, d

    def constant_field(self):
        """
        Return the algebraic closure of the constant field of the base
        field in this function field.

        EXAMPLES::

            sage: K.<x> = FunctionField(QQ); R.<y> = K[]
            sage: L.<y> = K.extension(y^5 - (x^3 + 2*x*y + 1/x))
            sage: L.constant_field()
            Traceback (most recent call last):
            ...
            NotImplementedError
        """
        raise NotImplementedError

    def constant_base_field(self):
        """
        Return the constant field of the base rational function field.

        EXAMPLES::

            sage: K.<x> = FunctionField(QQ); R.<y> = K[]
            sage: L.<y> = K.extension(y^5 - (x^3 + 2*x*y + 1/x)); L
            Function field in y defined by y^5 - 2*x*y + (-x^4 - 1)/x
            sage: L.constant_base_field()
            Rational Field
            sage: S.<z> = L[]
            sage: M.<z> = L.extension(z^2 - y)
            sage: M.constant_base_field()
            Rational Field
        """
        return self.base_field().constant_base_field()

    @cached_method(key=lambda self, base: self.base_field() if base is None else base)
    def degree(self, base=None):
        """
        Return the degree of this function field over the function field
        ``base``.

        INPUT:

        - ``base`` -- a function field or ``None`` (default: ``None``), a
          function field from which this field has been constructed as a finite
          extension.

        EXAMPLES::

            sage: K.<x> = FunctionField(QQ)
            sage: R.<y> = K[]
            sage: L.<y> = K.extension(y^5 - (x^3 + 2*x*y + 1/x)); L
            Function field in y defined by y^5 - 2*x*y + (-x^4 - 1)/x
            sage: L.degree()
            5
            sage: L.degree(L)
            1

            sage: R.<z> = L[]
            sage: M.<z> = L.extension(z^2 - y)
            sage: M.degree(L)
            2
            sage: M.degree(K)
            10

        TESTS::

            sage: L.degree(M)
            Traceback (most recent call last):
            ...
            ValueError: base must be None or the rational function field

        """
        if base is None:
            base = self.base_field()
        if base is self:
            from sage.rings.integer_ring import ZZ
            return ZZ(1)
        return self._polynomial.degree() * self.base_field().degree(base)

    def _repr_(self):
        """
        Return string representation of this function field.

        EXAMPLES::

            sage: K.<x> = FunctionField(QQ); R.<y> = K[]
            sage: L.<y> = K.extension(y^5 - (x^3 + 2*x*y + 1/x))
            sage: L._repr_()
            'Function field in y defined by y^5 - 2*x*y + (-x^4 - 1)/x'
        """
        return "Function field in %s defined by %s"%(self.variable_name(), self._polynomial)

    def base_field(self):
        """
        Return the base field of this function field.  This function
        field is presented as L = K[y]/(f(y)), and the base field is
        by definition the field K.

        EXAMPLES::

            sage: K.<x> = FunctionField(QQ); R.<y> = K[]
            sage: L.<y> = K.extension(y^5 - (x^3 + 2*x*y + 1/x))
            sage: L.base_field()
            Rational function field in x over Rational Field
        """
        return self._base_field

    def random_element(self, *args, **kwds):
        """
        Create a random element of this function field.  Parameters
        are passed onto the random_element method of the base_field.

        EXAMPLES::

            sage: K.<x> = FunctionField(QQ); R.<y> = K[]
            sage: L.<y> = K.extension(y^2 - (x^2 + x))
            sage: L.random_element() # random
            ((x^2 - x + 2/3)/(x^2 + 1/3*x - 1))*y^2 + ((-1/4*x^2 + 1/2*x - 1)/(-5/2*x + 2/3))*y + (-1/2*x^2 - 4)/(-12*x^2 + 1/2*x - 1/95)
        """
        return self(self._ring.random_element(degree=self.degree(), *args, **kwds))

    def polynomial(self):
        """
        Return the univariate polynomial that defines this function
        field, i.e., the polynomial f(y) so that this function field
        is of the form K[y]/(f(y)).

        EXAMPLES::

            sage: K.<x> = FunctionField(QQ); R.<y> = K[]
            sage: L.<y> = K.extension(y^5 - (x^3 + 2*x*y + 1/x))
            sage: L.polynomial()
            y^5 - 2*x*y + (-x^4 - 1)/x
        """
        return self._polynomial

    def polynomial_ring(self):
        """
        Return the polynomial ring used to represent elements of this
        function field.  If we view this function field as being presented
        as K[y]/(f(y)), then this function returns the ring K[y].

        EXAMPLES::

            sage: K.<x> = FunctionField(QQ); R.<y> = K[]
            sage: L.<y> = K.extension(y^5 - (x^3 + 2*x*y + 1/x))
            sage: L.polynomial_ring()
            Univariate Polynomial Ring in y over Rational function field in x over Rational Field
        """
        return self._ring

    @cached_method(key=lambda self, base: self.base_field() if base is None else base)
    def vector_space(self, base=None):
        """
        Return a vector space `V` and isomorphisms from this field to `V` and
        from `V` to this field.

        This function allows us to identify the elements of this field with
        elements of a vector space over the base field, which is useful for
        representation and arithmetic with orders, ideals, etc.

        INPUT:

        - ``base`` -- a function field or ``None`` (default: ``None``), the
          returned vector space is over ``base`` which defaults to the base
          field of this function field.

        OUTPUT:

        - ``V`` -- a vector space over base field
        - ``from_V`` -- an isomorphism from V to this field
        - ``to_V`` -- an isomorphism from this field to V

        EXAMPLES:

        We define a function field::

            sage: K.<x> = FunctionField(QQ); R.<y> = K[]
            sage: L.<y> = K.extension(y^5 - (x^3 + 2*x*y + 1/x)); L
            Function field in y defined by y^5 - 2*x*y + (-x^4 - 1)/x

        We get the vector spaces, and maps back and forth::

            sage: V, from_V, to_V = L.vector_space()
            sage: V
            Vector space of dimension 5 over Rational function field in x over Rational Field
            sage: from_V
            Isomorphism morphism:
              From: Vector space of dimension 5 over Rational function field in x over Rational Field
              To:   Function field in y defined by y^5 - 2*x*y + (-x^4 - 1)/x
            sage: to_V
            Isomorphism morphism:
              From: Function field in y defined by y^5 - 2*x*y + (-x^4 - 1)/x
              To:   Vector space of dimension 5 over Rational function field in x over Rational Field

        We convert an element of the vector space back to the function field::

            sage: from_V(V.1)
            y

        We define an interesting element of the function field::

            sage: a = 1/L.0; a
            (-x/(-x^4 - 1))*y^4 + 2*x^2/(-x^4 - 1)

        We convert it to the vector space, and get a vector over the base field::

            sage: to_V(a)
            (2*x^2/(-x^4 - 1), 0, 0, 0, -x/(-x^4 - 1))

        We convert to and back, and get the same element::

            sage: from_V(to_V(a)) == a
            True

        In the other direction::

            sage: v = x*V.0 + (1/x)*V.1
            sage: to_V(from_V(v)) == v
            True

        And we show how it works over an extension of an extension field::

            sage: R2.<z> = L[]; M.<z> = L.extension(z^2 -y)
            sage: M.vector_space()
            (Vector space of dimension 2 over Function field in y defined by y^5 - 2*x*y + (-x^4 - 1)/x, Isomorphism morphism:
              From: Vector space of dimension 2 over Function field in y defined by y^5 - 2*x*y + (-x^4 - 1)/x
              To:   Function field in z defined by z^2 - y, Isomorphism morphism:
              From: Function field in z defined by z^2 - y
              To:   Vector space of dimension 2 over Function field in y defined by y^5 - 2*x*y + (-x^4 - 1)/x)

        We can also get the vector space of ``M`` over ``K``::

            sage: M.vector_space(K)
            (Vector space of dimension 10 over Rational function field in x over Rational Field, Isomorphism morphism:
              From: Vector space of dimension 10 over Rational function field in x over Rational Field
              To:   Function field in z defined by z^2 - y, Isomorphism morphism:
              From: Function field in z defined by z^2 - y
              To:   Vector space of dimension 10 over Rational function field in x over Rational Field)

        """
        from maps import MapVectorSpaceToFunctionField, MapFunctionFieldToVectorSpace
        if base is None:
            base = self.base_field()
        degree = self.degree(base)
        V = base**degree;
        from_V = MapVectorSpaceToFunctionField(V, self)
        to_V   = MapFunctionFieldToVectorSpace(self, V)
        return (V, from_V, to_V)

    def maximal_order(self):
        """
        Return the maximal_order of self.  If we view self as L =
        K[y]/(f(y)), then this is the ring of elements of L that are
        integral over K.

        EXAMPLES:

        This is not yet implemented...::

            sage: K.<x> = FunctionField(QQ); R.<y> = K[]
            sage: L.<y> = K.extension(y^5 - (x^3 + 2*x*y + 1/x))
            sage: L.maximal_order()
            Traceback (most recent call last):
            ...
            NotImplementedError
        """
        raise NotImplementedError

    def _element_constructor_(self, x):
        r"""
        Make ``x`` into an element of this function field, possibly not canonically.

        INPUT:

            - ``x`` -- the element

        OUTPUT:

        ``x``, as an element of this function field

        TESTS::

            sage: K.<x> = FunctionField(QQ); R.<y> = K[]
            sage: L.<y> = K.extension(y^5 - (x^3 + 2*x*y + 1/x))
            sage: L._element_constructor_(L.polynomial_ring().gen())
            y
        """
        if isinstance(x, FunctionFieldElement):
            return FunctionFieldElement_polymod(self, self._ring(x.element()))
        return FunctionFieldElement_polymod(self, self._ring(x))

    def gen(self, n=0):
        """
        Return the ``n``-th generator of this function field. By default ``n`` is 0; any other
        value of ``n`` leads to an error. The generator is the class of y, if we view
        self as being presented as K[y]/(f(y)).

        EXAMPLES::

            sage: K.<x> = FunctionField(QQ); R.<y> = K[]
            sage: L.<y> = K.extension(y^5 - (x^3 + 2*x*y + 1/x))
            sage: L.gen()
            y
            sage: L.gen(1)
            Traceback (most recent call last):
            ...
            IndexError: Only one generator.
        """
        if n != 0: raise IndexError("Only one generator.")
        return self._gen

    def ngens(self):
        """
        Return the number of generators of this function field over
        its base field.  This is by definition 1.

        EXAMPLES::

            sage: K.<x> = FunctionField(QQ); R.<y> = K[]
            sage: L.<y> = K.extension(y^5 - (x^3 + 2*x*y + 1/x))
            sage: L.ngens()
            1
        """
        return 1

    def equation_order(self):
        """
        If we view self as being presented as K[y]/(f(y)), then this
        function returns the order generated by the class of y.  If f
        is not monic, then :meth:`_make_monic_integral` is called, and instead we
        get the order generated by some integral multiple of a root of f.

        EXAMPLES::

            sage: K.<x> = FunctionField(QQ); R.<y> = K[]
            sage: L.<y> = K.extension(y^5 - (x^3 + 2*x*y + 1/x))
            sage: O = L.equation_order()
            sage: O.basis()
            (1, x*y, x^2*y^2, x^3*y^3, x^4*y^4)

        We try an example, in which the defining polynomial is not
        monic and is not integral::

            sage: K.<x> = FunctionField(QQ); R.<y> = K[]
            sage: L.<y> = K.extension(x^2*y^5 - 1/x); L
            Function field in y defined by x^2*y^5 - 1/x
            sage: O = L.equation_order()
            sage: O.basis()
            (1, x^3*y, x^6*y^2, x^9*y^3, x^12*y^4)
        """
        d = self._make_monic_integral(self.polynomial())[1]
        return self.order(d*self.gen(), check=False)

    def hom(self, im_gens, base_morphism=None):
        """
        Create a homomorphism from self to another function field.

        INPUT:

           - ``im_gens`` -- a list of images of the generators of self
             and of successive base rings.

           - ``base_morphism`` -- (default: None) a homomorphism of
             the base ring, after the im_gens are used.  Thus if
             im_gens has length 2, then base_morphism should be a morphism
             from self.base_ring().base_ring().

        EXAMPLES:

        We create a rational function field, and a quadratic extension of it::

            sage: K.<x> = FunctionField(QQ); R.<y> = K[]
            sage: L.<y> = K.extension(y^2 - x^3 - 1)

        We make the field automorphism that sends y to -y::

            sage: f = L.hom(-y); f
            Function Field endomorphism of Function field in y defined by y^2 - x^3 - 1
              Defn: y |--> -y

        Evaluation works::

            sage: f(y*x - 1/x)
            -x*y - 1/x

        We try to define an invalid morphism::

            sage: f = L.hom(y+1)
            Traceback (most recent call last):
            ...
            ValueError: invalid morphism

        We make a morphism of the base rational function field::

            sage: phi = K.hom(x+1); phi
            Function Field endomorphism of Rational function field in x over Rational Field
              Defn: x |--> x + 1
            sage: phi(x^3 - 3)
            x^3 + 3*x^2 + 3*x - 2
            sage: (x+1)^3-3
            x^3 + 3*x^2 + 3*x - 2

        We make a morphism by specifying where the generators and the
        base generators go::

            sage: L.hom([-y, x])
            Function Field endomorphism of Function field in y defined by y^2 - x^3 - 1
              Defn: y |--> -y
                    x |--> x

        The usage of the keyword base_morphism is not implemented yet::

            sage: L.hom([-y, x-1], base_morphism=phi)
            Traceback (most recent call last):
            ...
            NotImplementedError: Function field homorphisms with optional argument base_morphism are not implemented yet. Please specify the images of the generators of the base fields manually.

        We make another extension of a rational function field::

            sage: K2.<t> = FunctionField(QQ); R2.<w> = K2[]
            sage: L2.<w> = K2.extension((4*w)^2 - (t+1)^3 - 1)

        We define a morphism, by giving the images of generators::

            sage: f = L.hom([4*w, t+1]); f
            Function Field morphism:
              From: Function field in y defined by y^2 - x^3 - 1
              To:   Function field in w defined by 16*w^2 - t^3 - 3*t^2 - 3*t - 2
              Defn: y |--> 4*w
                    x |--> t + 1

        Evaluation works, as expected::

            sage: f(y+x)
            4*w + t + 1
            sage: f(x*y + x/(x^2+1))
            (4*t + 4)*w + (t + 1)/(t^2 + 2*t + 2)

        We make another extension of a rational function field::

            sage: K3.<yy> = FunctionField(QQ); R3.<xx> = K3[]
            sage: L3.<xx> = K3.extension(yy^2 - xx^3 - 1)

        This is the function field L with the generators exchanged. We define a morphism to L::

            sage: g = L3.hom([x,y]); g
            Function Field morphism:
              From: Function field in xx defined by -xx^3 + yy^2 - 1
              To:   Function field in y defined by y^2 - x^3 - 1
              Defn: xx |--> x
                    yy |--> y

        """
        if base_morphism is not None:
            raise NotImplementedError("Function field homorphisms with optional argument base_morphism are not implemented yet. Please specify the images of the generators of the base fields manually.")

        if not isinstance(im_gens, (list,tuple)):
            im_gens = [im_gens]
        if len(im_gens) == 0:
            raise ValueError("no images specified")

        if len(im_gens) > 1:
            base_morphism = self.base_field().hom(im_gens[1:], base_morphism)

        # the codomain of this morphism is the field containing all the im_gens
        codomain = im_gens[0].parent();
        if base_morphism is not None:
            if base_morphism.codomain().has_coerce_map_from(codomain):
                codomain = base_morphism.codomain();

        from maps import FunctionFieldMorphism_polymod
        return FunctionFieldMorphism_polymod(self.Hom(codomain), im_gens[0], base_morphism)

    def rational_function_field(self):
        """
        Return the rational function field underlying self.

        EXAMPLES::

            sage: K.<x> = FunctionField(QQ); R.<y> = K[]
            sage: L.<y> = K.extension(y^2-x); RR.<z> = L[]
            sage: M.<z> = L.extension(z^2-y)
            sage: K.rational_function_field()
            Rational function field in x over Rational Field
            sage: L.rational_function_field()
            Rational function field in x over Rational Field
            sage: M.rational_function_field()
            Rational function field in x over Rational Field
        """
        return self.base_field().rational_function_field()

    @cached_method
    def genus(self):
        """
        Return the genus of this function field
        For now, the genus is computed using singular

        EXAMPLES::

            sage: K.<x> = FunctionField(QQ); R.<y> = K[]
            sage: L.<y> = K.extension(y^3 - (x^3 + 2*x*y + 1/x))
            sage: L.genus()
            3
        """
        # unfortunately singular can not compute the genus with the polynomial_ring()._singular_
        # object because genus method only accepts a ring of transdental degree 2 over a prime field
        # not a ring of transdental degree 1 over a rational function field of one variable

        if not self.constant_base_field().is_prime_field():
            raise NotImplementedError("Computation of genus over this base field not implemented yet")
        elif not is_RationalFunctionField(self._base_field):
            return self.simple_model()[0].genus()
        else:
            #Making the auxiliary ring which only has polynomials with integral coefficients.
            tmpAuxRing = PolynomialRing(self._base_field.constant_field(), str(self._base_field.gen())+','+str(self._ring.gen()))
            intMinPoly, d = self._make_monic_integral(self._polynomial)
            curveIdeal = tmpAuxRing.ideal(intMinPoly)

            singular.lib('normal.lib') #loading genus method in singular
            return int(curveIdeal._singular_().genus())

    @cached_method
    def derivation(self):
        """
        Return a generator of the space of derivations over the constant base
        ring of this function field.

        OUTPUT:

        A mapping of function fields which extends the usual derivation on
        polynomials to this function field.

        .. NOTE::

            Only implemented for separable extensions of rational function
            fields.  For a separable extension `L` of a rational function field
            `K(x)`, the space of derivations `\mathrm{Der}_K L` is a
            one-dimensional `K`-vector space generated by the mapping this
            method returns, see Theorem 5.1 in Section 5 of Chapter VIII of
            [Lang2002].

        REFERENCES::

        .. [Lang2002] Serge Lang. Algebra. Springer, 2002.

        EXAMPLES::

            sage: K.<x> = FunctionField(GF(3))
            sage: R.<y> = K[]
            sage: L.<y> = K.extension(y^2 - x)
            sage: d = L.derivation(); d
            Derivation map:
                From: Function field in y defined by y^2 + 2*x
                To:   Function field in y defined by y^2 + 2*x
            sage: d(x)
            1
            sage: d(x^3)
            0
            sage: d(x*y)
            0
            sage: d(y)
            2/x*y

        """
        from maps import FunctionFieldDerivation_polymod
        if not self.polynomial().gcd(self.polynomial().derivative()).is_one():
            K, K_to_self, self_to_K = self.separable_model(names=('a','b'))
            return K_to_self*K.derivation()*self_to_K
        else:
            return FunctionFieldDerivation_polymod(self, self.base_ring().derivation())

    @cached_method
    def separable_model(self, names):
        """
        Return a function field isomorphic to this field which is separable
        extension of a rational function field.

        INPUT:

        - ``names`` -- a tuple of two strings; the first entry will be used as
          the variable name of the rational function field, the second entry
          will be used as the variable name of its separable extension.

        OUTPUT:

        A function field ``K`` isomorphic to ``self``, an isomorphism from
        ``K`` to ``self``, and an isomorphism from ``self`` to ``K``.

        ALGORITHM:

        The algorithm is described in the proof of Proposition 4.1 in Chapter
        VIII of [Lang2002]. It is only implemented for simple extensions of
        rational function fields over perfect field.

        REFERENCES::

        .. [Lang2002] Serge Lang. Algebra. Springer, 2002.

        EXAMPLES::

            sage: K.<x> = FunctionField(GF(2))
            sage: R.<y> = K[]
            sage: L.<y> = K.extension(y^2 - x^3)
            sage: L.separable_model(('t','w'))
            (Function field in w defined by t^3 + x^2, Composite map:
              From: Function field in w defined by t^3 + x^2
              To:   Function field in y defined by y^2 + x^3
              Defn:   Morphism of function fields defined by w |--> x,  x |--> w
                    then
                      Morphism of function fields defined by w |--> y, Composite map:
              From: Function field in y defined by y^2 + x^3
              To:   Function field in w defined by t^3 + x^2
              Defn:   Morphism of function fields defined by y |--> w
                    then
                      Morphism of function fields defined by w |--> x,  x |--> w)

        This also works for non-integral polynomials::

            sage: K.<x> = FunctionField(GF(2))
            sage: R.<y> = K[]
            sage: L.<y> = K.extension(y^2/x - x^2)
            sageL.separable_model(('t','w'))
            (Function field in w defined by t^3 + x^2, Composite map:
              From: Function field in w defined by t^3 + x^2
              To:   Function field in y defined by 1/x*y^2 + x^2
              Defn:   Morphism of function fields defined by w |--> x,  x |--> w
                    then
                      Morphism of function fields defined by w |--> y, Composite map:
              From: Function field in y defined by 1/x*y^2 + x^2
              To:   Function field in w defined by t^3 + x^2
              Defn:   Morphism of function fields defined by y |--> w
                    then
                      Morphism of function fields defined by w |--> x,  x |--> w)

        TESTS:

        Check that this does not break in characteristic zero::

            sage: K.<x> = FunctionField(QQ)
            sage: R.<y> = K[]
            sage: L.<y> = K.extension(y^2 - x^3)
            sage: L.separable_model(('t','w'))
            (Function field in w defined by y^2 - x^3, Morphism of function fields defined by w |--> y, Morphism of function fields defined by y |--> w)

        """
        if not isinstance(self.base_ring(), RationalFunctionField):
            L, from_L, to_L = self.simple_model()
            K, from_K, to_K = L.separable_model(names=('a','b'))
            return K, from_L*from_K, to_K*to_L
        if not self.constant_base_field().is_perfect():
            raise NotImplementedError("only implemented for function fields over perfect constant base fields.")
        if len(names) != 2:
            raise ValueError("must provide exactly two variable names")

        K, from_K, to_K = self.monic_integral_model(names[1])

        # if K is separable, then we are done
        if K.polynomial().gcd(K.polynomial().derivative()).is_one():
            return K, from_K, to_K

        # otherwise, the polynomial of K must be separable in the other variable
        Kx = K.base_ring()
        # construct a field isomorphic to K on top of Kx
        # turn the minpoly of K into a bivariate polynomial
        from sage.rings.polynomial.polynomial_ring_constructor import PolynomialRing
        R = PolynomialRing(self.constant_base_field(), names)
        f = R( K.polynomial().map_coefficients(lambda c:c.numerator(), Kx._ring.change_var(names[0])).change_variable_name(names[1]) )
        # f must be separable in the other variable (otherwise it would factor)
        f = f.polynomial(R.gen(0)).change_ring(Kx)
        f /= f.leading_coefficient()
        assert f.gcd(f.derivative()).is_one()

        Ly = Kx.extension(f, names=(names[1]))
        # an isomorphishm from Ly to K
        from_Ly = Ly.hom( [K(K.base_ring().gen()), K.gen()] )
        # an isomorphism from K to Ly
        to_Ly = K.hom( [Ly(Kx.gen()), Ly.gen()] )
        return Ly, from_K*from_Ly, to_Ly*to_K

    def _simple_model(self, name):
        """
        Turn a tower of simple field extensions M/L/K into a simple extension N/K.

        EXAMPLES::

            sage: K.<x> = FunctionField(QQ); R.<y> = K[]
            sage: L.<y> = K.extension(y^2-x); R.<z> = L[]
            sage: M.<z> = L.extension(z^2-y)
            sage: M._simple_model('u')
            (Function field in u defined by u^4 - x, Morphism of function fields defined by z |--> u,  y |--> u^2, x |--> x, Morphism of function fields defined by u |--> z)

        Not implemented for inseparable extensions::

            sage: K.<x> = FunctionField(GF(2)); R.<y> = K[]
            sage: L.<y> = K.extension(y^2-x); R.<z> = L[]
            sage: M.<z> = L.extension(z^2-y)
            sage: M._simple_model('u')
            Traceback (most recent call last):
            ...
            NotImplementedError: cannot determine primitive elements for inseparable extensions
        """
        M = self
        L = M.base_field()
        K = L.base_field()

        assert(K is not L)
        assert(L is not M)

        if (L.polynomial().derivative()==0 or M.polynomial().derivative()==0) and not self.constant_base_field().is_perfect():
            raise NotImplementedError("cannot determine primitive elements for inseparable extensions over imperfect constant base field")

        # By THE MINIMUM NUMBER OF GENERATORS FOR INSEPARABLE ALGEBRAIC EXTENSIONS the extension is simple. It therefore admits only finitely many intermediate fields (Bosch, Aufgabe 3.6.7). If K(a+x^ib)=K(a+x^jb) then a,b can be found as linear combinations of the generators.

        y = M.gen()
        x = L.gen()

        total_degree = M.degree()*L.degree()

        # guess a primitive element y + l*x taking l from the rational function field k(x)
        for l in K.rational_function_field():
            v = M(y+l*x)

            from sage.matrix.matrix_space import MatrixSpace
            MS = MatrixSpace(K, total_degree)

            # compute the minimal polynomial of v over K (!= v.minpoly() since that would be over L)
            from itertools import product
            basis_xy = [x**n*y**m for (n,m) in product(range(L.degree()),range(M.degree()))]

            A = v._matrix_over_base(K)
            A = MS.matrix(A)
            minpoly = A.minpoly(name)
            assert minpoly.base_ring() is K

            # v is a primitive element iff the degree of minpoly is the degree of M/K
            if minpoly.degree()!=total_degree:
                continue

            R = K[name]
            N = K.extension(minpoly,names=(name))
            u = N.gen()

            # the homomorphism N -> M
            from_N = N.hom(v)

            # the homomorphism M -> N is given by a change of basis from (1,v,v^2,...) to (1,y,y^2,x,x*y,...)
            #basis_v = [v**n for n in range(total_degree)]
            #B = [(v**n)._coefficients(K) for n in range(total_degree)]
            #MS = MatrixSpace(N,total_degree)
            #B = MS.matrix(B)
            #from sage.modules.free_module import FreeModule
            #image = B.solve_right(FreeModule(N,total_degree)([u**n for n in range(total_degree)]))
            #to_N = M.hom([image[L.degree()],image[1]])

            return N,from_N,~from_N

    @cached_method
    def simple_model(self, base_field=None, name='y'):
        """
        Turn a tower of field extensions into a single simple extension. 
        This is only implemented for a tower of separable field extensions.

        INPUT:

            - ``base_field`` -- the resulting field will be an extension of this field; defaults to the underlying rational function field if not specified.
            - ``name`` -- the name of generator of the simple extension; defaults to ``y``. This paramater is ignored if self is a simple extension of base_field already.

        OUTPUT:

            - self as a simple extension of ``base_field``
            - a morphism from the constructed field to self
            - a morphism from self to the constructed field

        EXAMPLES:

        A tower of four function fields::

            sage: K.<x> = FunctionField(QQ); R.<z> = K[]
            sage: L.<z> = K.extension(z^2-x); R.<u> = L[]
            sage: M.<u> = L.extension(u^2-z); R.<v> = M[]
            sage: N.<v> = M.extension(v^2-u)

        The fields N and M as simple extensions of K::

            sage: N.make_simple()
            (Function field in y defined by y^8 - x, Morphism of function fields defined by v |--> y,  u |--> y^2,  z |--> y^4,  x |--> x, Morphism of function fields defined by y |--> v,  x |--> x)
            sage: M.make_simple()
            (Function field in y defined by y^4 - x, Morphism of function fields defined by u |--> y,  z |--> y^2,  x |--> x, Morphism of function fields defined by y |--> u,  x |--> x)

        An optional parameter ``name`` names the generator of the simple extension::

            sage: M.make_simple(name='t')
            (Function field in t defined by t^4 - x, Morphism of function fields defined by u |--> t,  z |--> t^2,  x |--> x, Morphism of function fields defined by t |--> u,  x |--> x)

        An optional parameter ``base_field`` can be given to compute a simple extension over a subfield::

            sage: N.make_simple(base_field=L)
            (Function field in y defined by y^4 - z, Morphism of function fields defined by v |--> y,  u |--> y^2,  z |--> z,  x |--> x, Morphism of function fields defined by y |--> v,  z |--> z,  x |--> x)

        The parameter ``name`` is ignored if the extension is simple already::

            sage: L.make_simple(name='t')
            (Function field in z defined by z^2 - x, Morphism of function fields defined by z |--> z, Morphism of function fields defined by z |--> z)
            sage: N.make_simple(base_field=M, name='t')
            (Function field in v defined by v^2 - u, Morphism of function fields defined by v |--> v, Morphism of function fields defined by v |--> v)

        Primitive elements may be more complicated than in the above examples::

            sage: K.<x> = FunctionField(GF(3)); R.<y> = K[]
            sage: L.<y> = K.extension(y^2-x^3); R.<z> = L[]
            sage: M.<z> = L.extension(z^2-y^3)
            sage: M.make_simple()
            (Function field in y defined by y^4 + 2*x^9, Morphism of function fields defined by z |--> y,  y |--> 1/x^3*y^2,  x |--> x, Morphism of function fields defined by y |--> z,  x |--> x)

        For inseparable extensions make_simple is not implemented::

            sage: K.<x> = FunctionField(GF(2)); R.<y> = K[]
            sage: L.<y> = K.extension(y^2-x); R.<z> = L[]
            sage: M.<z> = L.extension(z^2-y)
            sage: M.make_simple()
            Traceback (most recent call last):
            ...
            NotImplementedError: cannot determine primitive elements for inseparable extensions
        """
        if base_field is None:
            base_field = self.rational_function_field()

        # the extension is simple already
        if base_field==self.base_field() or base_field==self:
            return (self,self.Hom(self).identity(),self.Hom(self).identity())

        # turn a tower of two simple extension L/M/K into a simple extension M/K
        M, from_M, to_M = self._simple_model(name)
        # recursively simplify the resulting extension M/.../base_field to a simple extension N/base_field
        N, N_to_M, M_to_N = M.simple_model(name=name,base_field=base_field)

        return N, from_M*N_to_M, M_to_N*to_M

    def primitive_element(self, base=None):
        """
        Return a primitive element of this field over base. If base is not specified it defaults to self.base_field().base_field().
        This is only implemented for a tower of separable field extensions.

        EXAMPLES::

            sage: K.<x> = FunctionField(QQ); R.<y> = K[]
            sage: L.<y> = K.extension(y^2-x); R.<z> = L[]
            sage: M.<z> = L.extension(z^2-y)
            sage: M.primitive_element()
            z
            sage: L.primitive_element()
            y
            sage: K.primitive_element()
            1
            sage: R.<z> = L[]; N.<u> = L.extension(z^2-x-1)
            sage: N.primitive_element()
            u + y
            sage: N.primitive_element(base=L)
            u
            sage: K.<x> = FunctionField(GF(2)); R.<Y> = K[]
            sage: L.<y> = K.extension(Y^2-x); R.<Z> = L[]
            sage: M.<z> = L.extension(Z^2-y)
            sage: M.primitive_element()
            Traceback (most recent call last):
            ...
            NotImplementedError: cannot determine primitive elements for inseparable extensions
        """
        if base is None:
            base = self.base_field().base_field()

        # trivial cases
        if base==self:
            return self(1)
        if base==self.base_field():
            return self.gen()

        # turn self/self.base_field().base_field() into a simple extension
        (simple,to_simple, from_simple) = self.simple_model(self.base_field().base_field())
        # recursively turn simple into simple extension over base
        primitive = simple.primitive_element(base)
        # map the primitive element of this extension back to self
        return from_simple(primitive)

    @cached_method
    def relative_vector_space(self, base):
        """
        Return a vector space V and isomorphisms self --> V and V --> self.

        This functions allows us to identify the elements of self with
        elements of a vector space over the field `base`.

        OUTPUT:

            - ``V`` - a vector space over the field base
            - ``from_V`` - an isomorphism from V to self
            - ``to_V`` - an isomorphism from self to V

        EXAMPLES::

            sage: K.<x> = FunctionField(QQ); R.<y> = K[]
            sage: L.<y> = K.extension(y^2-x); R.<z> = L[]
            sage: M.<z> = L.extension(z^2-y)

        M is of dimension 2 over L, but of dimension 4 over K::

            sage: M.relative_vector_space(L)
            (Vector space of dimension 2 over Function field in y defined by y^2 - x, Isomorphism morphism:
              From: Vector space of dimension 2 over Function field in y defined by y^2 - x
              To:   Function field in z defined by z^2 - y, Isomorphism morphism:
              From: Function field in z defined by z^2 - y
              To:   Vector space of dimension 2 over Function field in y defined by y^2 - x)
            sage: M.relative_vector_space(K)
            (Vector space of dimension 4 over Rational function field in x over Rational Field, Isomorphism morphism:
              From: Vector space of dimension 4 over Rational function field in x over Rational Field
              To:   Function field in z defined by z^2 - y, Isomorphism morphism:
              From: Function field in z defined by z^2 - y
              To:   Vector space of dimension 4 over Rational function field in x over Rational Field)

        Fields are one-dimensional vector spaces over themselves::

            sage: K.relative_vector_space(K)[0]
            Vector space of dimension 1 over Rational function field in x over Rational Field
            sage: L.relative_vector_space(L)[0]
            Vector space of dimension 1 over Function field in y defined by y^2 - x

        The parameter base must specify a function field that self is based upon::

            sage: M.relative_vector_space(QQ)
            Traceback (most recent call last):
            ...
            ValueError: Rational Field does not qualify as a subfield of Function field in z defined by z^2 - y
        """
        from sage.misc.misc_c import prod
        import maps
        V = base**prod([field.degree() for field in self._intermediate_fields(base)[:-1]])
        from_V = maps.MapVectorSpaceToFunctionField(V, self, base)
        to_V   = maps.MapFunctionFieldToVectorSpace(self, V, base)
        return (V, from_V, to_V)

    def vector_space(self):
        """
        Return a vector space V and isomorphisms self --> V and V --> self.

        This function allows us to identify the elements of self with
        elements of a vector space over the base field, which is
        useful for representation and arithmetic with orders, ideals,
        etc.
        
        OUTPUT:

            -  ``V`` - a vector space over the base field
            -  ``from_V`` - an isomorphism from V to self
            -  ``to_V`` - an isomorphism from self to V

        EXAMPLES:

        We define a function field::
        
            sage: K.<x> = FunctionField(QQ); R.<y> = K[]
            sage: L.<w> = K.extension(y^5 - (x^3 + 2*x*y + 1/x)); L
            Function field in w defined by y^5 - 2*x*y + (-x^4 - 1)/x

        We get the vector spaces, and maps back and forth::
        
            sage: V, from_V, to_V = L.vector_space()
            sage: V
            Vector space of dimension 5 over Rational function field in x over Rational Field
            sage: from_V
            Isomorphism morphism:
              From: Vector space of dimension 5 over Rational function field in x over Rational Field
              To:   Function field in w defined by y^5 - 2*x*y + (-x^4 - 1)/x
            sage: to_V
            Isomorphism morphism:
              From: Function field in w defined by y^5 - 2*x*y + (-x^4 - 1)/x
              To:   Vector space of dimension 5 over Rational function field in x over Rational Field

        We convert an element of the vector space back to the function field::
        
            sage: from_V(V.1)
            w

        We define an interesting element of the function field::
        
            sage: a = 1/L.0; a
            (-x/(-x^4 - 1))*w^4 + 2*x^2/(-x^4 - 1)

        We convert it to the vector space, and get a vector over the base field::
        
            sage: to_V(a)
            (2*x^2/(-x^4 - 1), 0, 0, 0, -x/(-x^4 - 1))

        We convert to and back, and get the same element::
        
            sage: from_V(to_V(a)) == a
            True

        In the other direction::

            sage: v = x*V.0 + (1/x)*V.1
            sage: to_V(from_V(v)) == v
            True

        For a repeated extension this is the vector space over the base field::

            sage: R.<z> = L[]
            sage: M.<z> = L.extension(z^2 - w)
            sage: M.vector_space()
            (Vector space of dimension 2 over Function field in w defined by y^5 - 2*x*y + (-x^4 - 1)/x, Isomorphism morphism:
              From: Vector space of dimension 2 over Function field in w defined by y^5 - 2*x*y + (-x^4 - 1)/x
              To:   Function field in z defined by z^2 - w, Isomorphism morphism:
              From: Function field in z defined by z^2 - w
              To:   Vector space of dimension 2 over Function field in w defined by y^5 - 2*x*y + (-x^4 - 1)/x)
        """
        return self.relative_vector_space(self.base_field())

    def _squarefree_decomposition_univariate_polynomial(self, f):
        from sage.structure.factorization import Factorization
        if f.is_nth_power(self.characteristic()):
            g = f.nth_root(self.characteristic())
            G = g.squarefree_decomposition()
            return Factorization([(g,e*self.characteristic()) for (g,e) in G],unit=G.unit()**self.characteristic())
        if f.degree() == 1:
            return Factorization([(f/f.leading_coefficient(),1)],unit=f.leading_coefficient())
        if f.is_monic() and f.degree() == 2 and not f.is_nth_power(2):
            return Factorization([(f,1)])
        print "Squarefree decomposition not implemented yet for %s"%f
        raise NotImplementedError

    def _factor_univariate_polynomial(self, f):
        r"""

        sage: k = GF(2)
        sage: K.<x> = FunctionField(k)
        sage: R.<u> = K[]
        sage: L.<u> = K.extension(u^3-x)
        sage: R.<t> = L[]
        sage: (t^2+u*t).factor()

        """
        from sage.structure.factorization import Factorization
        if self.degree() == 1:
            g = f.map_coefficients(lambda c:c._x(self.polynomial()[0]), self.base())
            G = g.factor()
            ret = Factorization([ (F.map_coefficients(lambda c:c, self), e) for F,e in G ], unit=self(G.unit()))
        elif not f.is_squarefree():
            F = f.squarefree_decomposition()
            ret = []
            unit = f.parent().one()*F.unit()
            for g,e_g in F:
                G = g.factor()
                unit *= G.unit()
                ret.extend( [(h,e_h*e_g) for (h,e_h) in G] )
            ret = Factorization( ret, unit=unit)
        elif not isinstance(self.base_ring(), RationalFunctionField):
            L, from_L, to_L = self.simple_model()
            F = f.map_coefficients(to_L).factor()
            assert F.unit() == 1
            return Factorization( [(h.map_coefficients(from_L),e_h) for h,e_h in F] )
        elif self.polynomial().gcd(self.polynomial().derivative()) != 1:
            L, from_L, to_L = self.separable_model(names=('a','b'))
            F = f.map_coefficients(to_L).factor()
            assert F.unit() == 1
            return Factorization( [(h.map_coefficients(from_L),e_h) for h,e_h in F] )
        else:
            s,g,r = self._sqfr_norm(f)
            F = r.factor()
            if len(F)==1: return Factorization([(f,1)])
            ret = []
            for (h,e) in F:
                assert(e==1)
                h = h(g.parent().gen())
                h = g.gcd(h)
                g = g // h
                ret.append( (h(h.parent().gen()+s*self.gen()), e) )
            assert(F.unit() == 1)
            ret = Factorization( ret )

        assert ret.prod() == f, (ret, f)
        return ret

    def _sqfr_norm(self, f):
        if not isinstance(self.base_ring(), RationalFunctionField):
            raise NotImplementedError("only implemented for simple extensions of rational function fields.")
        if self.polynomial().gcd(self.polynomial().derivative()) != 1:
            raise NotImplementedError("only implemented for separable extensions of function fields.")
        assert self.degree() > 1
        s = self.base().gen()
        while True:
            g = f(f.parent().gen() - s*self.gen())
            R = PolynomialRing(self.base(), names=('x', 'y'))
            x,y = R.gens()
            P = self.polynomial()(y)
            G = g.map_coefficients(lambda c:c._x(y), y.parent())
            r = P.resultant(G(x), y)
            r = r.polynomial(y)
            assert( r.is_constant() )
            r = r[0]
            r = r(f.parent().change_ring(self.base()).gen())
            if r.is_squarefree():
                assert r.base_ring() is self.base()
                assert g(g.parent().gen() + s*self.gen()) == f
                return s,g,r
            s *= self.base().gen()
            print s

def is_RationalFunctionField(x):
    """
    Return ``True`` if ``x`` is of rational function field type.

    EXAMPLES::

        sage: from sage.rings.function_field.function_field import is_RationalFunctionField
        sage: is_RationalFunctionField(QQ)
        False
        sage: is_RationalFunctionField(FunctionField(QQ,'t'))
        True
    """
    if isinstance(x, RationalFunctionField):
        return True
    else:
        return False

class RationalFunctionField(FunctionField):
    """
    A rational function field K(t) in one variable, over an arbitrary
    base field.

    EXAMPLES::

        sage: K.<t> = FunctionField(GF(3)); K
        Rational function field in t over Finite Field of size 3
        sage: K.gen()
        t
        sage: 1/t + t^3 + 5
        (t^4 + 2*t + 1)/t

    There are various ways to get at the underlying fields and rings
    associated to a rational function field::

        sage: K.<t> = FunctionField(GF(7))
        sage: K.base_field()
        Rational function field in t over Finite Field of size 7
        sage: K.field()
        Fraction Field of Univariate Polynomial Ring in t over Finite Field of size 7
        sage: K.constant_field()
        Finite Field of size 7
        sage: K.maximal_order()
        Maximal order in Rational function field in t over Finite Field of size 7

    We define a morphism::

        sage: K.<t> = FunctionField(QQ)
        sage: L = FunctionField(QQ, 'tbar') # give variable name as second input
        sage: K.hom(L.gen())
        Function Field morphism:
          From: Rational function field in t over Rational Field
          To:   Rational function field in tbar over Rational Field
          Defn: t |--> tbar
    """
    def genus(self):return 0

    def __init__(self, constant_field, names,
            element_class = FunctionFieldElement_rational,
            category=CAT):
        """
        Create a rational function field in one variable.

        INPUT:

            - ``constant_field`` -- an arbitrary field
            - ``names`` -- a string or tuple of length 1
            - ``category`` -- default: FunctionFields()

        EXAMPLES::

            sage: K.<t> = FunctionField(CC); K
            Rational function field in t over Complex Field with 53 bits of precision
            sage: K.category()
            Category of function fields
            sage: FunctionField(QQ[I], 'alpha')
            Rational function field in alpha over Number Field in I with defining polynomial x^2 + 1

        Must be over a field::

            sage: FunctionField(ZZ, 't')
            Traceback (most recent call last):
            ...
            TypeError: constant_field must be a field
        """
        if names is None:
            raise ValueError("variable name must be specified")
        elif not isinstance(names, tuple):
            names = (names, )
        if not constant_field.is_field():
            raise TypeError("constant_field must be a field")
        self._element_class = element_class
        self._element_init_pass_parent = False
        Field.__init__(self, self, names=names, category = category)
        R = constant_field[names[0]]
        self._constant_field = constant_field
        self._ring = R
        self._field = R.fraction_field()
        self._populate_coercion_lists_(coerce_list=[self._field])
        self._gen = self(R.gen())

    def derivation(self):
        """
        Return a generator of the space of derivations over the constant base
        ring of this rational function field.

        OUTPUT:

        A mapping of function fields which extends the usual derivation on
        polynomials to rational functionts.

        .. NOTE::

            For a rational function field `K(x)`, the space of derivations
            `\mathrm{Der}_K K(x)` is a one-dimensional `K`-vector space
            generated by the mapping this method returns, see Theorem 5.1 in
            Section 5 of Chapter VIII of [Lang2002].

        REFERENCES::

        .. [Lang2002] Serge Lang. Algebra. Springer, 2002.

        EXAMPLES::

            sage: K.<x> = FunctionField(GF(3))
            sage: d = K.derivation(); d
            Derivation map:
              From: Rational function field in x over Finite Field of size 3
              To:   Rational function field in x over Finite Field of size 3
            sage: d(x)
            1
            sage: d(x^2)
            2*x
            sage: d(x^3)
            0
            sage: d(1/x^3)
            0

        """
        from maps import FunctionFieldDerivation_rational
        return FunctionFieldDerivation_rational(self, self.one())

    def __reduce__(self):
        """
        Returns the arguments which were used to create this instance. The rationale for this is explained in the documentation of ``UniqueRepresentation``.

        EXAMPLES::

            sage: K.<x> = FunctionField(QQ)
            sage: clazz,args = K.__reduce__()
            sage: clazz(*args)
            Rational function field in x over Rational Field
        """
        from constructor import FunctionField
        return FunctionField, (self._constant_field, self._names)

    def change_variable_name(self, names):
        """
        Return a rational function field over the same constant field but in
        the variable ``names``.

        INPUT:

        - ``names`` -- a string or a tuple consisting of a single string, the
          variable name of the new rational function field

        OUTPUT:

        A rational function field.

        EXAMPLES::

            sage: K.<x> = FunctionField(QQ)
            sage: K.change_variable_name('y')
            Rational function field in y over Rational Field
            sage: L.<y> = K.change_variable_name(); L
            Rational function field in y over Rational Field

        """
        if isinstance(names,tuple):
            if len(names)!=1:
                raise ValueError("names must be a string or a tuple consisting of exactly one string.")
        else:
            names = (names,)

        constructor, args = self.__reduce__()
        args = list(args)
        args[1] = names
        return constructor(*args)

    def __hash__(self):
        """
        Return hash of this function field.

        The hash is formed from the constant field and the variable names.

        EXAMPLES::

            sage: K.<t> = FunctionField(QQ)
            sage: hash(K) == hash((K.constant_base_field(), K.variable_names()))
            True

        """
        return hash((self.constant_field(), self.variable_name()))

    def _cache_key(self):
        return self.constant_field(), self.variable_name()

    def _repr_(self):
        """
        Return string representation of this function field.

        EXAMPLES::

            sage: K.<t> = FunctionField(QQ)
            sage: K._repr_()
            'Rational function field in t over Rational Field'
        """
        return "Rational function field in %s over %s"%(
            self.variable_name(), self._constant_field)

    def _element_constructor_(self, x):
        r"""
        Coerce ``x`` into an element of this function field, possibly not canonically.

        INPUT:

            - ``x`` -- the element

        OUTPUT:

            ``x``, as an element of this function field

        EXAMPLES::

            sage: K.<t> = FunctionField(QQ)
            sage: a = K._element_constructor_(K.maximal_order().gen()); a
            t
            sage: a.parent()
            Rational function field in t over Rational Field

        TESTS:

        Conversion of a string::

            sage: K('t')
            t
            sage: K('1/t')
            1/t

        Conversion of a constant polynomial over the function field::

            sage: K(K.polynomial_ring().one())
            1

        Some indirect test of conversion::

            sage: S.<x, y> = K[]
            sage: I = S*[x^2 - y^2, y-t]
            sage: I.groebner_basis()
            [x^2 - t^2, y - t]

        """
        if isinstance(x, FunctionFieldElement):
            return FunctionFieldElement_rational(self, self._field(x._x))
        try:
            x = self._field(x)
        except TypeError, Err:
            try:
                if x.parent() is self.polynomial_ring():
                    return x[0]
            except AttributeError:
                pass
            raise Err
        return FunctionFieldElement_rational(self, x)

    def _to_bivariate_polynomial(self, f):
        """
        Convert ``f`` from a univariate polynomial over the rational function
        field into a bivariate polynomial and a denominator.

        INPUT:

            - ``f`` -- a univariate polynomial over self.

        OUTPUT:

            - bivariate polynomial, denominator

        EXAMPLES::

            sage: R.<t> = FunctionField(GF(7))
            sage: S.<X> = R[]
            sage: f = (1/t)*(X^4 - 1/t^2)*(X^3 - t^3)
            sage: R._to_bivariate_polynomial(f)
            (X^7*t^2 - X^4*t^5 - X^3 + t^3, t^3)
        """
        v = f.list()
        from sage.rings.arith import LCM
        denom = LCM([a.denominator() for a in v])
        S = denom.parent()
        x,t = S.base_ring()['%s,%s'%(f.parent().variable_name(),self.variable_name())].gens()
        phi = S.hom([t])
        return sum([phi((denom * v[i]).numerator()) * x**i for i in range(len(v))]), denom

    def _factor_univariate_polynomial(self, f, proof=True):
        """
        Factor the univariate polynomial ``f`` over self.

        EXAMPLES::

        We do a factorization over the function field over the rationals::

            sage: R.<t> = FunctionField(QQ)
            sage: S.<X> = R[]
            sage: f = (1/t)*(X^4 - 1/t^2)*(X^3 - t^3)
            sage: f.factor()             # indirect doctest
            (1/t) * (X - t) * (X^2 - 1/t) * (X^2 + 1/t) * (X^2 + t*X + t^2)
            sage: f.factor().prod() == f
            True

        We do a factorization over a finite prime field::

            sage: R.<t> = FunctionField(GF(7))
            sage: S.<X> = R[]
            sage: f = (1/t)*(X^4 - 1/t^2)*(X^3 - t^3)
            sage: f.factor()
            (1/t) * (X + 3*t) * (X + 5*t) * (X + 6*t) * (X^2 + 1/t) * (X^2 + 6/t)
            sage: f.factor().prod() == f
            True

        Factoring over a function field over a non-prime finite field::

            sage: k.<a> = GF(9)
            sage: R.<t> = FunctionField(k)
            sage: S.<X> = R[]
            sage: f = (1/t)*(X^3 - a*t^3)
            sage: f.factor()
            (1/t) * (X + (a + 2)*t)^3
            sage: f.factor().prod() == f
            True

        Factoring with strange "contents"::

            sage: K.<x> = FunctionField(GF(3))
            sage: R.<t> = K[]
            sage: (x^3*t^3 + x^6).factor()

        """
        F, d = self._to_bivariate_polynomial(f)

        if hasattr(F.base_ring(), "absolute_extension"):
            l_to_k,k_to_l,l = F.base_ring().absolute_extension()
            G = F.map_coefficients(k_to_l)
            fac = G.factor()
            from sage.structure.factorization import Factorization
            fac = Factorization([(g.map_coefficients(l_to_k),e) for g,e in fac], unit=fac.unit().map_coefficients(l_to_k))
        else:
            fac = F.factor()
        x = f.parent().gen()
        t = f.parent().base_ring().gen()
        phi = F.parent().hom([x, t])
        v = [(phi(P),e) for P, e in fac]
        unit = phi(fac.unit())/d
        w = []
        for a, e in v:
            c = a.leading_coefficient()
            a = a/c
            unit *= (c**e)
            if a.is_one():
                continue
            w.append((a,e))
        from sage.structure.factorization import Factorization
        return Factorization(w, unit=unit)

    @cached_method
    def polynomial_ring(self, var='x'):
        """
        Return a polynomial ring in one variable over this rational function field.

        INPUT:

            - ``var`` -- a string (default: 'x')

        EXAMPLES::

            sage: K.<x> = FunctionField(QQ)
            sage: K.polynomial_ring()
            Univariate Polynomial Ring in x over Rational function field in x over Rational Field
            sage: K.polynomial_ring('T')
            Univariate Polynomial Ring in T over Rational function field in x over Rational Field
        """
        return self[var]

    @cached_method
    def vector_space(self):
        """
        Return a vector space V and isomorphisms self --> V and V --> self.

        OUTPUT:

            -  ``V`` -- a vector space over the rational numbers
            -  ``from_V`` -- an isomorphism from V to self
            -  ``to_V`` -- an isomorphism from self to V

        EXAMPLES::

            sage: K.<x> = FunctionField(QQ)
            sage: K.vector_space()
            (Vector space of dimension 1 over Rational function field in x over Rational Field, Isomorphism morphism:
              From: Vector space of dimension 1 over Rational function field in x over Rational Field
              To:   Rational function field in x over Rational Field, Isomorphism morphism:
              From: Rational function field in x over Rational Field
              To:   Vector space of dimension 1 over Rational function field in x over Rational Field)
        """
        V = self.base_field()**1
        from maps import MapVectorSpaceToFunctionField, MapFunctionFieldToVectorSpace
        from_V = MapVectorSpaceToFunctionField(V, self)
        to_V   = MapFunctionFieldToVectorSpace(self, V)
        return (V, from_V, to_V)

    def random_element(self, *args, **kwds):
        """
        Create a random element of this rational function field.

        Parameters are passed to the random_element method of the
        underlying fraction field.

        EXAMPLES::

            sage: FunctionField(QQ,'alpha').random_element()   # random
            (-1/2*alpha^2 - 4)/(-12*alpha^2 + 1/2*alpha - 1/95)
        """
        return self(self._field.random_element(*args, **kwds))

    def degree(self, base=None):
        """
        Return the degree over the base field of this rational
        function field. Since the base field is the rational function
        field itself, the degree is 1.

        INPUT:

        - ``base`` -- must be this field or ``None``; this parameter is ignored
          and exists to resemble the interface of
          :meth:`FunctionField_polymod.degree`.

        EXAMPLES::

            sage: K.<t> = FunctionField(QQ)
            sage: K.degree()
            1
        """
        if base is None:
            base = self
        if base is not self:
            raise ValueError("base must be None or the rational function field")
        from sage.rings.integer_ring import ZZ
        return ZZ(1)

    def gen(self, n=0):
        """
        Return the ``n``-th generator of this function field.  If ``n`` is not
        0, then an IndexError is raised.

        EXAMPLES::

            sage: K.<t> = FunctionField(QQ); K.gen()
            t
            sage: K.gen().parent()
            Rational function field in t over Rational Field
            sage: K.gen(1)
            Traceback (most recent call last):
            ...
            IndexError: Only one generator.
        """
        if n != 0:
            raise IndexError("Only one generator.")
        return self._gen

    def ngens(self):
        """
        Return the number of generators, which is 1.

        EXAMPLES::

            sage: K.<t> = FunctionField(QQ)
            sage: K.ngens()
            1
        """
        return 1

    def base_field(self):
        """
        Return the base field of this rational function field, which is just
        this function field itself.

        EXAMPLES::

            sage: K.<t> = FunctionField(GF(7))
            sage: K.base_field()
            Rational function field in t over Finite Field of size 7
        """
        return self

    def hom(self, im_gens, base_morphism=None):
        """
        Create a homomorphism from self to another function field.

        INPUT:

            - ``im_gens`` -- exactly one element of some function field
            - ``base_morphism`` -- ignored

        OUTPUT:

            - a map between function fields

        EXAMPLES:

        We make a map from a rational function field to itself::

            sage: K.<x> = FunctionField(GF(7))
            sage: K.hom( (x^4 + 2)/x)
            Function Field endomorphism of Rational function field in x over Finite Field of size 7
              Defn: x |--> (x^4 + 2)/x

        We construct a map from a rational function field into a
        non-rational extension field::

            sage: K.<x> = FunctionField(GF(7)); R.<y> = K[]
            sage: L.<y> = K.extension(y^3 + 6*x^3 + x)
            sage: f = K.hom(y^2 + y  + 2); f
            Function Field morphism:
              From: Rational function field in x over Finite Field of size 7
              To:   Function field in y defined by y^3 + 6*x^3 + x
              Defn: x |--> y^2 + y + 2
            sage: f(x)
            y^2 + y + 2
            sage: f(x^2)
            5*y^2 + (x^3 + 6*x + 4)*y + 2*x^3 + 5*x + 4
        """
        from sage.structure.category_object import CategoryObject
        if isinstance(im_gens, CategoryObject):
            return self.Hom(im_gens).natural_map()
        if not isinstance(im_gens, (list,tuple)):
            im_gens = [im_gens]
        if len(im_gens) != 1:
            raise ValueError("there must be exactly one generator")
        x = im_gens[0]
        from maps import FunctionFieldMorphism_rational
        return FunctionFieldMorphism_rational(self.Hom(x.parent()), x)

    def field(self):
        """
        Return the underlying field, forgetting the function field
        structure.

        EXAMPLES::

            sage: K.<t> = FunctionField(GF(7))
            sage: K.field()
            Fraction Field of Univariate Polynomial Ring in t over Finite Field of size 7
        """
        return self._field

    @cached_method
    def maximal_order(self):
        """
        Return the maximal order of this function field.  Since this
        is a rational function field it is of the form K(t), and the
        maximal order is by definition K[t].

        EXAMPLES::

            sage: K.<t> = FunctionField(QQ)
            sage: K.maximal_order()
            Maximal order in Rational function field in t over Rational Field
            sage: K.equation_order()
            Maximal order in Rational function field in t over Rational Field
        """
        from function_field_order import FunctionFieldOrder_rational
        return FunctionFieldOrder_rational(self)

    equation_order = maximal_order

    def constant_base_field(self):
        """
        Return the field that this rational function field is a
        transcendental extension of.

        EXAMPLES::

            sage: K.<t> = FunctionField(QQ)
            sage: K.constant_field()
            Rational Field

        """
        return self._constant_field

    constant_field = constant_base_field

    def genus(self):
        """
        Return the genus of this function field
        This is always equal 0 for a rational function field

        EXAMPLES::

            sage: K.<x> = FunctionField(QQ);
            sage: K.genus()
            0
        """
        return 0

    def rational_function_field(self):
        """
        Return the rational function field underlying self. In this case (self
        is a RationalFunctionField object) it is simply itself.

        EXAMPLES::

            sage: K.<x> = FunctionField(QQ); R.<y> = K[]
            sage: K.rational_function_field()
            Rational function field in x over Rational Field
        """
        return self

    def is_constant(self):
        """
        Return True if self is a member of the constant base field.

        EXAMPLES::

            sage: K.<x> = FunctionField(QQ); R.<y> = K[]
            sage: L.<y> = K.extension(y^2-x)
            sage: L(1).is_constant()
            True
            sage: L(0).is_constant()
            True
            sage: y.is_constant()
            False
            sage: L(x).is_constant()
            False
        """
        if self==0: return True
        return len(self.element().coeffs())==1 and self.element().coeffs()[0].is_constant()

    def __iter__(self):
        """
        Create an infinite sequence of members of this field.

        EXAMPLES::

            sage: import itertools
            sage: K.<x> = FunctionField(QQ)
            sage: [a for a in itertools.islice(K,17)]
            [0, 1, -1, 1/2, -1/2, 2, -2, 1/3, -1/3, 3, -3, 2/3, -2/3, 3/2, -3/2, 1/4, -1/4]
            sage: K.<x> = FunctionField(GF(2))
            sage: [a for a in itertools.islice(K,17)]
            [0, 1, x, x/(x + 1), (x + 1)/x, x + 1, x^2, x^2/(x^2 + 1), x^2/(x + 1), x^2/(x^2 + x + 1), x^2 + x, (x^2 + x)/(x^2 + x + 1), (x^2 + 1)/x^2, (x^2 + 1)/x, x^2 + 1, (x^2 + 1)/(x^2 + x + 1), (x^2 + x + 1)/x^2]
        """
        k = self.constant_base_field()
        if not k.is_finite():
            for a in k:
                yield self(a)
        else:
            ret = self.one()
            while True:
                yield ret
                ret *= self.gen()

    @cached_method
    def derivation(self):
        r"""
        Return a generator of the space of derivations over the constant base
        field of this function field.

        A derivation on `R` is a map `R \to R` with
        `D(\alpha + \beta) = D(\alpha) + D(\beta)` and
        `D(\alpha \beta) = \beta D(\alpha)+\alpha D(\beta)`
        for all `\alpha, \beta \in R`. For a function
        field `K(x)` with `K` perfect, the derivations form a one-dimensional
        `K`-vector space generated by the extension of the usual derivation on
        `K[x]` (cf. Proposition 10 in [GT1996]_.)

        OUTPUT:

        An endofunction on this function field.

        REFERENCES:

        ..  [GT1996]
            Gianni, P., & Trager, B. (1996). Square-free algorithms in
            positive characteristic. Applicable Algebra in Engineering,
            Communication and Computing, 7(1), 1-14.

        EXAMPLES::

            sage: K.<x> = FunctionField(GF(3))
            sage: K.derivation()
            Derivation map:
              From: Rational function field in x over Finite Field of size 3
              To:   Rational function field in x over Finite Field of size 3

        TESTS::

            sage: L.<y> = FunctionField(K)
            sage: L.derivation()
            Traceback (most recent call last):
            ...
            NotImplementedError: not implemented for non-perfect base fields

        """
        from maps import FunctionFieldDerivation_rational
        if not self.constant_base_field().is_perfect():
            raise NotImplementedError("not implemented for non-perfect base fields")
        return FunctionFieldDerivation_rational(self, self.one())

    @cached_method(key=lambda self, base: None)
    def vector_space(self, base=None):
        """
        Return a vector space `V` and isomorphisms from this field to `V` and
        from `V` to this field.

        This function allows us to identify the elements of this field with
        elements of a one-dimensional vector space over the field itself. This
        method exists so that all function fields (rational or not) have the
        same interface.

        INPUT:

        - ``base`` -- must be this field or ``None`` (default: ``None``); this
          parameter is ignored and merely exists to have the same interface as
          :meth:`FunctionField_polymod.vector_space`.

        OUTPUT:

        - ``V`` -- a vector space over base field
        - ``from_V`` -- an isomorphism from V to this field
        - ``to_V`` -- an isomorphism from this field to V

        EXAMPLES::

            sage: K.<x> = FunctionField(QQ)
            sage: K.vector_space()
            (Vector space of dimension 1 over Rational function field in x over Rational Field, Isomorphism morphism:
              From: Vector space of dimension 1 over Rational function field in x over Rational Field
              To:   Rational function field in x over Rational Field, Isomorphism morphism:
              From: Rational function field in x over Rational Field
              To:   Vector space of dimension 1 over Rational function field in x over Rational Field)

        TESTS::

            sage: K.vector_space()
            (Vector space of dimension 1 over Rational function field in x over Rational Field, Isomorphism morphism:
              From: Vector space of dimension 1 over Rational function field in x over Rational Field
              To:   Rational function field in x over Rational Field, Isomorphism morphism:
              From: Rational function field in x over Rational Field
              To:   Vector space of dimension 1 over Rational function field in x over Rational Field)

        """
        from maps import MapVectorSpaceToFunctionField, MapFunctionFieldToVectorSpace
        if base is None:
            base = self
        if base is not self:
            raise ValueError("base must be the rational function field or None")
        V = base**1
        from_V = MapVectorSpaceToFunctionField(V, self)
        to_V   = MapFunctionFieldToVectorSpace(self, V)
        return (V, from_V, to_V)
