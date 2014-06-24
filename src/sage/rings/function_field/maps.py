r"""
Function Field Morphisms

AUTHORS:

- William Stein (2010): initial version

- Julian Rueth (2011-09-14, 2014-06-23): refactored class hierarchy; added
derivation classes

EXAMPLES::

    sage: K.<x> = FunctionField(QQ); R.<y> = K[]
    sage: K.hom(1/x)
    Morphism of function fields defined by x |--> 1/x
    sage: L.<y> = K.extension(y^2-x)
    sage: K.hom(y)
    Morphism of function fields defined by x |--> y
    sage: L.hom([y,x])
    Morphism of function fields defined by y |--> y,  x |--> x
    sage: L.hom([x,y])
    Traceback (most recent call last):
    ...
    ValueError: invalid morphism
"""
#*****************************************************************************
#       Copyright (C) 2010 William Stein <wstein@gmail.com>
#       Copyright (C) 2011-2014 Julian Rueth <julian.rueth@gmail.com>
#
#  Distributed under the terms of the GNU General Public License (GPL)
#  as published by the Free Software Foundation; either version 2 of
#  the License, or (at your option) any later version.
#                  http://www.gnu.org/licenses/
#*****************************************************************************

from sage.categories.morphism import Morphism
from sage.misc.cachefunc import cached_method
from sage.categories.map import Map
from sage.rings.morphism import RingHomomorphism

class FunctionFieldDerivation(Map):
    r"""
    A base class for derivations on function fields.

    A derivation on `R` is map `R\to R` with
    `D(\alpha+\beta)=D(\alpha)+D(\beta)` and `D(\alpha\beta)=\beta
    D(\alpha)+\alpha D(\beta)` for all `\alpha,\beta\in R`.

    EXAMPLES::

        sage: K.<x> = FunctionField(QQ)
        sage: d = K.derivation()
        sage: isinstance(d, sage.rings.function_field.maps.FunctionFieldDerivation)
        True

    """
    def __init__(self, K):
        r"""
        Initialize a derivation from ``K`` to ``K``.

        EXAMPLES::

            sage: K.<x> = FunctionField(QQ)
            sage: d = K.derivation() # indirect doctest

        """
        from function_field import is_FunctionField
        if not is_FunctionField(K):
            raise ValueError("K must be a function field")
        self.__field = K
        from sage.categories.homset import Hom
        from sage.categories.sets_cat import Sets
        Map.__init__(self, Hom(K,K,Sets()))

    def _repr_type(self):
        r"""
        Return the type of this map (a derivation), for the purposes of printing out self.

        EXAMPLES::

            sage: K.<x> = FunctionField(QQ)
            sage: d = K.derivation()
            sage: d._repr_type()
            'Derivation'

        """
        return "Derivation"

    def is_injective(self):
        r"""
        Return whether this derivation is injective.

        OUTPUT:

        Returns ``False`` since derivations are never injective.

        EXAMPLES::

            sage: K.<x> = FunctionField(QQ)
            sage: d = K.derivation()
            sage: d.is_injective()
            False

        """
        return False

class FunctionFieldDerivation_rational(FunctionFieldDerivation):
    r"""
    A derivation on a rational function field.

    INPUT:

    - ``K`` -- a rational function field

    - ``u`` -- an element of ``K``, the image of the generator of ``K`` under
      the derivation.

    EXAMPLES::

        sage: K.<x> = FunctionField(QQ)
        sage: d = K.derivation()
        sage: isinstance(d, sage.rings.function_field.maps.FunctionFieldDerivation_rational)
        True

    """
    def __init__(self, K, u):
        r"""
        Initialize a derivation of ``K`` which sends the generator of ``K`` to
        ``u``.

        EXAMPLES::

            sage: K.<x> = FunctionField(QQ)
            sage: d = K.derivation() # indirect doctest

        """
        from function_field import is_RationalFunctionField
        if not is_RationalFunctionField(K):
            raise ValueError("K must be a rational function field")
        if u.parent() is not K:
            raise ValueError("u must be an element in K")
        FunctionFieldDerivation.__init__(self, K)
        self._u = u

    def _call_(self, x):
        r"""
        Compute the derivation of ``x``.

        INPUT:

        - ``x`` -- an element of the rational function field

        EXAMPLES::

            sage: K.<x> = FunctionField(QQ)
            sage: d = K.derivation()
            sage: d(x) # indirect doctest
            1
            sage: d(x^3)
            3*x^2
            sage: d(1/x)
            -1/x^2

        """
        f,g = x.numerator(),x.denominator()

        if not f.gcd(g).is_one():
            raise NotImplementedError("derivations only implemented for rational functions with coprime numerator and denominator.")

        numerator = f.derivative()*g - f*g.derivative()
        if numerator.is_zero():
            return self.codomain().zero()
        else:
            return self._u * self.codomain()( numerator / g**2 )

class FunctionFieldIsomorphism(Morphism):
    r"""
    A base class for isomorphisms between function fields and
    vector spaces.

    EXAMPLES::

        sage: K.<x> = FunctionField(QQ); R.<y> = K[]
        sage: L.<y> = K.extension(y^2 - x*y + 4*x^3)
        sage: V, f, t = L.vector_space()
        sage: isinstance(f, sage.rings.function_field.maps.FunctionFieldIsomorphism)
        True
    """
    def _repr_type(self):
        """
        Return the type of this map (an isomorphism), for the purposes of printing out self.

        EXAMPLES::

            sage: K.<x> = FunctionField(QQ); R.<y> = K[]
            sage: L.<y> = K.extension(y^2 - x*y + 4*x^3)
            sage: V, f, t = L.vector_space()
            sage: f._repr_type()
            'Isomorphism'
        """
        return "Isomorphism"

    def is_injective(self):
        """
        Return True, since this isomorphism is injective.

        EXAMPLES::

            sage: K.<x> = FunctionField(QQ); R.<y> = K[]
            sage: L.<y> = K.extension(y^2 - x*y + 4*x^3)
            sage: V, f, t = L.vector_space()
            sage: f.is_injective()
            True
        """
        return True

    def is_surjective(self):
        """
        Return True, since this isomorphism is surjective.

        EXAMPLES::

            sage: K.<x> = FunctionField(QQ); R.<y> = K[]
            sage: L.<y> = K.extension(y^2 - x*y + 4*x^3)
            sage: V, f, t = L.vector_space()
            sage: f.is_surjective()
            True
        """
        return True

class MapVectorSpaceToFunctionField(FunctionFieldIsomorphism):
    r"""
    An isomorphism from a vector space to a function field.

    EXAMPLES::

        sage: K.<x> = FunctionField(QQ); R.<y> = K[]
        sage: L.<y> = K.extension(y^2 - x*y + 4*x^3)
        sage: V, f, t = L.vector_space(); f
        Isomorphism morphism:
          From: Vector space of dimension 2 over Rational function field in x over Rational Field
          To:   Function field in y defined by y^2 - x*y + 4*x^3
    """
    def __init__(self, V, K, base=None):
        """
        EXAMPLES::

            sage: K.<x> = FunctionField(QQ); R.<y> = K[]
            sage: L.<y> = K.extension(y^2 - x*y + 4*x^3)
            sage: V, f, t = L.vector_space(); type(f)
            <class 'sage.rings.function_field.maps.MapVectorSpaceToFunctionField'>
        """
        self._V = V
        self._K = K
        if base is None:
            base = K.base_field()
        self._base = base
        from sage.categories.homset import Hom
        FunctionFieldIsomorphism.__init__(self, Hom(V, K))

    def _call_(self, v):
        """
        EXAMPLES::

            sage: K.<x> = FunctionField(QQ); R.<y> = K[]
            sage: L.<y> = K.extension(y^2 - x*y + 4*x^3)
            sage: V, f, t = L.vector_space()
            sage: f(x*V.0 + (1/x^3)*V.1)         # indirect doctest
            1/x^3*y + x
        """
        fields = self._K._intermediate_fields(self._base)

        degrees = [f.degree() for f in fields[:-1]]
        from sage.misc.misc_c import prod

        # the basis 1,x,x^2,x*y,y,x*y,x^2*y,y^2,...
        from itertools import product
        basis = [prod([fields[i].gen()**exponents[i] for i in range(len(degrees))]) for exponents in product(*[range(d) for d in degrees])]

        coefficients = self._V(v).list()
        return self._K(sum([c*b for (c,b) in zip(coefficients,basis)]))

    def domain(self):
        """
        Return the vector space which is the domain of this isomorphism.

        EXAMPLES::

            sage: K.<x> = FunctionField(QQ); R.<y> = K[]
            sage: L.<y> = K.extension(y^2 - x*y + 4*x^3)
            sage: V, f, t = L.vector_space()
            sage: f.domain()
            Vector space of dimension 2 over Rational function field in x over Rational Field
        """
        return self._V

    def codomain(self):
        """
        Return the function field which is the codomain of this isomorphism.

        EXAMPLES::

            sage: K.<x> = FunctionField(QQ); R.<y> = K[]
            sage: L.<y> = K.extension(y^2 - x*y + 4*x^3)
            sage: V, f, t = L.vector_space()
            sage: f.codomain()
            Function field in y defined by y^2 - x*y + 4*x^3
        """
        return self._K

class MapFunctionFieldToVectorSpace(FunctionFieldIsomorphism):
    """
    An isomorphism from a function field to a vector space.

    EXAMPLES::

        sage: K.<x> = FunctionField(QQ); R.<y> = K[]
        sage: L.<y> = K.extension(y^2 - x*y + 4*x^3)
        sage: V, f, t = L.vector_space(); t
        Isomorphism morphism:
          From: Function field in y defined by y^2 - x*y + 4*x^3
          To:   Vector space of dimension 2 over Rational function field in x over Rational Field
    """
    def __init__(self, K, V, base=None):
        """
        EXAMPLES::

            sage: K.<x> = FunctionField(QQ); R.<y> = K[]
            sage: L.<y> = K.extension(y^2 - x*y + 4*x^3)
            sage: V, f, t = L.vector_space(); type(t)
            <class 'sage.rings.function_field.maps.MapFunctionFieldToVectorSpace'>
        """
        self._V = V
        self._K = K
        if base is None:
            base = K.base_field()
        self._base = base
        self._zero = K.base_ring()(0)
        from sage.misc.misc_c import prod
        self._n = prod([field.degree() for field in K._intermediate_fields(base)[:-1]])
        from sage.categories.homset import Hom
        FunctionFieldIsomorphism.__init__(self, Hom(K, V))

    def domain(self):
        """
        Return the function field which is the domain of this isomorphism.

        EXAMPLES::

            sage: K.<x> = FunctionField(QQ); R.<y> = K[]
            sage: L.<y> = K.extension(y^2 - x*y + 4*x^3)
            sage: V, f, t = L.vector_space()
            sage: t.domain()
            Function field in y defined by y^2 - x*y + 4*x^3
        """
        return self._K

    def codomain(self):
        """
        Return the vector space which is the domain of this isomorphism.

        EXAMPLES::

            sage: K.<x> = FunctionField(QQ); R.<y> = K[]
            sage: L.<y> = K.extension(y^2 - x*y + 4*x^3)
            sage: V, f, t = L.vector_space()
            sage: t.codomain()
            Vector space of dimension 2 over Rational function field in x over Rational Field
        """
        return self._V

    def _repr_type(self):
        """
        EXAMPLES::

            sage: K.<x> = FunctionField(QQ); R.<y> = K[]
            sage: L.<y> = K.extension(y^2 - x*y + 4*x^3)
            sage: V, f, t = L.vector_space()
            sage: t._repr_type()
            'Isomorphism'
        """
        return "Isomorphism"

    def _call_(self, x):
        """
        EXAMPLES::

            sage: K.<x> = FunctionField(QQ); R.<y> = K[]
            sage: L.<y> = K.extension(y^2 - x*y + 4*x^3)
            sage: V, f, t = L.vector_space()
            sage: t(x + (1/x^3)*y)                       # indirect doctest
            (x, 1/x^3)
        """
        y = self._K(x)
        v = y._vector_(self._base)
        w = v + [self._zero]*(self._n - len(v))
        return self._V(w)

class FunctionFieldMorphism(RingHomomorphism):
    r"""
    Base class for morphisms between function fields.
    """
    def __init__(self, parent, im_gen, base_morphism):
        """
        EXAMPLES::

            sage: K.<x> = FunctionField(QQ)
            sage: f = K.hom(1/x); f
            Morphism of function fields defined by x |--> 1/x
            sage: isinstance(f, sage.rings.function_field.maps.FunctionFieldMorphism)
            True
        """
        RingHomomorphism.__init__(self, parent)

        self._im_gen = im_gen
        self._base_morphism = base_morphism

    def is_injective(self):
        """
        Returns True since homomorphisms of fields are injective.

        EXAMPLES::

            sage: K.<x> = FunctionField(QQ)
            sage: f = K.hom(1/x); f
            Morphism of function fields defined by x |--> 1/x
            sage: f.is_injective()
            True
        """
        return True

    def __repr__(self):
        """
        EXAMPLES::

            sage: K.<x> = FunctionField(GF(7)); R.<y> = K[]
            sage: L.<y> = K.extension(y^3 + 6*x^3 + x)
            sage: f = L.hom(y*2)
            sage: f.__repr__()
            'Morphism of function fields defined by y |--> 2*y'
        """
        return "Morphism of function fields defined by %s"%self._short_repr()

    def _short_repr(self):
        """
        EXAMPLES::

            sage: K.<x> = FunctionField(GF(7)); R.<y> = K[]
            sage: L.<y> = K.extension(y^3 + 6*x^3 + x)
            sage: f = L.hom(y*2)
            sage: f._short_repr()
            'y |--> 2*y'
        """
        a = '%s |--> %s'%(self.domain().gen(), self._im_gen)
        if self._base_morphism is not None:
            a += ',  ' + self._base_morphism._short_repr()
        return a

class FunctionFieldMorphism_polymod(FunctionFieldMorphism):
    """
    Morphism from a finite extension of a function field to a function field.

    EXAMPLES::

        sage: K.<x> = FunctionField(QQ); R.<y> = K[]
        sage: L.<y> = K.extension(y^2 - x)
        sage: f = L.hom(-y); f
        Morphism of function fields defined by y |--> -y
    """
    def __init__(self, parent, im_gen, base_morphism, check=True):
        """
        EXAMPLES::

            sage: K.<x> = FunctionField(GF(7)); R.<y> = K[]
            sage: L.<y> = K.extension(y^3 + 6*x^3 + x)
            sage: f = L.hom(y*2); f
            Morphism of function fields defined by y |--> 2*y
            sage: type(f)
            <class 'sage.rings.function_field.maps.FunctionFieldMorphism_polymod'>
            sage: factor(L.polynomial())
            y^3 + 6*x^3 + x
            sage: f(y).charpoly('y')
            y^3 + 6*x^3 + x
        """
        FunctionFieldMorphism.__init__(self, parent, im_gen, base_morphism)
        if check:
            R = self.codomain()['X']
            v = parent.domain().polynomial().list()
            if base_morphism is not None:
                v = [base_morphism(a) for a in v]
            f = R(v)
            if f(im_gen):
                raise ValueError, "invalid morphism from %s to %s. It maps a root of the minimal polynomial %s to %s which is not a root of the minimal polynomial's image in the codomain %s"%(self.domain(),self.codomain(),self.domain().polynomial(),im_gen,f)

    def _call_(self, x):
        """
        EXAMPLES::

            sage: K.<x> = FunctionField(GF(7)); R.<y> = K[]
            sage: L.<y> = K.extension(y^3 + 6*x^3 + x); f = L.hom(y*2)
            sage: f(y/x + x^2/(x+1))            # indirect doctest
            2/x*y + x^2/(x + 1)
            sage: f(y)
            2*y
        """
        v = x.list()
        if self._base_morphism is not None:
            v = [self._base_morphism(a) for a in v]
        f = v[0].parent()['X'](v)
        return f(self._im_gen)

    @cached_method
    def __invert__(self):
        """
        Compute the inverse of this morphism if it exists.
        Only implemented if the underlying morphism ``base_morphism`` is the identity on the constant base field.
        Only implemented in few cases if domain or codomain are not separable extensions of their underlying rational function fields.

        EXAMPLES::

        For a morphism of rational function fields::

            sage: K.<x> = FunctionField(QQ)
            sage: f = K.hom((x+1)/(x-1)); f
            Morphism of function fields defined by x |--> (x + 1)/(x - 1)
            sage: ~f
            Morphism of function fields defined by x |--> (-x - 1)/(-x + 1)
            sage: g = K.hom(1/x); g
            Morphism of function fields defined by x |--> 1/x
            sage: ~g
            Morphism of function fields defined by x |--> -1/-x

        For a morphism between extensions of rational function fields::

            sage: K.<x> = FunctionField(QQ); R.<y> = K[]
            sage: L.<y> = K.extension(y^2-x); L
            Function field in y defined by y^2 - x
            sage: M.<u> = FunctionField(QQ); R.<v> = M[]
            sage: N.<v> = M.extension(v^2-u); N
            Function field in v defined by v^2 - u
            sage: f = L.hom([-v,u]); f
            Morphism of function fields defined by y |--> -v,  x |--> u
            sage: ~f
            Morphism of function fields defined by v |--> -y,  u |--> x

        Morphisms from a rational function field to an extension of a rational function field::

            sage: f = K.hom(1/v); f
            Morphism of function fields defined by x |--> (-1/-u)*v
            sage: ~f
            Morphism of function fields defined by v |--> 1/x,  u |--> 1/x^2

        Morphisms in the opposite direction::

            sage: g = N.hom([(x+1)/(x-1),(x+1)^2/(x-1)^2]); g
            Morphism of function fields defined by v |--> (x + 1)/(x - 1),  u |--> (x^2 + 2*x + 1)/(x^2 - 2*x + 1)
            sage: ~g
            Morphism of function fields defined by x |--> (2/(u - 1))*v + (u + 1)/(u - 1)

        An error occurs if the morphism cannot be inverted::

            sage: h = K.hom(N(u))
            sage: h
            Morphism of function fields defined by x |--> u
            sage: ~h
            Traceback (most recent call last):
            ...
            ArithmeticError: morphism is not invertible

         For an inseparable extension this is only implemented for morphisms which are the identity when restricted to the underlying rational function field::

            sage: K.<x> = FunctionField(GF(2)); R.<y> = K[]
            sage: L.<y> = K.extension(y^2-x)
            sage: f = L.hom(y); f
            Morphism of function fields defined by y |--> y
            sage: ~f
            Morphism of function fields defined by y |--> y,  x |--> x

         In more complex inseparable cases it is not implemented::

            sage: g = L.hom([y+1,x+1]); g
            Morphism of function fields defined by y |--> y + 1,  x |--> x + 1
            sage: ~g
            Traceback (most recent call last):
            ...
            NotImplementedError: only implemented if domain and codomain are separable extensions of their underlying rational function fields
        """
        # verify that base_morphism does not touch the constant base field
        base_morphism = self._base_morphism
        while base_morphism is not None:
            if not isinstance(base_morphism, FunctionFieldMorphism):
                raise NotImplementedError("only implemented if the underlying morphism ``base_morphism`` is the identity on the constant base field")
            base_morphism = base_morphism._base_morphism

        # automorphisms of rational function fields can be inverted directly
        if self.domain() is self.domain().rational_function_field() and self.codomain() is self.codomain().rational_function_field():
            y = self(self.domain().gen())
            a,b,c,d = y.numerator()[1],y.numerator()[0],y.denominator()[1],y.denominator()[0]
            if y != (a*self.codomain().gen() + b) / (c*self.codomain().gen() + d):
                raise ArithmeticError("morphism is not invertible")

            ret = self.codomain().hom( (d*self.domain().gen() - b) / (a - c*self.domain().gen()) )

        # if self is the identity on the underlying rational function field then domain and codomain are vector spaces over that function field and we simply have to invert the matrix corresponding to self.
        elif self(self.domain().rational_function_field().gen()) == self.codomain().rational_function_field().gen():
            (U,from_U,to_U) = self.domain().relative_vector_space(self.domain().rational_function_field())
            (V,from_V,to_V) = self.codomain().relative_vector_space(self.codomain().rational_function_field())
            f = U.hom([to_V(self(from_U(gen))) for gen in U.gens()], V)
            if not f.matrix().is_invertible():
                raise ArithmeticError("morphism is not invertible")
            ret = from_U*(~f)*to_V

        # reduce to the case of a simple extension
        elif self.domain().base_field() is not self.domain().rational_function_field() or self.codomain().base_field() is not self.codomain().rational_function_field(): 
            (D,D_to_domain,domain_to_D) = self.domain().make_simple()
            (C,C_to_codomain,codomain_to_C) = self.codomain().make_simple()
            g = ~(codomain_to_C*self*D_to_domain)
            ret = C_to_codomain*g*domain_to_D

        # construct a number of auxiliary fields which help to describe the inverse
        else: 
            # denote the codomain by K=k(x,y) and the domain by L=k(u,v)
            (K,x,y) = self.codomain(),self.codomain().rational_function_field().gen(),self.codomain().gen()
            (L,u,v) = self.domain(),self.domain().rational_function_field().gen(),self.domain().gen()

            # guess a primitive element for k(x,u,v)/k(x) of the form u+l*v with l in k(u)
            if not K._is_separable() or not L._is_separable():
                raise NotImplementedError("only implemented if domain and codomain are separable extensions of their underlying rational function fields")

            # by the primitive element theorem, there are no more than n*(n+1)/2 elements `l` such that u+l*v does not generate K(x,u,v) over K(x); with n=[K(x,u,v):K(x)]
            n = self(u).minpoly().degree()*self(v).minpoly().degree() # this bounds the degree of K(x,u,v)/K(x) from above
            from itertools import islice
            for l in islice(L.rational_function_field(),n*(n+1)/2+1):
                p = u+l*v

                try:
                    # construct some auxiliary fields (and morphisms):
                    # 1: M1=k(x,p)
                    M1 = K.base_field().extension(self(p).minpoly(), names=('p'))
                    M1_to_K = M1.hom([self(p),x]);
                    # 2: M2=k(p,x)
                    (M2,M2_to_M1,M1_to_M2) = M1.swap_generators()
                    # 3: N2=k(u,p)
                    N2 = L.base_field().extension(p.minpoly(), names=('p'))
                    N2_to_L = N2.hom([p,u])
                    # 3: N1=k(p,u)
                    (N1,N1_to_N2,N2_to_N1) = N2.swap_generators()
                    
                    # construction of the connecting morphism N1 -> M2
                    L_to_M2 = M1_to_M2*(~M1_to_K)*self # M1_to_K can be inverted since it is the identity on the underlying rational function fields
                    N1_to_M2 = N1.hom([L_to_M2(u),L_to_M2(p)])

                    # this produces a chain of morphisms K -> L
                    ret = N2_to_L*N1_to_N2*(~N1_to_M2)*M1_to_M2*(~M1_to_K) # N1_to_M2, M1_to_K can be inverted since they are the identity on the underlying rational function fields

                    break
                except ArithmeticError as e:
                    pass # p is not primitive
            else:
                raise ArithmeticError("morphism is not invertible")

        # simplify the inverse
        ret = ret.domain().hom([ret(field.gen()) for field in ret.domain()._intermediate_fields(ret.domain().rational_function_field())])
        
        # assert that the "inverse" is an actual inverse
        assert not any([(ret*self)(f.gen())-f.gen() for f in self.domain()._intermediate_fields(self.domain().rational_function_field())] + [(self*ret)(f.gen())-f.gen() for f in self.codomain()._intermediate_fields(self.codomain().rational_function_field())]) 

        return ret

class FunctionFieldMorphism_rational(FunctionFieldMorphism):
    """
    Morphism from a rational function field to a function field.

    EXAMPLES::

        sage: K.<x> = FunctionField(QQ)
        sage: f = K.hom(1/x); f
        Morphism of function fields defined by x |--> 1/x
    """
    def __init__(self, parent, im_gen):
        """
        EXAMPLES::

            sage: K.<x> = FunctionField(GF(7))
            sage: f = K.hom(1/x); f
            Morphism of function fields defined by x |--> 1/x
            sage: type(f)
            <class 'sage.rings.function_field.maps.FunctionFieldMorphism_rational'>
        """
        FunctionFieldMorphism.__init__(self, parent, im_gen, None)

    def _call_(self, x):
        """
        EXAMPLES::

            sage: K.<x> = FunctionField(GF(7))
            sage: f = K.hom(1/x); f
            Morphism of function fields defined by x |--> 1/x
            sage: f(x+1)                          # indirect doctest
            (x + 1)/x
            sage: 1/x + 1
            (x + 1)/x
        """
        if x.is_constant(): return self.codomain()(self.codomain().rational_function_field()(x.element()))
        return x.element()(self._im_gen)

    @cached_method
    def __invert__(self):
        """
        Compute the inverse of this morphism if it exists.
        Only implemented if the underlying morphism ``base_morphism`` is the identity on the constant base field.
        Only implemented in few cases if domain or codomain are not separable extensions of their underlying rational function fields.

        EXAMPLES::

        For a morphism of rational function fields::

            sage: K.<x> = FunctionField(QQ)
            sage: f = K.hom((x+1)/(x-1)); f
            Morphism of function fields defined by x |--> (x + 1)/(x - 1)
            sage: ~f
            Morphism of function fields defined by x |--> (-x - 1)/(-x + 1)
            sage: g = K.hom(1/x); g
            Morphism of function fields defined by x |--> 1/x
            sage: ~g
            Morphism of function fields defined by x |--> -1/-x

        For a morphism between extensions of rational function fields::

            sage: K.<x> = FunctionField(QQ); R.<y> = K[]
            sage: L.<y> = K.extension(y^2-x); L
            Function field in y defined by y^2 - x
            sage: M.<u> = FunctionField(QQ); R.<v> = M[]
            sage: N.<v> = M.extension(v^2-u); N
            Function field in v defined by v^2 - u
            sage: f = L.hom([-v,u]); f
            Morphism of function fields defined by y |--> -v,  x |--> u
            sage: ~f
            Morphism of function fields defined by v |--> -y,  u |--> x

        Morphisms from a rational function field to an extension of a rational function field::

            sage: f = K.hom(1/v); f
            Morphism of function fields defined by x |--> (-1/-u)*v
            sage: ~f
            Morphism of function fields defined by v |--> 1/x,  u |--> 1/x^2

        Morphisms in the opposite direction::

            sage: g = N.hom([(x+1)/(x-1),(x+1)^2/(x-1)^2]); g
            Morphism of function fields defined by v |--> (x + 1)/(x - 1),  u |--> (x^2 + 2*x + 1)/(x^2 - 2*x + 1)
            sage: ~g
            Morphism of function fields defined by x |--> (2/(u - 1))*v + (u + 1)/(u - 1)

        An error occurs if the morphism cannot be inverted::

            sage: h = K.hom(N(u))
            sage: h
            Morphism of function fields defined by x |--> u
            sage: ~h
            Traceback (most recent call last):
            ...
            ArithmeticError: morphism is not invertible

         For an inseparable extension this is only implemented for morphisms which are the identity when restricted to the underlying rational function field::

            sage: K.<x> = FunctionField(GF(2)); R.<y> = K[]
            sage: L.<y> = K.extension(y^2-x)
            sage: f = L.hom(y); f
            Morphism of function fields defined by y |--> y
            sage: ~f
            Morphism of function fields defined by y |--> y,  x |--> x

         In more complex inseparable cases it is not implemented::

            sage: g = L.hom([y+1,x+1]); g
            Morphism of function fields defined by y |--> y + 1,  x |--> x + 1
            sage: ~g
            Traceback (most recent call last):
            ...
            NotImplementedError: only implemented if domain and codomain are separable extensions of their underlying rational function fields
        """
        # verify that base_morphism does not touch the constant base field
        base_morphism = self._base_morphism
        while base_morphism is not None:
            if not isinstance(base_morphism, FunctionFieldMorphism):
                raise NotImplementedError("only implemented if the underlying morphism ``base_morphism`` is the identity on the constant base field")
            base_morphism = base_morphism._base_morphism

        # automorphisms of rational function fields can be inverted directly
        if self.codomain() is self.codomain().rational_function_field():
            y = self(self.domain().gen())
            a,b,c,d = y.numerator()[1],y.numerator()[0],y.denominator()[1],y.denominator()[0]
            if y != (a*self.codomain().gen() + b) / (c*self.codomain().gen() + d):
                raise ArithmeticError("morphism is not invertible")

            ret = self.codomain().hom( (d*self.domain().gen() - b) / (a - c*self.domain().gen()) )

        # if self is the identity on the underlying rational function field then domain and codomain are vector spaces over that function field and we simply have to invert the matrix corresponding to self.
        elif self(self.domain().gen()) == self.codomain().rational_function_field().gen():
            (U,from_U,to_U) = self.domain().relative_vector_space(self.domain().rational_function_field())
            (V,from_V,to_V) = self.codomain().relative_vector_space(self.codomain().rational_function_field())
            f = U.hom([to_V(self(from_U(gen))) for gen in U.gens()], V)
            if not f.matrix().is_invertible():
                raise ArithmeticError("morphism is not invertible")
            ret = from_U*(~f)*to_V

        # construct a number of auxiliary fields which help to describe the inverse
        else: 
            # denote the codomain by K=k(x,y) and the domain by L=k(u,v)
            (K,x,y) = self.codomain(),self.codomain().rational_function_field().gen(),self.codomain().gen()
            (L,u) = self.domain(),self.domain().gen()

            # guess a primitive element for k(x,u,v)/k(x) of the form u+l*v with l in k(u)
            if not K._is_separable():
                raise NotImplementedError("only implemented if domain and codomain are separable extensions of their underlying rational function fields")

            # construct some auxiliary fields (and morphisms):
            # 1: M1=k(x,u)
            M1 = K.base_field().extension(self(u).minpoly(), names=('u'))
            M1_to_K = M1.hom([self(u),x]);
            # 2: M2=k(u,x)
            (M2,M2_to_M1,M1_to_M2) = M1.swap_generators()
                    
            # construction of the connecting morphism N1 -> M2
            L_to_M2 = M1_to_M2*(~M1_to_K)*self # M1_to_K can be inverted since it is the identity on the underlying rational function fields

            # this produces a chain of morphisms K -> L
            ret = (~L_to_M2)*M1_to_M2*(~M1_to_K) # N1_to_M2, M1_to_K can be inverted since they are the identity on the underlying rational function fields

        # simplify the inverse
        ret = ret.domain().hom([ret(field.gen()) for field in ret.domain()._intermediate_fields(ret.domain().rational_function_field())])
        
        # assert that the "inverse" is an actual inverse
        assert not any([(ret*self)(f.gen())-f.gen() for f in self.domain()._intermediate_fields(self.domain().rational_function_field())] + [(self*ret)(f.gen())-f.gen() for f in self.codomain()._intermediate_fields(self.codomain().rational_function_field())]) 

        return ret

class FunctionFieldDerivation_polymod(FunctionFieldDerivation):
    r"""
    A derivation of function fields over the constant base field.

    EXAMPLES::

        sage: K.<x> = FunctionField(QQ)
        sage: R.<y> = K[]
        sage: L.<y> = K.extension(y^2 - x)
        sage: d = L.derivation()
        sage: isinstance(d, sage.rings.function_field.maps.FunctionFieldDerivation_polymod)
        True

    """
    def __init__(self, L, d):
        r"""
        Initialize a derivation of ``L`` which extends the derivation ``d`` on
        its base field.

        EXAMPLES::

            sage: K.<x> = FunctionField(QQ)
            sage: R.<y> = K[]
            sage: L.<y> = K.extension(y^2 - x)
            sage: d = L.derivation()

        """
        FunctionFieldDerivation.__init__(self, L)
        self._d = d

    @cached_method
    def _call_gen(self):
        f= self.domain().polynomial()
        x= self.domain().gen()
        if not f.gcd(f.derivative().is_one()):
            raise NotImplementedError("derivation only implemented for separable extensions")
        return - f.map_coefficients(lambda c:self._d(c))(x) / f.derivative()(x)

    def _call_(self, x):
        r"""
        Compute the derivative of ``x``.

        INPUT:

        - ``x`` -- an element of the function field

        EXAMPLES::

            sage: K.<x> = FunctionField(QQ)
            sage: R.<y> = K[]
            sage: L.<y> = K.extension(y^2 - x)
            sage: d = L.derivation()
            sage: d(x) # indirect doctest
            1
            sage: d(y)
            (-1/2/-x)*y
            sage: d(y^2)
            1

        """
        if x.is_zero():
            return self.codomain().zero()
        return x._x.map_coefficients(self._d) \
               + x._x.derivative()(self.domain().gen()) * self._call_gen()

    def _repr_defn(self):
        base = self._d._repr_defn()
        ret = "%s |--> %s"%(self.domain().gen(),self._call_gen())
        if base:
            return base + "\n" + ret
        else:
            return ret
