# -*- coding: utf-8 -*-
r"""
Discrete valuations on function fields

EXAMPLES:

We can create classical valuations that correspond to finite and infinite
places on a rational function field::

    sage: from mac_lane import * # optional: standalone
    sage: K.<x> = FunctionField(QQ)
    sage: v = FunctionFieldValuation(K, 1); v
    (x - 1)-adic valuation
    sage: v = FunctionFieldValuation(K, x^2 + 1); v
    (x^2 + 1)-adic valuation
    sage: v = FunctionFieldValuation(K, 1/x); v
    Valuation at the infinite place

Note that we can also specify valuations which do not correspond to a place of
the function field::

    sage: R.<x> = QQ[]
    sage: w = GaussValuation(R, pAdicValuation(QQ, 2))
    sage: v = FunctionFieldValuation(K, w); v
    2-adic valuation

Valuations on a rational function field can then be extended to finite
extensions::

    sage: v = FunctionFieldValuation(K, x - 1); v
    (x - 1)-adic valuation
    sage: R.<y> = K[]
    sage: L.<y> = K.extension(y^2 - x)
    sage: w = v.extensions(L); w # long time
    [[ (x - 1)-adic valuation, v(y - 1) = 1 ]-adic valuation,
     [ (x - 1)-adic valuation, v(y + 1) = 1 ]-adic valuation]

TESTS:

Run test suite for classical places over rational function fields::

    sage: K.<x> = FunctionField(QQ)
    sage: v = FunctionFieldValuation(K, 1)
    sage: TestSuite(v).run(max_runs=100) # long time

    sage: v = FunctionFieldValuation(K, x^2 + 1)
    sage: TestSuite(v).run(max_runs=100) # long time

    sage: v = FunctionFieldValuation(K, 1/x)
    sage: TestSuite(v).run(max_runs=100) # long time

Run test suite over classical places of finite extensions::

    sage: K.<x> = FunctionField(QQ)
    sage: v = FunctionFieldValuation(K, x - 1)
    sage: R.<y> = K[]
    sage: L.<y> = K.extension(y^2 - x)
    sage: ws = v.extensions(L) # long time
    sage: for w in ws: TestSuite(w).run(max_runs=100) # long time

Run test suite for valuations that do not correspond to a classical place::

    sage: K.<x> = FunctionField(QQ)
    sage: R.<x> = QQ[]
    sage: v = GaussValuation(R, pAdicValuation(QQ, 2))
    sage: w = FunctionFieldValuation(K, v)
    sage: TestSuite(w).run() # long time

Run test suite for some other classical places over large ground fields::

    sage: K.<t> = FunctionField(GF(3))
    sage: M.<x> = FunctionField(K)
    sage: v = FunctionFieldValuation(M, x^3 - t)
    sage: TestSuite(v).run(max_runs=10) # long time

Run test suite for extensions over the infinite place::

    sage: K.<x> = FunctionField(QQ)
    sage: v = FunctionFieldValuation(K, 1/x)
    sage: R.<y> = K[]
    sage: L.<y> = K.extension(y^2 - 1/(x^2 + 1))
    sage: w = v.extensions(L) # long time
    sage: TestSuite(w).run() # long time

Run test suite for a valuation with `v(1/x) > 0` which does not come from a
classical valuation of the infinite place::

    sage: K.<x> = FunctionField(QQ)
    sage: R.<x> = QQ[]
    sage: w = GaussValuation(R, pAdicValuation(QQ, 2)).augmentation(x, 1)
    sage: w = FunctionFieldValuation(K, w)
    sage: v = FunctionFieldValuation(K, (w, K.hom([~K.gen()]), K.hom([~K.gen()])))
    sage: TestSuite(v).run() # long time

Run test suite for extensions which come from the splitting in the base field::

    sage: K.<x> = FunctionField(QQ)
    sage: v = FunctionFieldValuation(K, x^2 + 1)
    sage: L.<x> = FunctionField(GaussianIntegers().fraction_field())
    sage: ws = v.extensions(L)
    sage: for w in ws: TestSuite(w).run(max_runs=100) # long time

Run test suite for a finite place with residual degree and ramification::

    sage: K.<t> = FunctionField(GF(3))
    sage: L.<x> = FunctionField(K)
    sage: v = FunctionFieldValuation(L, x^6 - t)
    sage: TestSuite(v).run(max_runs=10) # long time

Run test suite for a valuation which is backed by limit valuation::

    sage: K.<x> = FunctionField(QQ)
    sage: R.<y> = K[]
    sage: L.<y> = K.extension(y^2 - (x^2 + x + 1))
    sage: v = FunctionFieldValuation(K, x - 1)
    sage: w = v.extension(L)
    sage: TestSuite(w).run() # long time

AUTHORS:

- Julian Rüth (2016-10-16): initial version

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

from sage.structure.factory import UniqueFactory
from sage.rings.all import QQ, ZZ, infinity
from sage.misc.abstract_method import abstract_method

from valuation import DiscreteValuation
from trivial_valuation import TrivialValuation
from mapped_valuation import FiniteExtensionFromLimitValuation, MappedValuation_base

class FunctionFieldValuationFactory(UniqueFactory):
    r"""
    Create a valuation on ``domain`` corresponding to ``prime``.

    INPUT:

    - ``domain`` -- a function field

    - ``prime`` -- a place of the function field, a valuation on a subring, or
      a valuation on another function field together with information for
      isomorphisms to and from that function field

    EXAMPLES::
    
        sage: from mac_lane import * # optional: standalone
        sage: K.<x> = FunctionField(QQ)
    
    We create a valuation that correspond to a finite rational place of a function
    field::

        sage: v = FunctionFieldValuation(K, 1); v
        (x - 1)-adic valuation
        sage: v(x)
        0
        sage: v(x - 1)
        1

    A place can also be specified with an irreducible polynomial::

        sage: v = FunctionFieldValuation(K, x - 1); v
        (x - 1)-adic valuation
    
    Similarly, for a finite non-rational place::
        
        sage: v = FunctionFieldValuation(K, x^2 + 1); v
        (x^2 + 1)-adic valuation
        sage: v(x^2 + 1)
        1
        sage: v(x)
        0

    Or for the infinite place::
    
        sage: v = FunctionFieldValuation(K, 1/x); v
        Valuation at the infinite place
        sage: v(x)
        -1
    
    Instead of specifying a generator of a place, we can define a valuation on a
    rational function field by giving a discrete valuation on the underlying
    polynomial ring::
    
        sage: R.<x> = QQ[]
        sage: w = GaussValuation(R, TrivialValuation(QQ)).augmentation(x - 1, 1)
        sage: v = FunctionFieldValuation(K, w); v
        (x - 1)-adic valuation
    
    Note that this allows us to specify valuations which do not correspond to a
    place of the function field::
    
        sage: w = GaussValuation(R, pAdicValuation(QQ, 2))
        sage: v = FunctionFieldValuation(K, w); v
        2-adic valuation

    The same is possible for valuations with `v(1/x) > 0` by passing in an
    extra pair of parameters, an isomorphism between this function field and an
    isomorphic function field. That way you can, for example, indicate that the
    valuation is to be understood as a valuation on `K[1/x]`, i.e., after
    applying the substitution `x \mapsto 1/x` (here, the inverse map is also `x
    \mapsto 1/x`)::

        sage: w = GaussValuation(R, pAdicValuation(QQ, 2)).augmentation(x, 1)
        sage: w = FunctionFieldValuation(K, w)
        sage: v = FunctionFieldValuation(K, (w, K.hom([~K.gen()]), K.hom([~K.gen()]))); v
        Valuation on rational function field induced by [ Gauss valuation induced by 2-adic valuation, v(x) = 1 ] (in Rational function field in x over Rational Field after x |--> 1/x)

    Note that classical valuations at finite places or the infinite place are
    always normalized such that the uniformizing element has valuation 1::

        sage: K.<t> = FunctionField(GF(3))
        sage: M.<x> = FunctionField(K)
        sage: v = FunctionFieldValuation(M, x^3 - t)
        sage: v(x^3 - t)
        1

    However, if such a valuation comes out of a base change of the ground
    field, this is not the case anymore. In the example below, the unique
    extension of ``v`` to ``L`` still has valuation 1 on ``x^3 - t`` but it has
    valuation ``1/3`` on its uniformizing element  ``x - w``::

        sage: R.<w> = K[]
        sage: L.<w> = K.extension(w^3 - t)
        sage: N.<x> = FunctionField(L)
        sage: w = v.extension(N) # optional: integrated
        sage: w(x^3 - t) # optional: integrated
        1
        sage: w(x - w) # optional: integrated
        1/3

    There are several ways to create valuations on extensions of rational
    function fields::

        sage: K.<x> = FunctionField(QQ)
        sage: R.<y> = K[]
        sage: L.<y> = K.extension(y^2 - x); L
        Function field in y defined by y^2 - x

    A place that has a unique extension can just be defined downstairs::

        sage: v = FunctionFieldValuation(L, x); v
        (x)-adic valuation

    """
    def create_key_and_extra_args(self, domain, prime):
        r"""
        Create a unique key which identifies the valuation given by ``prime``
        on ``domain``.

        TESTS:

        We specify a valuation on a function field by two different means and
        get the same object::

            sage: from mac_lane import * # optional: standalone
            sage: K.<x> = FunctionField(QQ)
            sage: v = FunctionFieldValuation(K, x - 1) # indirect doctest

            sage: R.<x> = QQ[]
            sage: w = GaussValuation(R, TrivialValuation(QQ)).augmentation(x - 1, 1)
            sage: FunctionFieldValuation(K, w) is v
            True

        The normalization is, however, not smart enough, to unwrap
        substitutions that turn out to be trivial::
        
            sage: w = GaussValuation(R, pAdicValuation(QQ, 2))
            sage: w = FunctionFieldValuation(K, w)
            sage: w is FunctionFieldValuation(K, (w, K.hom([~K.gen()]), K.hom([~K.gen()])))
            False

        """
        from sage.categories.function_fields import FunctionFields
        from sage.rings.valuation.valuation_space import DiscretePseudoValuationSpace
        if domain not in FunctionFields():
            raise ValueError("Domain must be a function field.")

        if isinstance(prime, tuple):
            if len(prime) == 3:
                # prime is a triple of a valuation on another function field with
                # isomorphism information
                return self.create_key_and_extra_args_from_valuation_on_isomorphic_field(domain, prime[0], prime[1], prime[2])

        if prime in DiscretePseudoValuationSpace(domain):
            # prime is already a valuation of the requested domain
            # if we returned (domain, prime), we would break caching
            # because this element has been created from a different key
            # Instead, we return the key that was used to create prime
            # so the caller gets back a correctly cached version of prime
            if not hasattr(prime, "_factory_data"):
               raise NotImplementedError("Valuations on function fields must be unique and come out of the FunctionFieldValuation factory but %r has been created by other means"%(prime,))
            return prime._factory_data[2], {}

        if prime in domain:
            # prime defines a place
            return self.create_key_and_extra_args_from_place(domain, prime)
        if prime in DiscretePseudoValuationSpace(domain._ring):
            # prime is a discrete (pseudo-)valuation on the polynomial ring
            # that the domain is constructed from
            return self.create_key_and_extra_args_from_valuation(domain, prime)
        if domain.base_field() is not domain:
            # prime might define a valuation on a subring of domain and have a
            # unique extension to domain
            base_valuation = FunctionFieldValuation(domain.base_field(), prime)
            return self.create_key_and_extra_args_from_valuation(domain, base_valuation)

        raise NotImplementedError("argument must be a place or a pseudo-valuation on a supported subring but %r does not satisfy this for the domain %r"%(prime, domain))

    def create_key_and_extra_args_from_place(self, domain, generator):
        r"""
        Create a unique key which identifies the valuation at the place
        specified by ``generator``.

        TESTS:

            sage: from mac_lane import * # optional: standalone
            sage: K.<x> = FunctionField(QQ)
            sage: v = FunctionFieldValuation(K, 1/x) # indirect doctest

        """
        if generator not in domain.base_field():
            raise NotImplementedError("a place must be defined over a rational function field")

        if domain.base_field() is not domain:
            # if this is an extension field, construct the unique place over
            # the place on the subfield
            return self.create_key_and_extra_args(domain, FunctionFieldValuation(domain.base_field(), generator))

        if generator in domain.constant_base_field():
            # generator is a constant, we associate to it the place which
            # corresponds to the polynomial (x - generator)
            return self.create_key_and_extra_args(domain, domain.gen() - generator)

        if generator in domain._ring:
            # generator is a polynomial
            generator = domain._ring(generator)
            if not generator.is_monic():
                raise ValueError("place must be defined by a monic polynomiala but %r is not monic"%(generator,))
            if not generator.is_irreducible():
                raise ValueError("place must be defined by an irreducible polynomial but %r factors over %r"%(generator, domain._ring))
            # we construct the corresponding valuation on the polynomial ring
            # with v(generator) = 1
            from sage.rings.valuation.gauss_valuation import GaussValuation
            valuation = GaussValuation(domain._ring, TrivialValuation(domain.constant_base_field())).augmentation(generator, 1)
            return self.create_key_and_extra_args(domain, valuation)
        elif generator == ~domain.gen():
            # generator is 1/x, the infinite place
            return (domain, (FunctionFieldValuation(domain, domain.gen()), domain.hom(~domain.gen()), domain.hom(~domain.gen()))), {}
        else:
            raise ValueError("a place must be given by an irreducible polynomial or the inverse of the generator; %r does not define a place over %r"%(generator, domain))

    def create_key_and_extra_args_from_valuation(self, domain, valuation):
        r"""
        Create a unique key which identifies the valuation which extends
        ``valuation``.

        TESTS:

            sage: from mac_lane import * # optional: standalone
            sage: K.<x> = FunctionField(QQ)
            sage: R.<x> = QQ[]
            sage: w = GaussValuation(R, TrivialValuation(QQ)).augmentation(x - 1, 1)
            sage: v = FunctionFieldValuation(K, w) # indirect doctest

        """
        # this should have been handled by create_key already
        assert valuation.domain() is not domain

        if valuation.domain() is domain._ring:
            if domain.base_field() is not domain:
                vK = valuation.restriction(valuation.domain().base_ring())
                if vK.domain() is not domain.base_field():
                    raise ValueError("valuation must extend a valuation on the base field but %r extends %r whose domain is not %r"%(valuation, vK, domain.base_field()))
                # Valuation is an approximant that describes a single valuation
                # on domain.
                # For uniqueness of valuations (which provides better caching
                # and easier pickling) we need to find a normal form of
                # valuation, i.e., the smallest approximant that describes this
                # valuation
                approximants = vK.mac_lane_approximants(domain.polynomial())
                approximant = vK.mac_lane_approximant(domain.polynomial(), valuation, approximants)
                return (domain, approximant), {'approximants': approximants}
            else:
                # on a rational function field K(x), any valuation on K[x] that
                # is not only a pseudo-valuation extends to a valuation on K(x)
                if not valuation.is_discrete_valuation():
                    raise ValueError("valuation must be a discrete valuation but %r is not."%(valuation,))
                return (domain, valuation), {}

        if valuation.domain().is_subring(domain.base_field()):
            # valuation is defined on a subring of this function field, try to lift it
            return self.create_key_and_extra_args(domain, valuation.extension(domain))

        raise NotImplementedError("extension of valuation from %r to %r not implemented yet"%(valuation.domain(), domain))

    def create_key_and_extra_args_from_valuation_on_isomorphic_field(self, domain, valuation, to_valuation_domain, from_valuation_domain):
        r"""
        Create a unique key which identifies the valuation which is
        ``valuation`` after mapping through ``to_valuation_domain``.

        TESTS::

            sage: from mac_lane import * # optional: standalone
            sage: K.<x> = FunctionField(GF(2))
            sage: R.<y> = K[]
            sage: L.<y> = K.extension(y^2 + y + x^3)
            sage: v = FunctionFieldValuation(K, 1/x)
            sage: w = v.extension(L) # indirect doctest

        """
        from sage.categories.function_fields import FunctionFields
        if valuation.domain() not in FunctionFields():
            raise ValueError("valuation must be defined over an isomorphic function field but %r is not a function field"%(valuation.domain(),))

        from sage.categories.homset import Hom
        if to_valuation_domain not in Hom(domain, valuation.domain()):
            raise ValueError("to_valuation_domain must map from %r to %r but %r maps from %r to %r"%(domain, valuation.domain(), to_valuation_domain, to_valuation_domain.domain(), to_valuation_domain.codomain()))
        if from_valuation_domain not in Hom(valuation.domain(), domain):
            raise ValueError("from_valuation_domain must map from %r to %r but %r maps from %r to %r"%(valuation.domain(), domain, from_valuation_domain, from_valuation_domain.domain(), from_valuation_domain.codomain()))

        if domain is domain.base():
            # over rational function fields, we only support the map x |--> 1/x with another rational function field
            if valuation.domain() is not valuation.domain().base() or valuation.domain().constant_base_field() != domain.constant_base_field():
                raise NotImplementedError("maps must be isomorphisms with a rational function field over the same base field, not with %r"%(valuation.domain(),))
            if to_valuation_domain != domain.hom([~valuation.domain().gen()]):
                raise NotImplementedError("to_valuation_domain must be the map %r not %r"%(domain.hom([~valuation.domain().gen()]), to_valuation_domain))
            if from_valuation_domain != valuation.domain().hom([~domain.gen()]):
                raise NotImplementedError("from_valuation_domain must be the map %r not %r"%(valuation.domain().hom([domain.gen()]), from_valuation_domain))
            if domain != valuation.domain():
                # make it harder to create different representations of the same valuation
                # (nothing bad happens if we did, but >= and <= are only implemented when this is the case.)
                raise NotImplementedError("domain and valuation.domain() must be the same rational function field but %r is not %r"%(domain, valuation.domain()))
        else:
            if domain.base() is not valuation.domain().base():
                raise NotImplementedError("domain and valuation.domain() must have the same base field but %r is not %r"%(domain.base(), valuation.domain().base()))
            if to_valuation_domain != domain.hom([to_valuation_domain(domain.gen())]):
                raise NotImplementedError("to_valuation_domain must be trivial on the base fields but %r is not %r"%(to_valuation_domain, domain.hom([to_valuation_domain(domain.gen())])))
            if from_valuation_domain != valuation.domain().hom([from_valuation_domain(valuation.domain().gen())]):
                raise NotImplementedError("from_valuation_domain must be trivial on the base fields but %r is not %r"%(from_valuation_domain, valuation.domain().hom([from_valuation_domain(valuation.domain().gen())])))
            if to_valuation_domain(domain.gen()) == valuation.domain().gen():
                raise NotImplementedError("to_valuation_domain seems to be trivial but trivial maps would currently break partial orders of valuations")

        if from_valuation_domain(to_valuation_domain(domain.gen())) != domain.gen():
            # only a necessary condition
            raise ValueError("to_valuation_domain and from_valuation_domain are not inverses of each other")

        return (domain, (valuation, to_valuation_domain, from_valuation_domain)), {}

    def create_object(self, version, key, **extra_args):
        r"""
        Create the valuation specified by ``key``.

        EXAMPLES::

            sage: from mac_lane import * # optional: standalone
            sage: K.<x> = FunctionField(QQ)
            sage: R.<x> = QQ[]
            sage: w = GaussValuation(R, pAdicValuation(QQ, 2))
            sage: v = FunctionFieldValuation(K, w); v # indirect doctest
            2-adic valuation

        """
        domain, valuation = key
        from sage.rings.valuation.valuation_space import DiscretePseudoValuationSpace
        parent = DiscretePseudoValuationSpace(domain)

        if isinstance(valuation, tuple) and len(valuation) == 3:
            valuation, to_valuation_domain, from_valuation_domain = valuation
            if domain is domain.base() and valuation.domain() is valuation.domain().base() and to_valuation_domain == domain.hom([~valuation.domain().gen()]) and from_valuation_domain == valuation.domain().hom([~domain.gen()]):
                # valuation on the rational function field after x |--> 1/x
                if valuation == FunctionFieldValuation(valuation.domain(), valuation.domain().gen()):
                    # the classical valuation at the place 1/x
                    return parent.__make_element_class__(InfiniteRationalFunctionFieldValuation)(parent)
                return parent.__make_element_class__(RationalFunctionFieldMappedValuation)(parent, valuation, to_valuation_domain, from_valuation_domain)
            return parent.__make_element_class__(FunctionFieldExtensionMappedValuation)(parent, valuation, to_valuation_domain, from_valuation_domain)

        if domain is valuation.domain():
            # we can not just return valuation in this case
            # as this would break uniqueness and pickling
            raise ValueError("valuation must not be a valuation on domain yet but %r is a valuation on %r"%(valuation, domain))

        if domain.base_field() is domain:
            # valuation is a base valuation on K[x] that induces a valuation on K(x)
            if valuation.restriction(domain.constant_base_field()).is_trivial():
                # valuation corresponds to a finite place
                return parent.__make_element_class__(FiniteRationalFunctionFieldValuation)(parent, valuation)
            else:
                return parent.__make_element_class__(NonClassicalRationalFunctionFieldValuation)(parent, valuation)
        else:
            # valuation is a limit valuation that singles out an extension
            return parent.__make_element_class__(FunctionFieldFromLimitValuation)(parent, valuation, domain.polynomial(), extra_args['approximants'])

        raise NotImplementedError("valuation on %r from %r on %r"%(domain, valuation, valuation.domain()))

FunctionFieldValuation = FunctionFieldValuationFactory("FunctionFieldValuation")

class FunctionFieldValuation_base(DiscreteValuation):
    r"""
    Base class for valuations on function fields.

    TESTS::

        sage: from mac_lane import * # optional: standalone
        sage: K.<x> = FunctionField(QQ)
        sage: v = FunctionFieldValuation(K, x) # indirect doctest
        sage: isinstance(v, FunctionFieldValuation_base)
        True

    """
    def extensions(self, L):
        r"""
        Return the extensions of this valuation to ``L``.

        EXAMPLES::

            sage: from mac_lane import * # optional: standalone
            sage: K.<x> = FunctionField(QQ)
            sage: v = FunctionFieldValuation(K, x)
            sage: R.<y> = K[]
            sage: L.<y> = K.extension(y^2 - x)
            sage: v.extensions(L)
            [(x)-adic valuation]

        TESTS:

        Valuations over the infinite place::

            sage: v = FunctionFieldValuation(K, 1/x)
            sage: R.<y> = K[]
            sage: L.<y> = K.extension(y^2 - 1/(x^2 + 1))
            sage: v.extensions(L) # long time
            [[ Valuation at the infinite place, v(y - 1/x) = 3 ]-adic valuation,
             [ Valuation at the infinite place, v(y + 1/x) = 3 ]-adic valuation]

        Iterated extensions over the infinite place::

            sage: K.<x> = FunctionField(GF(2))
            sage: R.<y> = K[]
            sage: L.<y> = K.extension(y^2 + y + x^3)
            sage: v = FunctionFieldValuation(K, 1/x)
            sage: w = v.extension(L)
            sage: R.<z> = L[]
            sage: M.<z> = L.extension(z^2 - y)
            sage: w.extension(M) # squarefreeness is not implemented here
            Traceback (most recent call last):
            ...
            NotImplementedError

        """
        K = self.domain()
        from sage.categories.function_fields import FunctionFields
        if L is K:
            return [self]
        if L in FunctionFields():
            if K.is_subring(L):
                if L.base() is K:
                    # L = K[y]/(G) is a simple extension of the domain of this valuation
                    G = L.polynomial()
                    if not G.is_monic():
                        G = G / G.leading_coefficient()
                    if any(self(c) < 0 for c in G.coefficients()):
                        # rewrite L = K[u]/(H) with H integral and compute the extensions
                        from gauss_valuation import GaussValuation
                        g = GaussValuation(G.parent(), self)
                        y_to_u, u_to_y, H = g.monic_integral_model(G)
                        M = K.extension(H, names=L.variable_names())
                        H_extensions = self.extensions(M)

                        from sage.rings.morphism import RingHomomorphism_im_gens
                        if type(y_to_u) == RingHomomorphism_im_gens and type(u_to_y) == RingHomomorphism_im_gens:
                            return [FunctionFieldValuation(L, (w, L.hom([M(y_to_u(y_to_u.domain().gen()))]), M.hom([L(u_to_y(u_to_y.domain().gen()))]))) for w in H_extensions]
                        raise NotImplementedError
                    return [FunctionFieldValuation(L, w) for w in self.mac_lane_approximants(L.polynomial())]
                elif L.base() is not L and K.is_subring(L):
                    # recursively call this method for the tower of fields
                    from operator import add
                    return reduce(add, A, [])
                elif L.constant_field() is not K.constant_field() and K.constant_field().is_subring(L):
                    # subclasses should override this method and handle this case, so we never get here
                    raise NotImplementedError("Can not compute the extensions of %r from %r to %r since the base ring changes."%(self, self.domain(), ring))
        raise NotImplementedError("extension of %r from %r to %r not implemented"%(self, K, L))


class RationalFunctionFieldValuation_base(FunctionFieldValuation_base):
    r"""
    Base class for discrete valuations on rational function fields.

    TESTS::

        sage: from mac_lane import * # optional: standalone
        sage: K.<x> = FunctionField(GF(2))
        sage: v = FunctionFieldValuation(K, x) # indirect doctest
        sage: isinstance(v, RationalFunctionFieldValuation_base)
        True

    """


class ClassicalFunctionFieldValuation_base(FunctionFieldValuation_base):
    r"""
    Base class for discrete valuations on rational function fields that come
    from points on the projective line.

    TESTS::

        sage: from mac_lane import * # optional: standalone
        sage: K.<x> = FunctionField(GF(5))
        sage: v = FunctionFieldValuation(K, x) # indirect doctest
        sage: isinstance(v, ClassicalFunctionFieldValuation_base)
        True

    """
    def _test_classical_residue_field(self, **options):
        r"""
        Check correctness of the residue field of a discrete valuation at a
        classical point.

        TESTS::

            sage: from mac_lane import * # optional: standalone
            sage: K.<x> = FunctionField(QQ)
            sage: v = FunctionFieldValuation(K, x^2 + 1)
            sage: v._test_classical_residue_field()

        """
        tester = self._tester(**options)

        tester.assertTrue(self.domain().constant_field().is_subring(self.residue_field()))

    def _ge_(self, other):
        r"""
        Return whether ``self`` is greater or equal to ``other`` everywhere.

        EXAMPLES::

            sage: from mac_lane import * # optional: standalone
            sage: K.<x> = FunctionField(QQ)
            sage: v = FunctionFieldValuation(K, x^2 + 1)
            sage: w = FunctionFieldValuation(K, x)
            sage: v >= w
            False
            sage: w >= v
            False

        """
        if other.is_trivial():
            return other.is_discrete_valuation()
        if isinstance(other, ClassicalFunctionFieldValuation_base):
            return self == other
        super(ClassicalFunctionFieldValuation_base, self)._ge_(other)

class InducedFunctionFieldValuation_base(FunctionFieldValuation_base):
    r"""
    Base class for function field valuation induced by a valuation on the
    underlying polynomial ring.

    TESTS::

        sage: from mac_lane import * # optional: standalone
        sage: K.<x> = FunctionField(QQ)
        sage: v = FunctionFieldValuation(K, x^2 + 1) # indirect doctest

    """
    def __init__(self, parent, base_valuation):
        r"""
        TESTS::

            sage: from mac_lane import * # optional: standalone
            sage: K.<x> = FunctionField(QQ)
            sage: v = FunctionFieldValuation(K, x) # indirect doctest
            sage: isinstance(v, InducedFunctionFieldValuation_base)
            True
            
        """
        FunctionFieldValuation_base.__init__(self, parent)

        domain = parent.domain()
        if base_valuation.domain() is not domain._ring:
            raise ValueError("base valuation must be defined on %r but %r is defined on %r"%(domain._ring, base_valuation, base_valuation.domain()))

        self._base_valuation = base_valuation

    def uniformizer(self):
        r"""
        Return a uniformizing element for this valuation.

        EXAMPLES::

            sage: from mac_lane import * # optional: standalone
            sage: K.<x> = FunctionField(QQ)
            sage: FunctionFieldValuation(K, x).uniformizer()
            x
            
        """
        return self.domain()(self._base_valuation.uniformizer())

    def lift(self, F):
        r"""
        Return a lift of ``F`` to the :meth:`domain` of this valuation such
        that :meth:`reduce` returns the original element.

        EXAMPLES::

            sage: from mac_lane import * # optional: standalone
            sage: K.<x> = FunctionField(QQ)
            sage: v = FunctionFieldValuation(K, x)
            sage: v.lift(0)
            0
            sage: v.lift(1)
            1

        """
        F = self.residue_ring().coerce(F)
        if F in self._base_valuation.residue_ring():
            num = self._base_valuation.residue_ring()(F)
            den = self._base_valuation.residue_ring()(1)
        elif F in self._base_valuation.residue_ring().fraction_field():
            num = self._base_valuation.residue_ring()(F.numerator())
            den = self._base_valuation.residue_ring()(F.denominator())
        else:
            raise NotImplementedError("lifting not implemented for this valuation")

        return self.domain()(self._base_valuation.lift(num)) / self.domain()(self._base_valuation.lift(den))

    def value_group(self):
        r"""
        Return the value group of this valuation.

        EXAMPLES::

            sage: from mac_lane import * # optional: standalone
            sage: K.<x> = FunctionField(QQ)
            sage: FunctionFieldValuation(K, x).value_group()
            Additive Abelian Group generated by 1

        """
        return self._base_valuation.value_group()

    def reduce(self, f):
        r"""
        Return the reduction of ``f`` in :meth:`residue_ring`.

        EXAMPLES::

            sage: from mac_lane import * # optional: standalone
            sage: K.<x> = FunctionField(QQ)
            sage: v = FunctionFieldValuation(K, x^2 + 1)
            sage: v.reduce(x)
            u1

        """
        f = self.domain().coerce(f)

        if self(f) > 0:
            return self.residue_field().zero()
        if self(f) < 0:
            raise ValueError

        base = self._base_valuation

        num = f.numerator()
        den = f.denominator()

        assert base(num) == base(den)
        shift = base.element_with_valuation(-base(num))
        num *= shift
        den *= shift
        ret = base.reduce(num) / base.reduce(den)
        assert not ret.is_zero()
        return self.residue_field()(ret)

    def _repr_(self):
        r"""
        Return a printable representation of this valuation.

        EXAMPLES::

            sage: from mac_lane import * # optional: standalone
            sage: K.<x> = FunctionField(QQ)
            sage: FunctionFieldValuation(K, x^2 + 1) # indirect doctest
            (x^2 + 1)-adic valuation

        """
        from sage.rings.valuation.augmented_valuation import AugmentedValuation_base
        from sage.rings.valuation.gauss_valuation import GaussValuation
        if isinstance(self._base_valuation, AugmentedValuation_base):
            if self._base_valuation._base_valuation == GaussValuation(self.domain()._ring, TrivialValuation(self.domain().constant_field())):
                if self._base_valuation._mu == 1:
                    return "(%r)-adic valuation"%(self._base_valuation.phi())
        vK = self._base_valuation.restriction(self._base_valuation.domain().base_ring())
        if self._base_valuation == GaussValuation(self.domain()._ring, vK):
            return repr(vK)
        return "Valuation on rational function field induced by %s"%self._base_valuation

    def extensions(self, L):
        r"""
        Return all extensions of this valuation to ``L`` which has a larger
        constant field than the :meth:`domain` of this valuation.

        EXAMPLES::

            sage: from mac_lane import * # optional: standalone
            sage: K.<x> = FunctionField(QQ)
            sage: v = FunctionFieldValuation(K, x^2 + 1)
            sage: L.<x> = FunctionField(GaussianIntegers().fraction_field())
            sage: v.extensions(L) # indirect doctest
            [(x - I)-adic valuation, (x + I)-adic valuation]

        """
        K = self.domain()
        if L is K:
            return [self]

        from sage.categories.function_fields import FunctionFields
        if L in FunctionFields() \
            and K.is_subring(L) \
            and L.base() is L \
            and L.constant_field() is not K.constant_field() \
            and K.constant_field().is_subring(L.constant_field()):
            # The above condition checks whether L is an extension of K that
            # comes from an extension of the field of constants
            # Condition "L.base() is L" is important so we do not call this
            # code for extensions from K(x) to K(x)(y)
            
            # We extend the underlying valuation on the polynomial ring
            W = self._base_valuation.extensions(L._ring)
            return [FunctionFieldValuation(L, w) for w in W]

        return super(InducedFunctionFieldValuation_base, self).extensions(L)

    def _call_(self, f):
        r"""
        Evaluate this valuation at the function ``f``.

        EXAMPLES::

            sage: from mac_lane import * # optional: standalone
            sage: K.<x> = FunctionField(QQ)
            sage: v = FunctionFieldValuation(K, x) # indirect doctest
            sage: v((x+1)/x^2)
            -2
            
        """
        return self._base_valuation(f.numerator()) - self._base_valuation(f.denominator())

    def residue_ring(self):
        r"""
        Return the residue field of this valuation.

        EXAMPLES::

            sage: from mac_lane import * # optional: standalone
            sage: K.<x> = FunctionField(QQ)
            sage: FunctionFieldValuation(K, x).residue_ring()
            Rational Field

            sage: K.<x> = FunctionField(QQ)
            sage: v = GaussValuation(QQ['x'], pAdicValuation(QQ, 2))
            sage: w = FunctionFieldValuation(K, v)
            sage: w.residue_ring()
            Fraction Field of Univariate Polynomial Ring in x over Finite Field of size 2 (using NTL)

            sage: R.<x> = QQ[]
            sage: vv = v.augmentation(x, 1)
            sage: w = FunctionFieldValuation(K, vv)
            sage: w.residue_ring()
            Fraction Field of Univariate Polynomial Ring in x over Finite Field of size 2 (using NTL)
            
        """
        return self._base_valuation.residue_ring().fraction_field()

class FiniteRationalFunctionFieldValuation(ClassicalFunctionFieldValuation_base, InducedFunctionFieldValuation_base, RationalFunctionFieldValuation_base):
    r"""
    Valuation of a finite place of a function field.

    EXAMPLES::

        sage: from mac_lane import * # optional: standalone
        sage: K.<x> = FunctionField(QQ)
        sage: v = FunctionFieldValuation(K, x + 1); v # indirect doctest
        (x + 1)-adic valuation

    A finite place with residual degree::

        sage: w = FunctionFieldValuation(K, x^2 + 1); w
        (x^2 + 1)-adic valuation

    A finite place with ramification::

        sage: K.<t> = FunctionField(GF(3))
        sage: L.<x> = FunctionField(K)
        sage: u = FunctionFieldValuation(L, x^3 - t); u
        (x^3 + 2*t)-adic valuation

    A finite place with residual degree and ramification::

        sage: q = FunctionFieldValuation(L, x^6 - t); q
        (x^6 + 2*t)-adic valuation

    """
    def __init__(self, parent, base_valuation):
        r"""
        TESTS::
    
            sage: from mac_lane import * # optional: standalone
            sage: K.<x> = FunctionField(QQ)
            sage: v = FunctionFieldValuation(K, x + 1)
            sage: isinstance(v, FiniteRationalFunctionFieldValuation)
            True
    
        """
        ClassicalFunctionFieldValuation_base.__init__(self, parent)
        InducedFunctionFieldValuation_base.__init__(self, parent, base_valuation)
        RationalFunctionFieldValuation_base.__init__(self, parent)


class NonClassicalRationalFunctionFieldValuation(InducedFunctionFieldValuation_base, RationalFunctionFieldValuation_base):
    r"""
    Valuation induced by a valuation on the underlying polynomial ring which is
    non-classical.

    EXAMPLES::

        sage: from mac_lane import * # optional: standalone
        sage: K.<x> = FunctionField(QQ)
        sage: v = GaussValuation(QQ['x'], pAdicValuation(QQ, 2))
        sage: w = FunctionFieldValuation(K, v); w # indirect doctest
        2-adic valuation

    """
    def __init__(self, parent, base_valuation):
        r"""
        TESTS::

            sage: from mac_lane import * # optional: standalone
            sage: K.<x> = FunctionField(QQ)
            sage: v = GaussValuation(QQ['x'], pAdicValuation(QQ, 2))
            sage: w = FunctionFieldValuation(K, v)
            sage: isinstance(w, NonClassicalRationalFunctionFieldValuation)
            True

        """
        InducedFunctionFieldValuation_base.__init__(self, parent, base_valuation)
        RationalFunctionFieldValuation_base.__init__(self, parent)

class FunctionFieldFromLimitValuation(FiniteExtensionFromLimitValuation):
    r"""
    A valuation on a finite extensions of function fields `L=K[y]/(G)` where `K` is
    another function field.

    EXAMPLES::

        sage: from mac_lane import * # optional: standalone
        sage: K.<x> = FunctionField(QQ)
        sage: R.<y> = K[]
        sage: L.<y> = K.extension(y^2 - (x^2 + x + 1))
        sage: v = FunctionFieldValuation(K, x - 1) # indirect doctest
        sage: w = v.extension(L); w
        (x - 1)-adic valuation

    TESTS::

        sage: isinstance(w, FunctionFieldFromLimitValuation)
        True

    """
    def _to_base_domain(self, f):
        r"""
        Return ``f`` as an element of the domain of the underlying limit valuation.

        EXAMPLES::

            sage: from mac_lane import * # optional: standalone
            sage: K.<x> = FunctionField(QQ)
            sage: R.<y> = K[]
            sage: L.<y> = K.extension(y^2 - (x^2 + x + 1))
            sage: v = FunctionFieldValuation(K, x - 1) # indirect doctest
            sage: w = v.extension(L)
            sage: w._to_base_domain(y).parent()
            Univariate Polynomial Ring in y over Rational function field in x over Rational Field

        """
        return f.element()

    def scale(self, scalar):
        r"""
        Return this valuation scaled by ``scalar``.

        EXAMPLES::

            sage: from mac_lane import * # optional: standalone
            sage: K.<x> = FunctionField(QQ)
            sage: R.<y> = K[]
            sage: L.<y> = K.extension(y^2 - (x^2 + x + 1))
            sage: v = FunctionFieldValuation(K, x - 1) # indirect doctest
            sage: w = v.extension(L)
            sage: 3*w
            3 * (x - 1)-adic valuation

        """
        if scalar in QQ and scalar > 0 and scalar != 1:
            return FunctionFieldValuation(self.domain(), self._base_valuation._initial_approximation.scale(scalar))
        return super(FunctionFieldFromLimitValuation, self).scale(scalar)


class FunctionFieldMappedValuation_base(FunctionFieldValuation_base, MappedValuation_base):
    r"""
    A valuation on a function field which relies on a ``base_valuation`` on an
    isomorphic function field.

    EXAMPLES::
    
        sage: from mac_lane import * # optional: standalone
        sage: K.<x> = FunctionField(GF(2))
        sage: v = FunctionFieldValuation(K, 1/x); v
        Valuation at the infinite place

    """
    def __init__(self, parent, base_valuation, to_base_valuation_domain, from_base_valuation_domain):
        r"""
        TESTS::
    
            sage: from mac_lane import * # optional: standalone
            sage: K.<x> = FunctionField(GF(2))
            sage: v = FunctionFieldValuation(K, 1/x)
            sage: isinstance(v, FunctionFieldMappedValuation_base)
            True
    
        """
        FunctionFieldValuation_base.__init__(self, parent)
        MappedValuation_base.__init__(self, parent, base_valuation)

        self._to_base = to_base_valuation_domain
        self._from_base = from_base_valuation_domain

    def _to_base_domain(self, f):
        r"""
        Return ``f`` as an element in the domain of ``_base_valuation``.

        EXAMPLES::

            sage: from mac_lane import * # optional: standalone
            sage: K.<x> = FunctionField(GF(2))
            sage: R.<y> = K[]
            sage: L.<y> = K.extension(y^2 + y + x^3)
            sage: v = FunctionFieldValuation(K, 1/x)
            sage: w = v.extension(L)
            sage: w._to_base_domain(y)
            x^2*y

        """
        return self._to_base(f)

    def _from_base_domain(self, f):
        r"""
        Return ``f`` as an element in the domain of this valuation.

        EXAMPLES::

            sage: from mac_lane import * # optional: standalone
            sage: K.<x> = FunctionField(GF(2))
            sage: R.<y> = K[]
            sage: L.<y> = K.extension(y^2 + y + x^3)
            sage: v = FunctionFieldValuation(K, 1/x)
            sage: w = v.extension(L)
            sage: w._from_base_domain(w._to_base_domain(y))
            y

        r"""
        return self._from_base(f)

    def scale(self, scalar):
        r"""
        Return this valuation scaled by ``scalar``.

        EXAMPLES::

            sage: from mac_lane import * # optional: standalone
            sage: K.<x> = FunctionField(GF(2))
            sage: R.<y> = K[]
            sage: L.<y> = K.extension(y^2 + y + x^3)
            sage: v = FunctionFieldValuation(K, 1/x)
            sage: w = v.extension(L)
            sage: 3*w
            3 * (x)-adic valuation (in Rational function field in x over Finite Field of size 2 after x |--> 1/x)

        """
        from sage.rings.all import QQ
        if scalar in QQ and scalar > 0 and scalar != 1:
            return FunctionFieldValuation(self.domain(), (self._base_valuation.scale(scalar), self._to_base, self._from_base))
        return super(FunctionFieldMappedValuation_base, self).scale(scalar)

    def _repr_(self):
        r"""
        Return a printable representation of this valuation.

        EXAMPLES::

            sage: from mac_lane import * # optional: standalone
            sage: K.<x> = FunctionField(GF(2))
            sage: R.<y> = K[]
            sage: L.<y> = K.extension(y^2 + y + x^3)
            sage: v = FunctionFieldValuation(K, 1/x)
            sage: v.extension(L) # indirect doctest
            Valuation at the infinite place

        """
        to_base = repr(self._to_base)
        if hasattr(self._to_base, '_repr_defn'):
            to_base = self._to_base._repr_defn().replace('\n', ', ')
        return "%r (in %r after %s)"%(self._base_valuation, self._base_valuation.domain(), to_base)

class RationalFunctionFieldMappedValuation(FunctionFieldMappedValuation_base, RationalFunctionFieldValuation_base):
    r"""
    Valuation on a rational function field that is implemented after a map to
    an isomorphic (rational) function field.

    EXAMPLES::

        sage: from mac_lane import *
        sage: K.<x> = FunctionField(QQ)
        sage: R.<x> = QQ[]
        sage: w = GaussValuation(R, pAdicValuation(QQ, 2)).augmentation(x, 1)
        sage: w = FunctionFieldValuation(K, w)
        sage: v = FunctionFieldValuation(K, (w, K.hom([~K.gen()]), K.hom([~K.gen()]))); v
        Valuation on rational function field induced by [ Gauss valuation induced by 2-adic valuation, v(x) = 1 ] (in Rational function field in x over Rational Field after x |--> 1/x)

    """
    def __init__(self, parent, base_valuation, to_base_valuation_doain, from_base_valuation_domain):
        r"""
        TESTS::

            sage: from mac_lane import *
            sage: K.<x> = FunctionField(QQ)
            sage: R.<x> = QQ[]
            sage: w = GaussValuation(R, pAdicValuation(QQ, 2)).augmentation(x, 1)
            sage: w = FunctionFieldValuation(K, w)
            sage: v = FunctionFieldValuation(K, (w, K.hom([~K.gen()]), K.hom([~K.gen()])))
            sage: isinstance(v, RationalFunctionFieldMappedValuation)
            True

        """
        FunctionFieldMappedValuation_base.__init__(self, parent, base_valuation, to_base_valuation_doain, from_base_valuation_domain)
        RationalFunctionFieldValuation_base.__init__(self, parent)

class InfiniteRationalFunctionFieldValuation(FunctionFieldMappedValuation_base, RationalFunctionFieldValuation_base, ClassicalFunctionFieldValuation_base):
    r"""
    Valuation of the infinite place of a function field.

    EXAMPLES::

        sage: from mac_lane import * # optional: standalone
        sage: K.<x> = FunctionField(QQ)
        sage: v = FunctionFieldValuation(K, 1/x) # indirect doctest

    """
    def __init__(self, parent):
        r"""
        TESTS::

            sage: from mac_lane import * # optional: standalone
            sage: K.<x> = FunctionField(QQ)
            sage: v = FunctionFieldValuation(K, 1/x) # indirect doctest
            sage: isinstance(v, InfiniteRationalFunctionFieldValuation)
            True

        """
        x = parent.domain().gen()
        FunctionFieldMappedValuation_base.__init__(self, parent, FunctionFieldValuation(parent.domain(), x), parent.domain().hom([1/x]), parent.domain().hom([1/x]))
        RationalFunctionFieldValuation_base.__init__(self, parent)
        ClassicalFunctionFieldValuation_base.__init__(self, parent)

    def _repr_(self):
        r"""
        Return a printable representation of this valuation.

        EXAMPLES::

            sage: from mac_lane import * # optional: standalone
            sage: K.<x> = FunctionField(QQ)
            sage: FunctionFieldValuation(K, 1/x) # indirect doctest
            Valuation at the infinite place

        """
        return "Valuation at the infinite place"


class FunctionFieldExtensionMappedValuation(FunctionFieldMappedValuation_base):
    r"""
    A valuation on a finite extensions of function fields `L=K[y]/(G)` where `K` is
    another function field which redirects to another ``base_valuation`` on an
    isomorphism function field `M=K[y]/(H)`.

    The isomorphisms must be trivial on ``K``.

    EXAMPLES::

        sage: from mac_lane import * # optional: standalone
        sage: K.<x> = FunctionField(GF(2))
        sage: R.<y> = K[]
        sage: L.<y> = K.extension(y^2 + y + x^3)
        sage: v = FunctionFieldValuation(K, 1/x)
        sage: w = v.extension(L)

        sage: w(x)
        -1
        sage: w(y)
        -3/2
        sage: w.uniformizer()
        1/x^2*y

    TESTS::

        sage: isinstance(w, FunctionFieldExtensionMappedValuation)
        True

    """
    def _repr_(self):
        r"""
        Return a printable representation of this valuation.

        EXAMPLES::

            sage: from mac_lane import * # optional: standalone
            sage: K.<x> = FunctionField(GF(2))
            sage: R.<y> = K[]
            sage: L.<y> = K.extension(y^2 + y + x^3)
            sage: v = FunctionFieldValuation(K, 1/x)
            sage: w = v.extension(L); w
            Valuation at the infinite place

            sage: K.<x> = FunctionField(QQ)
            sage: R.<y> = K[]
            sage: L.<y> = K.extension(y^2 - 1/x^2 - 1)
            sage: v = FunctionFieldValuation(K, 1/x)
            sage: w = v.extensions(L); w
            [[ Valuation at the infinite place, v(y - 1) = 2 ]-adic valuation,
             [ Valuation at the infinite place, v(y + 1) = 2 ]-adic valuation]

        """
        assert(self.domain().base() is not self.domain())
        if repr(self._base_valuation) == repr(self.restriction(self.domain().base())):
            return repr(self._base_valuation)
        return super(FunctionFieldExtensionMappedValuation, self)._repr_()

    def restriction(self, ring):
        r"""
        Return the restriction of this valuation to ``ring``.

        EXAMPLES::

            sage: from mac_lane import * # optional: standalone
            sage: K.<x> = FunctionField(GF(2))
            sage: R.<y> = K[]
            sage: L.<y> = K.extension(y^2 + y + x^3)
            sage: v = FunctionFieldValuation(K, 1/x)
            sage: w = v.extension(L)
            sage: w.restriction(K) is v
            True

        """
        if ring.is_subring(self.domain().base()):
            return self._base_valuation.restriction(ring)
        return super(FunctionFieldMappedValuation, self).restriction(ring)
