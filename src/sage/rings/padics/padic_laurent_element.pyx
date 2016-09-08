r"""
Elements of two step extensions of `\mathbb{Q}_p` and `\mathbb{Z}_p` realized
as Laurent series or power series over the unramified first step.

AUTHORS:

- Julian Rueth (2012-10-23): initial version

"""
#*****************************************************************************
#       Copyright (C) 2012 Julian Rueth <julian.rueth@fsfe.org>
#
#  Distributed under the terms of the GNU General Public License (GPL)
#  as published by the Free Software Foundation; either version 2 of
#  the License, or (at your option) any later version.
#                  http://www.gnu.org/licenses/
#*****************************************************************************

from sage.rings.padics.padic_generic_element cimport pAdicGenericElement
from sage.rings.padics.padic_ext_element cimport pAdicExtElement
from sage.rings.infinity import infinity
from sage.misc.cachefunc import cached_method
from sage.rings.integer import Integer
from sage.structure.element cimport CommutativeRingElement
from sage.structure.element import is_Element
from sage.rings.padics.precision_error import PrecisionError

cdef long maxordp = (1L << (sizeof(long) * 8 - 2)) - 1

cdef class pAdicLaurentElement(pAdicExtElement):
    r"""
    Shared functionality of all elements of two step extension of
    `\mathbb{Q}_p` and `\mathbb{Z}_p` realized as Laurent series or power
    series over the unramified first step.

    EXAMPLES::

        sage: K = Qp(3,10)
        sage: R.<u> = K[]
        sage: L.<u> = K.extension(u^2 + 3*u + 4)
        sage: R.<a> = L[]
        sage: M = QpTwoStepExtensionFactory(L, a^3 - 9*u*a^2 + 3*u, ram_name="a"); a = M.uniformizer(); u = M(u)
        sage: a
        a + O(a^31)
        sage: u
        u + O(a^30)
        sage: M.zero()
        0

    Elements can be initialized from lists of elements of the residue field::

        sage: k = M.residue_field()
        sage: M([k.zero(),k.one(),k.gen(),k.one()])
        a + u*a^2 + a^3 + O(a^4)

    Elements can be initialized from elements of the base field::

        sage: M(K.one())
        1 + O(a^30)
        sage: M(K(3))
        u*a^3 + (u + 1)*a^6 + 2*a^8 + 2*a^9 + (u + 1)*a^11 + a^12 + u*a^13 + a^14 + a^15 + (2*u + 1)*a^16 + 2*a^17 + a^18 + (u + 2)*a^19 + u*a^20 + (2*u + 2)*a^21 + (u + 1)*a^22 + 2*a^23 + 2*a^24 + (2*u + 1)*a^25 + a^26 + (u + 2)*a^28 + (u + 1)*a^29 + u*a^30 + 2*u*a^31 + u*a^32 + O(a^33)
        sage: M(K(1/3))
        2*u*a^-3 + 1 + 2*a^2 + 2*u*a^7 + (2*u + 2)*a^10 + 2*a^12 + a^13 + u*a^15 + (u + 2)*a^16 + 2*u*a^17 + u*a^19 + (2*u + 2)*a^20 + u*a^21 + (u + 1)*a^22 + 2*u*a^23 + (u + 1)*a^25 + u*a^26 + O(a^27)
        sage: M(K(3^10))
        2*a^30 + (u + 1)*a^33 + 2*u*a^35 + 2*u*a^36 + u*a^38 + 2*a^40 + 2*a^41 + u*a^42 + (2*u + 1)*a^43 + a^45 + (2*u + 2)*a^46 + a^47 + a^48 + (u + 2)*a^49 + (2*u + 1)*a^50 + (u + 2)*a^51 + (u + 1)*a^52 + (u + 1)*a^53 + (2*u + 1)*a^54 + (u + 1)*a^55 + (2*u + 1)*a^56 + (2*u + 2)*a^57 + (u + 2)*a^58 + (u + 2)*a^59 + O(a^60)

    """
    def __init__(self, parent, x, absprec = None):
        """
        Initializes ``self`` from ``x``.

        INPUT:

            - ``parent`` -- the parent of ``self``

            - ``x`` -- an element from which ``self`` can be initialized

            - ``absprec`` -- integer or ``None`` (default: None), reduce the
              precision of ``self`` to that value if not ``None``

        AUTHORS:

        - Julian Rueth (2012-10-23): initial version

        EXAMPLES::

            sage: K = Qp(3,10)
            sage: R.<u> = K[]
            sage: L.<u> = K.extension(u^2 + 3*u + 4)
            sage: R.<a> = L[]
            sage: M = QpTwoStepExtensionFactory(L, a^3 - 9*u*a^2 + 3*u, ram_name="a"); a = M.uniformizer(); u = M(u)
            sage: M(None)
            0
            sage: M(None,3)
            O(a^3)

        """
        pAdicExtElement.__init__(self, parent)

        if x is None or ( is_Element(x) and x.parent() is self.parent().base_ring() and x._is_exact_zero() ):
            ls = self.__series_ring().zero()
            if absprec is not None:
                ls = ls.add_bigoh(absprec)
            self.__set_from_laurent_series(ls)
        elif is_Element(x) and x.parent() is self.parent():
            if absprec is not None:
                ls = x._series_raw().add_bigoh(absprec)
            self.__set_from_laurent_series(ls)
        elif is_Element(x) and x.parent() is self.parent().residue_field():
            ls = self.parent()(self.parent().inertia_subring()(x))._series_raw()
            if absprec is not None:
                ls = ls.add_bigoh(absprec)
            ls = ls.add_bigoh(1)
            self.__set_from_laurent_series(ls)
        elif is_Element(x) and (x.parent() is self.parent().base_ring() or x.parent() is self.parent().inertia_subring()):
            val = x.valuation()
            if val<0:
                x >>= val
            ls = self.__series_ring()(x)
            if parent.is_capped_relative() or parent.is_capped_absolute():
                ls = ls.add_bigoh(x.precision_absolute()*parent.ramification_index())
            if parent.is_capped_relative():
                ls = ls.add_bigoh(x.valuation()*parent.ramification_index()+self.parent().precision_cap())
            if absprec is not None:
                ls = ls.add_bigoh(absprec)
            self.__set_from_laurent_series(ls)
            if val<0:
                tmp = self/(parent.base_ring().uniformizer_pow(-val))
                self.__set_from_laurent_series(tmp._series_raw())
        elif isinstance(x,list):
            if all([c in self.parent().residue_field() for c in x]):
                ls = self.__series_ring()([self.parent()._inertia_subring(c).lift_to_precision(self.parent()._inertia_subring.precision_cap()) for c in x])
                if parent.is_capped_relative() or parent.is_capped_absolute():
                    ls = ls.add_bigoh(len(x))
                if parent.is_capped_relative():
                    ls = ls.add_bigoh(ls.valuation()+self.parent().precision_cap())
                if absprec is not None:
                    ls = ls.add_bigoh(absprec)
                self.__set_from_laurent_series(ls)
            else:
                raise NotImplementedError("initialization from %s"%x)
        else:
            raise NotImplementedError("initialization from %s"%x)

    def __set_from_laurent_series(self, ls):
        """
        Initializes ``self`` from the Laurent series ``ls``.

        INPUT:

            - ``ls`` -- a Laurent series over the maximal unramified
              subextension of ``self``

        EXAMPLES::

            sage: K = Qp(3,10)
            sage: R.<u> = K[]
            sage: L.<u> = K.extension(u^2 + 3*u + 4)
            sage: R.<a> = L[]
            sage: M = QpTwoStepExtensionFactory(L, a^3 - 9*u*a^2 + 3*u, ram_name="a"); a = M.uniformizer(); u = M(u)
            sage: x = M(None)
            sage: x.__set_from_laurent_series(x.__series_ring().one().add_bigoh(3))
            sage: x
            1 + O(a^3)

        """
        self.__series_start = 0
        self.__series_raw = ls
        self.__series_developed = None
        self.__series_relative = None
        self.__series_valuation = None

    def __series_ring(self):
        """
        Returns the Laurent/power series ring underlying the implementation of
        ``self``.

        EXAMPLES::

            sage: K = Qp(3,10)
            sage: R.<u> = K[]
            sage: L.<u> = K.extension(u^2 + 3*u + 4)
            sage: R.<a> = L[]
            sage: M = QpTwoStepExtensionFactory(L, a^3 - 9*u*a^2 + 3*u, ram_name="a"); a = M.uniformizer(); u = M(u)
            sage: M.gen().__series_ring()
            Laurent Series Ring in a over Unramified Extension in u defined by (1 + O(3^10))*u^2 + (3 + O(3^10))*u + 1 + 3 + O(3^10) of 3-adic Field with capped relative precision 10

        """
        from sage.rings.laurent_series_ring import LaurentSeriesRing
        return LaurentSeriesRing(self.parent()._inertia_subring, name=self.parent().variable_names()[1])

    cpdef bint _is_inexact_zero(self) except -1:
        """
        Return True if ``self`` is indistinguisable from zero but has finite
        valuation.

        EXAMPLES::

            sage: K = Qp(3,10)
            sage: R.<u> = K[]
            sage: L.<u> = K.extension(u^2 + 3*u + 4)
            sage: R.<a> = L[]
            sage: M = QpTwoStepExtensionFactory(L, a^3 - 9*u*a^2 + 3*u, ram_name="a"); a = M.uniformizer(); u = M(u)
            sage: u._is_inexact_zero()
            False
            sage: a._is_inexact_zero()
            False
            sage: M(0,3)._is_inexact_zero()
            True
            sage: M.zero()._is_inexact_zero()
            False

        """
        return self.valuation() == self.precision_absolute() and not self.valuation() is infinity

    cpdef bint _is_exact_zero(self) except -1:
        """
        Return True if ``self`` has infinite valuation.

        EXAMPLES::

            sage: K = Qp(3,10)
            sage: R.<u> = K[]
            sage: L.<u> = K.extension(u^2 + 3*u + 4)
            sage: R.<a> = L[]
            sage: M = QpTwoStepExtensionFactory(L, a^3 - 9*u*a^2 + 3*u, ram_name="a"); a = M.uniformizer(); u = M(u)
            sage: u._is_exact_zero()
            False
            sage: a._is_exact_zero()
            False
            sage: M(0,3)._is_exact_zero()
            False
            sage: M.zero()._is_exact_zero()
            True

        """
        return self.valuation() is infinity

    cdef long valuation_c(self):
        """
        Returns the valuation of ``self`` or ``maxordp`` if it is infinite.

        EXAMPLES::

            sage: K = Qp(3,10)
            sage: R.<u> = K[]
            sage: L.<u> = K.extension(u^2 + 3*u + 4)
            sage: R.<a> = L[]
            sage: M = QpTwoStepExtensionFactory(L, a^3 - 9*u*a^2 + 3*u, ram_name="a"); a = M.uniformizer(); u = M(u)
            sage: a.valuation() # indirect doctest
            1
            sage: u.valuation()
            0
            sage: M(0,3).valuation()
            3
            sage: M.zero().valuation()
            +Infinity

        """
        if self._series_raw().is_zero():
            ret = self.precision_absolute()
        else:
            ls = self._series_valuation()
            if ls.is_zero():
                ret = self.precision_absolute()
            else:
                ret = ls.valuation()

        if ret is infinity:
            assert self.parent().is_capped_relative()
            return maxordp
        else:
            assert self.parent().is_capped_relative() or ret <= self.parent().precision_cap()
            return int(ret)

    def vector(self, base=None):
        if base is None:
            base = self.parent().base()
        if base is self.parent().inertia_subring():
            ret = [base.zero()]*self._series_compressed().valuation()+self._series_compressed().list()
            assert all([c.is_zero() for c in ret[self.parent().ramification_index():]])
            ret = ret[:self.parent().ramification_index()]
            ret = ret+[self.parent().inertia_subring().zero()]*(self.parent().ramification_index()-len(ret))
            from sage.rings.infinity import infinity
            ret = [c.add_bigoh((self.precision_absolute() if self.precision_absolute() is not infinity else self.parent().precision_cap())//self.parent().ramification_index()) for c in ret]
            return ret
        elif base is self.parent().ground_ring_of_tower():
            from itertools import chain
            return list(chain(*[c.vector(base=base) for c in self.vector(base=self.parent().inertia_subring())]))
        else:
            raise ValueError

    def polynomial(self):
        from sage.rings.all import PolynomialRing
        D = {}
        for e in range(self.parent().ramification_index()):
            for u in range(self.parent().inertia_subring().degree()):
                D[(u,e)] = self._series_compressed()[e].polynomial()[u]
        return PolynomialRing(self.parent().base(), names=self.parent().variable_names())(D)

    def matrix(self, base=None):
        """
        If ``base`` is ``None``, return the element, as a `1\times 1` matrix.

        If ``base`` is not ``None``, then ``base`` must be either a field that
        embeds into the field where the element is defined or a morphism into
        that field, in which case this function returns the matrix of
        multiplication on the power basis, where we view the parent
        field as a field over ``base``.

        INPUT:

            ``base`` -- field or morphism or ``None`` (default: ``None``)

        EXAMPLES::

            sage: K = Qp(3,10)
            sage: R.<u> = K[]
            sage: L.<u> = K.extension(u^2 + 3*u + 4)
            sage: R.<a> = L[]
            sage: M = QpTwoStepExtensionFactory(L, a^3 - 9*u*a^2 + 3*u, ram_name="a"); a = M.uniformizer(); u = M(u)
            sage: a.matrix() # known bug - too much precision
            [a + O(a^13)]
            sage: a.matrix(base=K) # known bug - too much precision
            [                              O(3^4)                               O(3^4)                           1 + O(3^4)                               O(3^4)                               O(3^4)                               O(3^4)]
            [                              O(3^4)                               O(3^4)                               O(3^4)                           1 + O(3^4)                               O(3^4)                               O(3^4)]
            [                              O(3^4)                               O(3^4)                               O(3^4)                               O(3^4)                           1 + O(3^4)                               O(3^4)]
            [                              O(3^4)                               O(3^4)                               O(3^4)                               O(3^4)                               O(3^4)                           1 + O(3^4)]
            [                              O(3^5) 2*3 + 2*3^2 + 2*3^3 + 2*3^4 + O(3^5)                               O(3^5)                               O(3^5)                               O(3^5)                         3^2 + O(3^5)]
            [                    3 + 3^2 + O(3^5)                         3^2 + O(3^5)                               O(3^5)                               O(3^5)         2*3^2 + 3^3 + 2*3^4 + O(3^5)               2*3^3 + 2*3^4 + O(3^5)]
            sage: a.matrix(base=M.inertia_subring()) # known bug - too much precision
            [                                      O(3^4)                                   1 + O(3^4)                                       O(3^4)]
            [                                      O(3^4)                                       O(3^4)                                   1 + O(3^4)]
            [2*u*3 + 2*u*3^2 + 2*u*3^3 + 2*u*3^4 + O(3^5)                                       O(3^5)                               u*3^2 + O(3^5)]

        """
        from sage.matrix.all import matrix

        if base is None or base is self.parent():
            return matrix(self.parent(),1,1,[self])
        elif base is self.parent().inertia_subring():
            ret = [(self*self.parent().gen(1)**i).vector(base) for i in range(self.parent().ramification_index())]
            return matrix(base,self.parent().ramification_index(),self.parent().ramification_index(), ret)
        elif base is self.parent().ground_ring_of_tower():
            ret = [(self*self.parent().gen(0)**i*self.parent().gen(1)**j).vector(base) for j in range(self.parent().ramification_index()) for i in range(self.parent().degree()//self.parent().ramification_index())]
            return matrix(base,self.parent().degree(),self.parent().degree(),ret)
        else:
            raise NotImplementedError

    cdef ext_p_list(self, bint pos):
        """
        Returns a list of lists of integers. ``self`` can be reconstructed as a
        sum of powers of the uniformizer times polynomials in the generator of
        the unramified subextension.

        Note that zeros are truncated from the returned list, so you must use
        the :meth:`valuation` function to completely recover ``self``.

        INPUT:

            - pos -- bint.  If ``True``, all integers will be in the range
              [0,p-1], otherwise they will be in the range [(1-p)/2, p/2].

        OUTPUT:

        A list of lists giving the series expansion of ``self``

        AUTHORS:

        - Julian Rueth (2012-10-23): initial version

        EXAMPLES::

            sage: K = Qp(3,10)
            sage: R.<u> = K[]
            sage: L.<u> = K.extension(u^2 + 3*u + 4)
            sage: R.<a> = L[]
            sage: M = QpTwoStepExtensionFactory(L, a^3 - 9*u*a^2 + 3*u, ram_name="a"); a = M.uniformizer(); u = M(u)
            sage: a._ext_p_list(False) #indirect doctest
            [[1], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], []]
            sage: u._ext_p_list(False)
            [[0, 1], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], []]
            sage: M(0,3)._ext_p_list(False)
            []

        """
        p = self.parent().prime()

        ret = []
        for i in range(self.valuation(),self.precision_absolute()):
            term = self._series_developed()[i].list()
            if len(term) == 0:
                ret.append([])
            else:
                term = term[0]
                if not pos:
                    term = [ c if c<=p/2 else c-p for c in term ]
                ret.append(term)
        return ret

    def precision_absolute(self):
        """
        The precision to which ``self`` is accurate.

        OUTPUT:

        An integer or infinity.

        EXAMPLES::

            sage: K = Qp(3,10)
            sage: R.<u> = K[]
            sage: L.<u> = K.extension(u^2 + 3*u + 4)
            sage: R.<a> = L[]
            sage: M = QpTwoStepExtensionFactory(L, a^3 - 9*u*a^2 + 3*u, ram_name="a"); a = M.uniformizer(); u = M(u)
            sage: a.precision_absolute()
            31
            sage: u.precision_absolute()
            30
            sage: M(0,3).precision_absolute()
            3
            sage: M.zero().precision_absolute()
            +Infinity

        """
        return self._series_raw().prec()

    def precision_relative(self):
        if self.precision_absolute() is infinity:
            return infinity
        return self.precision_absolute() - self.valuation()

    def _series_raw(self):
        """
        Returns a Laurent series defining ``self``.

        OUTPUT:

        A Laurent series over the maximal unramified subextension of
        ``self.parent()`` which represents ``self``. Initially, this is the
        Laurent series that was used to initialize ``self``. Later, however,
        calls to :meth:`_series_developed` and :meth:`_series_valuation`, can
        change the return value.

        .. SEEALSO::

            :meth:`_series_developed`, :meth:`_series_valuation`

        EXAMPLES::

            sage: K = Qp(3,10)
            sage: R.<u> = K[]
            sage: L.<u> = K.extension(u^2 + 3*u + 4)
            sage: R.<a> = L[]
            sage: M = QpTwoStepExtensionFactory(L, a^3 - 9*u*a^2 + 3*u, ram_name="a"); a = M.uniformizer(); u = M(u)
            sage: a._series_raw()
            (1 + O(3^10))*a + O(a^31)
            sage: u._series_raw()
            (u + O(3^10)) + O(a^30)
            sage: M(0,3)._series_raw()
            O(a^3)
            sage: M.zero()._series_raw()
            0

        """
        return self.__series_raw

    def _series_valuation(self, prec = None):
        """
        Compute a Laurent series defining ``self`` such that at least its first
        non-zero coefficient has valuation zero.

        INPUT:

            - ``prec`` -- an integer or ``None`` (default: ``None``), up to
              which index we try to find a coefficient of valuation zero.

        OUTPUT:

        A Laurent series over the maximal unramified subextension of
        ``self.parent()`` which represents ``self``.

        .. SEEALSO::

            :meth:`_series_developed`, :meth:`_series_raw`

        AUTHORS:

        - Julian Rueth (2012-10-23): initial version

        EXAMPLES::

            sage: K = Qp(3,10)
            sage: R.<u> = K[]
            sage: L.<u> = K.extension(u^2 + 3*u + 4)
            sage: R.<a> = L[]
            sage: M = QpTwoStepExtensionFactory(L, a^3 - 9*u*a^2 + 3*u, ram_name="a"); a = M.uniformizer(); u = M(u)
            sage: a._series_valuation()
            (1 + O(3^10))*a + O(a^31)
            sage: u._series_valuation()
            (u + O(3^10)) + O(a^30)
            sage: M(0,3)._series_valuation()
            O(a^3)
            sage: M.zero()._series_valuation()
            0

        """
        if self.__series_valuation is None:
            if prec is not None:
                self.__series_raw, self.__series_start = self.__develop(self.__series_raw, self.__series_start, True, prec)
                return self.__series_raw

            self.__series_valuation, self.__series_start = self.__develop(self._series_raw(), self.__series_start, True)
            self.__series_raw = self.__series_valuation
        return self.__series_valuation

    def _cache_key(self):
        s = self._series_developed()
        return tuple(s.list()),s.valuation(),s.prec(),self.parent()

    def _series_compressed(self):
        if self.__series_compressed is None:
            self.__series_compressed = self.__compress(self._series_developed())
            if self.__develop(self.__series_compressed)[0] != self._series_developed():
                print "WARNING: %s develops in %s to\n %s and compresses to\n %s but redeveloping it gives\n %s i.e. there has been an error of at most pi^%s"%(self,self.parent(),self.__series_developed,self.__series_compressed,self.__develop(self.__series_compressed)[0],(self.__series_developed-self.__develop(self.__series_compressed)[0]).valuation())
        return self.__series_compressed

    def _series_developed(self, prec = None):
        """
        Compute a Laurent series defining ``self`` such that no coefficient has
        finite non-zero valuation.

        INPUT:

            - ``prec`` -- an integer or ``None`` (default: ``None``), up to
              which index the coefficients will have no finite non-zero
              valuation. If ``None`` then no coefficients will have finite
              non-zero valuation.

        OUTPUT:

        A Laurent series over the maximal unramified subextension of
        ``self.parent()`` which represents ``self``.

        .. SEEALSO::

            :meth:`_series_valuation`, :meth:`_series_raw`

        AUTHORS:

        - Julian Rueth (2012-10-23): initial version

        EXAMPLES::

            sage: K = Qp(3,10)
            sage: R.<u> = K[]
            sage: L.<u> = K.extension(u^2 + 3*u + 4)
            sage: R.<a> = L[]
            sage: M = QpTwoStepExtensionFactory(L, a^3 - 9*u*a^2 + 3*u, ram_name="a"); a = M.uniformizer(); u = M(u)
            sage: a._series_developed()
            (1 + O(3^10))*a + O(a^31)
            sage: u._series_developed()
            (u + O(3^10)) + O(a^30)
            sage: M(0,3)._series_developed()
            O(a^3)
            sage: M.zero()._series_developed()
            0

        """
        if self.__series_developed is None:
            if prec is not None:
                self.__series_raw, self.__series_start = self.__develop(self.__series_raw, self.__series_start, False, prec)
                if self.__series_valuation is not None:
                    self.__series_valuation = self.__series_raw
                return self.__series_raw

            self.__series_developed, self.__series_start = self.__develop(self._series_valuation(), self.__series_start)
            self.__series_valuation = self.__series_developed
            self.__series_raw = self.__series_developed
            assert all([c.precision_absolute()>=1 for c in self.__series_developed]),"%s"%self.__series_developed
            assert all([c.is_zero() or c.valuation()==0 for c in self.__series_developed]),"%s"%self.__series_developed
        return self.__series_developed

    def __develop(self, x, start = 0, valuation_only = False, max_prec = None):
        """
        Helper method which expands a Laurent series over the maximal
        unramified subextension of ``self.parent()`` in such a way that no
        coefficient has finite non-zero valuation.

        INPUT:

            - ``x`` -- a Laurent series over the maximal unramified
              subextension of ``self.parent()``

            - ``start`` -- a non-negative integer (default: 0), index up to
              which ``x`` is already of the form that no coefficient has finite
              non-zero valuation

            - ``valuation_only`` -- (default: ``False``), whether or not to
              stop the expansion once we found an coefficient with valuation
              zero, i.e.  once we know the valuation of ``x``

            - ``max_prec`` -- an integer or ``None`` (default: ``None``), at
              which index to stop expansion or ``None`` in which case we expand
              up to absolute precision of ``self``

        OUTPUT:

        A Laurent series which is equal to ``x`` modulo the Eisenstein
        polynomial defining the extension of ``self.parent()``, and a new value
        for ``start``.

        AUTHORS:

        - Julian Rueth (2012-10-23): initial version

        EXAMPLES::

            sage: K = Qp(3,10)
            sage: R.<u> = K[]
            sage: L.<u> = K.extension(u^2 + 3*u + 4)
            sage: R.<a> = L[]
            sage: M = QpTwoStepExtensionFactory(L, a^3 - 9*u*a^2 + 3*u, ram_name="a"); a = M.uniformizer(); u = M(u)
            sage: L = M.gen().__series_ring()
            sage: ls = L(3).add_bigoh(20); ls
            (3 + O(3^11)) + O(a^20)
            sage: a.__develop(ls,valuation_only=True)
            ((u + O(3^10))*a^3 + (3^3 + 3^12 + O(3^13))*a^4 + (u*3 + (u + 2)*3^2 + (u + 1)*3^3 + (u + 1)*3^4 + (u + 1)*3^5 + (u + 1)*3^6 + (u + 1)*3^7 + (u + 1)*3^8 + (u + 1)*3^9 + 3^10 + O(3^11))*a^5 + ((u + 1) + u*3 + (2*u + 2)*3^2 + (2*u + 1)*3^3 + u*3^5 + (2*u + 2)*3^6 + (2*u + 1)*3^7 + 2*u*3^9 + O(3^10))*a^6 + O(a^20), 1)
            sage: a.__develop(ls)
            ((u + O(3^10))*a^3 + ((u + 1) + O(3^10))*a^6 + (2 + O(3^10))*a^8 + (2 + O(3^10))*a^9 + ((u + 1) + O(3^10))*a^11 + (1 + O(3^10))*a^12 + (u + O(3^10))*a^13 + (1 + O(3^10))*a^14 + (1 + O(3^10))*a^15 + ((2*u + 1) + O(3^10))*a^16 + (2 + O(3^10))*a^17 + (1 + O(3^10))*a^18 + ((u + 2) + O(3^10))*a^19 + O(a^20), 19)

        """
        # handle exact and inexact zeros
        if x.prec() is infinity:
            assert x.is_zero()
            return x, start
        if x.is_zero():
            return x, start

        cdef int valuation = x.valuation()
        cdef int precision = x.prec()

        if max_prec is not None and valuation >= max_prec:
            return x, start

        cdef int parent_precision_cap = self.parent().base_ring().precision_cap()
        cdef CommutativeRingElement parent_zero = self.parent().base_ring().zero()
        cdef CommutativeRingElement parent_approx_zero = parent_zero.add_bigoh(parent_precision_cap)

        # we rewrite the defining polynomial of the Eisenstein step such that
        # we can use it to expand the Laurent series
        R = self.__series_ring()
        replacement = R(self.parent()._epoly.map_coefficients(lambda c:self.parent()._inertia_subring(c).lift_to_precision(),self.parent()._inertia_subring))
        replacement *= replacement[0].unit_part().inverse_of_unit().lift_to_precision()
        replacement *= -1
        replacement = replacement.power_series()
        # this dict tells us how to realize p in terms of the uniformizer
        replacement = replacement.dict()
        del(replacement[0])
        # replacements_e are the powers of the uniformizer that we need to use
        # to realize p
        cdef list replacements_e = replacement.keys()
        replacements_e.reverse()
        # replacements_v are the coefficients of these powers
        cdef list replacements_v = replacement.values()
        replacements_v.reverse()
        cdef int rlen = len(replacements_e)

        cdef CommutativeRingElement c, zero, pos
        cdef list C = x.list()
        cdef int max_len_C = precision-valuation
        cdef int cur_len_C = len(C)
        cdef int d
        cdef int e
        cdef int ri

        cdef int max_d = max_len_C if max_prec is None else min(max_len_C,max_prec-valuation+1)

        # we iterate through the Laurent series and expand coefficients with
        # positive valuation
        for d in range(start,max_d):
            if d >= cur_len_C:
                break
            c = C[d]
            if c.is_zero():
                C[d] = parent_zero
                continue
            # split every coefficient in its valuation zero part and its part
            # of positive valuation
            zero = c[0:1].lift_to_precision()
            pos = (c[1:]>>1).lift_to_precision()
            C[d] = zero
            if not pos.is_zero():
                # expand the positive part
                for ri in range(rlen):
                    e = replacements_e[ri]
                    v = replacements_v[ri]
                    if d+e >= cur_len_C:
                        C.extend([parent_zero]*(d+e-cur_len_C+1))
                        cur_len_C = len(C)
                    C[d+e] += pos*v
            if zero.is_zero():
                C[d] = parent_zero
            elif valuation_only:
                d = 1
                break

        ret = R(C)<<x.valuation()
        ret = ret.add_bigoh(x.prec())
        return ret, d

    def __compress(self, x):
        # handle exact and inexact zeros
        if x.prec() is infinity:
            assert x.is_zero()
            return x
        if x.is_zero():
            return x

        cdef int valuation = x.valuation()
        cdef int precision = x.prec()

        cdef int parent_precision_cap = self.parent().base_ring().precision_cap()
        cdef CommutativeRingElement parent_zero = self.parent().base_ring().zero()
        cdef CommutativeRingElement parent_approx_zero = parent_zero.add_bigoh(parent_precision_cap)

        cdef int ram_index = self.parent().ramification_index()

        # we rewrite the defining polynomial of the Eisenstein step such that
        # we can use it to expand the Laurent series
        R = self.__series_ring()
        replacement = self.parent()._epoly.map_coefficients(lambda c:self.parent()._inertia_subring(c).lift_to_precision(),self.parent()._inertia_subring)
        assert replacement.leading_coefficient().is_unit()
        replacement *= replacement.leading_coefficient().inverse_of_unit().lift_to_precision()
        replacement *= -1
        replacement = R(replacement)
        replacement = replacement.power_series()
        # this dict tells us how to realize pi^e in terms of the uniformizer
        replacement = replacement.dict()
        del(replacement[ram_index])
        # replacements_e are the powers of the uniformizer that we need to use
        # to realize pi^ram_index
        cdef list replacements_e = replacement.keys()
        replacements_e.reverse()
        # replacements_v are the coefficients of these powers
        cdef list replacements_v = replacement.values()
        replacements_v.reverse()
        cdef int rlen = len(replacements_e)

        cdef CommutativeRingElement c
        cdef list C = x.list()
        C = [self.parent()._inertia_subring.zero()]*x.valuation() + C
        cdef int len_C = len(C)
        cdef int d
        cdef int e
        cdef int ri

        # we iterate through the Laurent series and unexpand coefficients
        for d in range(len_C-1,ram_index-1,-1):
            c = C[d]
            C[d] = parent_zero
            if not c.is_zero():
                # unexpand c
                for ri in range(rlen):
                    e = replacements_e[ri]
                    v = replacements_v[ri]
                    C[d-ram_index+e] += c*v
        ret = R(C)
        ret = ret.add_bigoh(x.prec())
        return ret

    cpdef _add_(self, right):
        """
        Compute the sum of ``self`` and ``right``.

        INPUT:

            - ``right`` -- an element of the same parent as ``self``

        OUTPUT:

        An element in the same parent as ``self``, the sum of ``self`` and
        ``right``.

        EXAMPLES::

            sage: K = Qp(3,10)
            sage: R.<u> = K[]
            sage: L.<u> = K.extension(u^2 + 3*u + 4)
            sage: R.<a> = L[]
            sage: M = QpTwoStepExtensionFactory(L, a^3 - 9*u*a^2 + 3*u, ram_name="a"); a = M.uniformizer(); u = M(u)
            sage: a + u
            u + a + O(a^30)
            sage: a + a
            2*a + O(a^31)
            sage: a + a + a
            u*a^4 + (u + 1)*a^7 + 2*a^9 + 2*a^10 + (u + 1)*a^12 + a^13 + u*a^14 + a^15 + a^16 + (2*u + 1)*a^17 + 2*a^18 + a^19 + (u + 2)*a^20 + u*a^21 + (2*u + 2)*a^22 + (u + 1)*a^23 + 2*a^24 + 2*a^25 + (2*u + 1)*a^26 + a^27 + (u + 2)*a^29 + (u + 1)*a^30 + O(a^31)

        """
        ret = self.parent()(None)
        ret.__set_from_laurent_series(self._series_raw() + right._series_raw())
        return ret

    cpdef _neg_(self):
        """
        Compute ``-self``.

        OUTPUT:

        An element of the same parent as ``self``.

        EXAMPLES::

            sage: K = Qp(3,10)
            sage: R.<u> = K[]
            sage: L.<u> = K.extension(u^2 + 3*u + 4)
            sage: R.<a> = L[]
            sage: M = QpTwoStepExtensionFactory(L, a^3 - 9*u*a^2 + 3*u, ram_name="a"); a = M.uniformizer(); u = M(u)
            sage: a - u
            2*u + a + a^3 + u*a^8 + (u + 1)*a^11 + a^13 + 2*a^14 + 2*u*a^16 + a^17 + u*a^18 + 2*a^19 + a^20 + (u + 1)*a^21 + 2*a^22 + a^23 + (u + 2)*a^25 + (u + 1)*a^26 + (2*u + 2)*a^27 + 2*a^28 + (u + 2)*a^29 + O(a^30)
            sage: a - a
            O(a^31)

        """
        ret = self.parent()(None)
        ret.__set_from_laurent_series(-self._series_raw())
        return ret

    def is_unit(self):
        """
        Returns whether ``self`` is a unit in ``self.parent()``.

        EXAMPLES::

            sage: K = Qp(3,10)
            sage: R.<u> = K[]
            sage: L.<u> = K.extension(u^2 + 3*u + 4)
            sage: R.<a> = L[]
            sage: M = QpTwoStepExtensionFactory(L, a^3 - 9*u*a^2 + 3*u, ram_name="a"); a = M.uniformizer(); u = M(u)
            sage: a.is_unit()
            True
            sage: u.is_unit()
            True
            sage: M.zero().is_unit()
            False
            sage: M(0,3).is_unit()
            False

        """
        return (self.parent().is_field() and not self.is_zero()) or self.valuation()==0

    def __invert__(self):
        """
        Compute a multiplicative inverse of ``self``.

        OUTPUT:

        An element in the parent of ``self``. Raises an ``NotImplementedError``
        if ``self`` is not a unit.

        EXAMPLES::

            sage: K = Qp(3,10)
            sage: R.<u> = K[]
            sage: L.<u> = K.extension(u^2 + 3*u + 4)
            sage: R.<a> = L[]
            sage: M = QpTwoStepExtensionFactory(L, a^3 - 9*u*a^2 + 3*u, ram_name="a"); a = M.uniformizer(); u = M(u)
            sage: ~a
            a^-1 + O(a^29)
            sage: ~a*a
            1 + O(a^30)
            sage: ~u
            2*u + 2*u*a^3 + 2*a^6 + a^8 + (2*u + 2)*a^9 + (u + 2)*a^12 + 2*u*a^13 + 2*a^14 + (u + 2)*a^15 + (2*u + 1)*a^16 + 2*a^17 + 2*a^18 + u*a^19 + 2*u*a^20 + 2*u*a^21 + (2*u + 2)*a^22 + u*a^23 + a^24 + (u + 2)*a^26 + 2*u*a^27 + a^28 + 2*a^29 + O(a^30)
            sage: ~u*u
            1 + O(a^30)
            sage: ~M(0,3)
            Traceback (most recent call last):
            ...
            NotImplementedError: cannot invert non-units
            sage: ~M(3) - M(~3)
            O(a^27)

        TESTS:

        We test that this also works for other base rings::

            sage: K = ZpCA(3,10)
            sage: R.<u> = K[]
            sage: L.<u> = K.extension(u^2 + 3*u + 4)
            sage: R.<a> = L[]
            sage: M = ZpTwoStepExtensionFactory(L, a^3 - 9*u*a^2 + 3*u, ram_name="a"); a = M.uniformizer(); u = M(u)
            sage: ~a
            Traceback (most recent call last):
            ...
            NotImplementedError: cannot invert non-units
            sage: ~u
            2*u + 2*u*a^3 + 2*a^6 + a^8 + (2*u + 2)*a^9 + (u + 2)*a^12 + 2*u*a^13 + 2*a^14 + (u + 2)*a^15 + (2*u + 1)*a^16 + 2*a^17 + 2*a^18 + u*a^19 + 2*u*a^20 + 2*u*a^21 + (2*u + 2)*a^22 + u*a^23 + a^24 + (u + 2)*a^26 + 2*u*a^27 + a^28 + 2*a^29 + O(a^30)

            sage: K = ZpFM(3,10)
            sage: R.<u> = K[]
            sage: L.<u> = K.extension(u^2 + 3*u + 4)
            sage: R.<a> = L[]
            sage: M = ZpTwoStepExtensionFactory(L, a^3 - 9*u*a^2 + 3*u, ram_name="a"); a = M.uniformizer(); u = M(u)
            sage: ~a
            Traceback (most recent call last):
            ...
            NotImplementedError: cannot invert non-units
            sage: ~u
            2*u + 2*u*a^3 + 2*a^6 + a^8 + (2*u + 2)*a^9 + (u + 2)*a^12 + 2*u*a^13 + 2*a^14 + (u + 2)*a^15 + (2*u + 1)*a^16 + 2*a^17 + 2*a^18 + u*a^19 + 2*u*a^20 + 2*u*a^21 + (2*u + 2)*a^22 + u*a^23 + a^24 + (u + 2)*a^26 + 2*u*a^27 + a^28 + 2*a^29 + O(a^30)

        """
        if not self.is_unit():
            raise NotImplementedError("cannot invert non-units")
        ret = self.parent()(None)
        ret.__set_from_laurent_series(~self._series_developed())
        return ret

    cpdef _div_(self, other):
        """
        Return the result of ``self`` divided by ``other``.

        INPUT:

            - ``other`` -- an element in the same ring as ``self``

        OUTPUT:

        An element in the same ring as ``self``. Raises a
        ``NotImplementedError`` if ``other`` is not invertible in the parent of
        ``other``.

        EXAMPLES::

            sage: K = Qp(3,10)
            sage: R.<u> = K[]
            sage: L.<u> = K.extension(u^2 + 3*u + 4)
            sage: R.<a> = L[]
            sage: M = QpTwoStepExtensionFactory(L, a^3 - 9*u*a^2 + 3*u, ram_name="a"); a = M.uniformizer(); u = M(u)
            sage: a/a
            1 + O(a^30)
            sage: a/u/a*u
            1 + O(a^30)

        TESTS:

        We test that this also works for other base rings::

            sage: K = ZpCA(3,10)
            sage: R.<u> = K[]
            sage: L.<u> = K.extension(u^2 + 3*u + 4)
            sage: R.<a> = L[]
            sage: M = ZpTwoStepExtensionFactory(L, a^3 - 9*u*a^2 + 3*u, ram_name="a"); a = M.uniformizer(); u = M(u)
            sage: a/a
            Traceback (most recent call last):
            ...
            NotImplementedError: cannot invert non-units
            sage: u/u
            1 + O(a^30)

            sage: K = ZpFM(3,10)
            sage: R.<u> = K[]
            sage: L.<u> = K.extension(u^2 + 3*u + 4)
            sage: R.<a> = L[]
            sage: M = ZpTwoStepExtensionFactory(L, a^3 - 9*u*a^2 + 3*u, ram_name="a"); a = M.uniformizer(); u = M(u)
            sage: a/a
            Traceback (most recent call last):
            ...
            NotImplementedError: cannot invert non-units
            sage: u/u
            1 + O(a^30)

        """
        return self * ~other

    def __nonzero__(self):
        """
        Returns whether this element is non-zero.

        OUTPUT:

        Returns False if this element is either an exact zero or an inexact
        zero.

        EXAMPLES::

            sage: K = Qp(3,10)
            sage: R.<u> = K[]
            sage: L.<u> = K.extension(u^2 + 3*u + 4)
            sage: R.<a> = L[]
            sage: M = QpTwoStepExtensionFactory(L, a^3 - 9*u*a^2 + 3*u, ram_name="a"); a = M.uniformizer(); u = M(u)
            sage: a.is_zero() # indirect doctest
            False
            sage: M.zero().is_zero()
            True
            sage: M(0,3).is_zero()
            True

        """
        return not self._is_inexact_zero() and not self._is_exact_zero()

    cpdef _mul_(self, other):
        """
        Compute the multiplication of ``self`` by ``other``.

        INPUT:

            - ``other`` -- an element in the same ring as ``self``

        EXAMPLES::

            sage: K = Qp(3,10)
            sage: R.<u> = K[]
            sage: L.<u> = K.extension(u^2 + 3*u + 4)
            sage: R.<a> = L[]
            sage: M = QpTwoStepExtensionFactory(L, a^3 - 9*u*a^2 + 3*u, ram_name="a"); a = M.uniformizer(); u = M(u)
            sage: a*a
            a^2 + O(a^32)
            sage: M(3)^10 - M(3^10) # indirect doctest
            O(a^60)

        TESTS:

        We test that this also works for other base rings::

            sage: K = ZpCA(3,10)
            sage: R.<u> = K[]
            sage: L.<u> = K.extension(u^2 + 3*u + 4)
            sage: R.<a> = L[]
            sage: M = ZpTwoStepExtensionFactory(L, a^3 - 9*u*a^2 + 3*u, ram_name="a"); a = M.uniformizer(); u = M(u)
            sage: a*a
            a^2 + O(a^30)
            sage: M(3)^10 - M(3^10) # indirect doctest
            O(a^30)

            sage: K = ZpFM(3,10)
            sage: R.<u> = K[]
            sage: L.<u> = K.extension(u^2 + 3*u + 4)
            sage: R.<a> = L[]
            sage: M = ZpTwoStepExtensionFactory(L, a^3 - 9*u*a^2 + 3*u, ram_name="a"); a = M.uniformizer(); u = M(u)
            sage: a*a
            a^2 + O(a^30)
            sage: M(3)^10 - M(3^10) # indirect doctest
            O(a^30)

        """
        ret = self.parent()(None)
        ls = self._series_valuation() * other._series_valuation()
        if self.parent().is_capped_absolute() or self.parent().is_fixed_mod():
            ls = ls.add_bigoh(self.parent().precision_cap())
        ret.__set_from_laurent_series(ls)
        return ret

    def __lshift__(self, shift):
        """
        Multiply this element by ``pi^shift`` with ``pi`` being the generator
        of the Eisenstein step of the extension.

        INPUT:

            - ``shift`` -- an integer, if the element is not defined in a
              field, then ``-shift`` must not exceed its valuation.

        OUTPUT:

        An element in the same ring.

        EXAMPLES::

            sage: K = QpCR(3,10)
            sage: R.<u> = K[]
            sage: L.<u> = K.extension(u^2 + 3*u + 4)
            sage: R.<a> = L[]
            sage: M = QpTwoStepExtensionFactory(L, a^3 - 9*u*a^2 + 3*u, ram_name="a"); a = M.uniformizer(); u = M(u)
            sage: a<<2
            a^3 + O(a^33)
            sage: a<<-2
            a^-1 + O(a^29)

        TESTS:

        We test that this also works for other base rings::

            sage: K = ZpCA(3,10)
            sage: R.<u> = K[]
            sage: L.<u> = K.extension(u^2 + 3*u + 4)
            sage: R.<a> = L[]
            sage: M = ZpTwoStepExtensionFactory(L, a^3 - 9*u*a^2 + 3*u, ram_name="a"); a = M.uniformizer(); u = M(u)
            sage: a<<2
            a^3 + O(a^30)
            sage: a<<-2
            Traceback (most recent call last):
            ...
            ValueError: -shift must not exceed valuation
            sage: M(a,absprec=2)<<-1
            1 + O(a)
            sage: a<<30
            O(a^30)

            sage: K = ZpFM(3,10)
            sage: R.<u> = K[]
            sage: L.<u> = K.extension(u^2 + 3*u + 4)
            sage: R.<a> = L[]
            sage: M = ZpTwoStepExtensionFactory(L, a^3 - 9*u*a^2 + 3*u, ram_name="a"); a = M.uniformizer(); u = M(u)
            sage: a<<2
            a^3 + O(a^30)
            sage: a<<-2
            Traceback (most recent call last):
            ...
            ValueError: -shift must not exceed valuation
            sage: a<<30
            O(a^30)

        """
        if not self.parent().is_field() and -shift > self.valuation():
            raise ValueError("-shift must not exceed valuation")

        ret = self.parent()(None)
        ls = self._series_raw() << shift
        if self.parent().is_capped_absolute():
            ls = ls.add_bigoh(self.parent().precision_cap())
        elif self.parent().is_fixed_mod():
            ls = ls.truncate(self.parent().precision_cap()).add_bigoh(self.parent().precision_cap())
        ret.__set_from_laurent_series(ls)
        return ret

    def __rshift__(self, shift):
        """
        Multiply this element by ``pi^-shift`` with ``pi`` being the generator
        of the Eisenstein step of the extension.

        INPUT:

            - ``shift`` -- an integer, if the element is not defined in a
              field, then ``shift`` must not exceed its valuation.

        OUTPUT:

        An element in the same ring.

        EXAMPLES::

            sage: K = QpCR(3,10)
            sage: R.<u> = K[]
            sage: L.<u> = K.extension(u^2 + 3*u + 4)
            sage: R.<a> = L[]
            sage: M = QpTwoStepExtensionFactory(L, a^3 - 9*u*a^2 + 3*u, ram_name="a"); a = M.uniformizer(); u = M(u)
            sage: a>>-2
            a^3 + O(a^33)
            sage: a>>2
            a^-1 + O(a^29)

        """
        return self<<-shift

    def is_zero(self, absprec=None):
        """
        Returns whether this element is zero.

        INPUT:

            - ``absprec`` -- an integer, ``None`` or infinity (default: None),
              if ``absprec`` is ``None``, then this method returns whether this
              element is zero to the precision it is defined to, otherwise
              returns whether the element zero if considered to precision
              ``absprec``.

        OUTPUT:

        Raises an error if the element is not defined to the degree given by
        ``absprec``.

        EXAMPLES::

            sage: K = QpCR(3,10)
            sage: R.<u> = K[]
            sage: L.<u> = K.extension(u^2 + 3*u + 4)
            sage: R.<a> = L[]
            sage: M = QpTwoStepExtensionFactory(L, a^3 - 9*u*a^2 + 3*u, ram_name="a"); a = M.uniformizer(); u = M(u)
            sage: a.is_zero()
            False
            sage: a.is_zero(1)
            True
            sage: a.is_zero(infinity)
            Traceback (most recent call last):
            ...
            PrecisionError: element not defined to the required precision
            sage: M.zero().is_zero(infinity)
            True

        """
        if absprec is None:
            absprec = self.precision_absolute()
        if absprec > self.precision_absolute():
            raise PrecisionError("element not defined to the required precision")
        return self.valuation() >= absprec

    def unit_part(self):
        """
        Returns an element ``u`` such that the element is of the form
        ``u*pi^v`` with ``pi`` being the generator of the Eisenstein step of
        the two-step extension field.

        EXAMPLES::

            sage: K = QpCR(3,10)
            sage: R.<u> = K[]
            sage: L.<u> = K.extension(u^2 + 3*u + 4)
            sage: R.<a> = L[]
            sage: M = QpTwoStepExtensionFactory(L, a^3 - 9*u*a^2 + 3*u, ram_name="a"); a = M.uniformizer(); u = M(u)
            sage: a.unit_part()
            1 + O(a^30)

        We test that this also works for other base rings::

            sage: K = ZpCA(3,10)
            sage: R.<u> = K[]
            sage: L.<u> = K.extension(u^2 + 3*u + 4)
            sage: R.<a> = L[]
            sage: M = ZpTwoStepExtensionFactory(L, a^3 - 9*u*a^2 + 3*u, ram_name='a'); a = M.uniformizer()
            sage: a.unit_part()
            1 + O(a^29)

            sage: K = ZpFM(3,10)
            sage: R.<u> = K[]
            sage: L.<u> = K.extension(u^2 + 3*u + 4)
            sage: R.<a> = L[]
            sage: M = ZpTwoStepExtensionFactory(L, a^3 - 9*u*a^2 + 3*u, ram_name='a'); a = M.uniformizer()
            sage: a.unit_part()
            1 + O(a^30)

        """
        if self.is_zero():
            raise ValueError("element has no unit part")
        return self>>self.valuation()

    def lift_to_precision(self, absprec=None):
        """
        Returns a lift of this element which is defined at least to precision
        ``absprec``.

        INPUT:

            - ``absprec`` -- an integer or infinity

        EXAMPLES::

            sage: K = QpCR(3,10)
            sage: R.<u> = K[]
            sage: L.<u> = K.extension(u^2 + 3*u + 4)
            sage: R.<a> = L[]
            sage: M = QpTwoStepExtensionFactory(L, a^3 - 9*u*a^2 + 3*u, ram_name='a'); a = M.uniformizer()
            sage: a.lift_to_precision(3)
            a + O(a^31)
            sage: M(a,2).lift_to_precision(3)
            a + O(a^3)
            sage: a.lift_to_precision(32)
            Traceback (most recent call last):
            ...
            ValueError: cannot lift element to the requested precision in this ring

        """
        if absprec is None:
            if self.precision_relative() == 0:
                absprec = infinity
            else:
                absprec = self.valuation() + self.parent().precision_cap()

        if absprec is infinity:
            if not self.parent().is_capped_relative():
                raise ValueError("cannot lift element to the requested precision in this ring")
            return self.parent().zero()

        if self.parent().is_fixed_mod():
            return self

        if (self.parent().is_capped_relative() and absprec > self.parent().precision_cap() + self.valuation()) or \
           (self.parent().is_capped_absolute() and absprec > self.parent().precision_cap()):
             raise ValueError("cannot lift element to the requested precision in this ring")

        if self.precision_absolute() >= absprec:
            return self

        ret = self.parent()(None)
        ret.__set_from_laurent_series(self._series_raw().truncate(absprec).add_bigoh(absprec))
        return ret

    def is_equal_to(self, right, absprec=None):
        """
        Returns whether the element is equal to ``right``.

        INPUT:

            - ``right`` -- an element that coerces to the parent ring

            - ``absprec`` -- an integer, infinity, or ``None`` (default:
              ``None``), if ``None``, return whether the elements are equal
              when considered to the smallest of their precisions, otherwise,
              return whether the elements are equal when considered to
              precision ``absprec``.

        OUTPUT:

        Raises an error if ``absprec`` exceeds the precision of the elements.

        EXAMPLES::

            sage: K = QpCR(3,10)
            sage: R.<u> = K[]
            sage: L.<u> = K.extension(u^2 + 3*u + 4)
            sage: R.<a> = L[]
            sage: M = QpTwoStepExtensionFactory(L, a^3 - 9*u*a^2 + 3*u, ram_name='a'); a = M.uniformizer()
            sage: (a^3).is_equal_to(9*u*a^2 - 3*u)
            True
            sage: a.is_equal_to(a, absprec=infinity)
            Traceback (most recent call last):
            ...
            PrecisionError: element not defined to the required precision
            sage: M.zero().is_equal_to(0,absprec=infinity)
            True
            sage: a.is_equal_to(a+a^2,absprec=1)
            True

        """
        from sage.misc.functional import coerce
        right = coerce(self.parent(), right)
        return (self-right).is_zero(absprec)

    cdef int _cmp_units(left, pAdicGenericElement right) except -2:
        return 0 if (left-right).is_zero() else 1

    def residue(self, absprec=1):
        if absprec != 1:
            raise NotImplementedError
        if self.valuation() < 0:
            raise NotImplementedError
        elif self.valuation() > 0:
            return self.parent().residue_field().zero()
        else:
            return self._series_valuation()[0].residue()
