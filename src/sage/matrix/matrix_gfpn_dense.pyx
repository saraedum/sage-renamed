r"""
Dense Matrices over `\mathbb F_q`, with `q<255`.

This module is a wrapper for version 2.4.24 of the Aachen
`C-MeatAxe <http://www.math.rwth-aachen.de/homes/MTX/download.html>`_,
improved by an implementation of the Winograd-Strassen multiplication
algorithm. It provides matrices over the finite field `\mathbb F_q`,
where `q\le 255`.

By default, it is only used when `q` is odd and not prime, because other
matrix implementations in SageMath perform better for prime fields or in
characteristic two.

AUTHORS:

- Simon King (2015-09): initial version

"""

#*****************************************************************************
#       Copyright (C) 2015 Simon King <simon.king@uni-jena.de>
#
# This program is free software: you can redistribute it and/or modify
# it under the terms of the GNU General Public License as published by
# the Free Software Foundation, either version 2 of the License, or
# (at your option) any later version.
#                  http://www.gnu.org/licenses/
#*****************************************************************************
from __future__ import print_function, absolute_import, division

from cysignals.memory cimport check_realloc, check_malloc, sig_free
from cpython.bytes cimport PyBytes_AsString, PyBytes_FromStringAndSize
from cysignals.signals cimport sig_on, sig_off, sig_check

import os

####################
#
# import sage types
#
####################

from sage.cpython.string cimport str_to_bytes
from sage.cpython.string import FS_ENCODING
from sage.rings.integer import Integer
from sage.rings.finite_rings.finite_field_constructor import GF
from sage.rings.finite_rings.integer_mod import IntegerMod_int
from sage.matrix.constructor import random_matrix
from sage.matrix.matrix_space import MatrixSpace
from sage.misc.randstate import current_randstate
from sage.misc.randstate cimport randstate
from sage.misc.cachefunc import cached_method, cached_function
from sage.structure.element cimport Element, ModuleElement, RingElement, Matrix
from .args cimport MatrixArgs_init

from libc.string cimport memset, memcpy

cimport sage.matrix.matrix0

# The following import is just to ensure that meataxe_init() is called.
import sage.libs.meataxe

####################
#
# auxiliary functions
#
####################

# Fast conversion from field to int and int to field
cdef class FieldConverter_class:
    """
    An auxiliary class, used to convert between <int> and finite field element.

    This class is for non-prime fields only. The method
    :meth:`int_to_field` exists for speed. The method
    :meth:`field_to_int` exists in order to have a common interface
    for elements of prime and non-prime fields; see
    :class:`PrimeFieldConverter_class`.

    EXAMPLES::

        sage: from sage.matrix.matrix_gfpn_dense import FieldConverter_class  # optional: meataxe
        sage: F.<y> = GF(125)
        sage: C = FieldConverter_class(F)               # optional: meataxe
        sage: C.int_to_field(15)                        # optional: meataxe
        3*y
        sage: F.fetch_int(15)                           # optional: meataxe
        3*y
        sage: %timeit C.int_to_field(15)    # not tested
        625 loops, best of 3: 1.04 ??s per loop
        sage: %timeit F.fetch_int(15)       # not tested
        625 loops, best of 3: 3.97 ??s per loop
        sage: C.field_to_int(y)                         # optional: meataxe
        5
        sage: y.integer_representation()
        5

    """
    def __init__(self, field):
        """
        INPUT:

        A finite *non-prime* field. This assumption is not tested.

        EXAMPLES::

            sage: from sage.matrix.matrix_gfpn_dense import FieldConverter_class # optional: meataxe
            sage: F.<y> = GF(125)
            sage: C = FieldConverter_class(F)           # optional: meataxe
            sage: C.int_to_field(15)                    # optional: meataxe
            3*y
            sage: F.fetch_int(15)
            3*y
            sage: C.field_to_int(y)                     # optional: meataxe
            5
            sage: y.integer_representation()
            5

        """
        self.field = field._cache.fetch_int
    cpdef object int_to_field(self, int x):
        """
        Fetch a python int into the field.

        EXAMPLES::

            sage: from sage.matrix.matrix_gfpn_dense import FieldConverter_class  # optional: meataxe
            sage: F.<y> = GF(125)
            sage: C = FieldConverter_class(F)           # optional: meataxe
            sage: C.int_to_field(15)                    # optional: meataxe
            3*y
            sage: F.fetch_int(15)
            3*y

        """
        return self.field(x)
    cpdef int field_to_int(self, x):
        """
        Represent a field element by a python int.

        EXAMPLES::

            sage: from sage.matrix.matrix_gfpn_dense import FieldConverter_class  # optional: meataxe
            sage: F.<y> = GF(125)
            sage: C = FieldConverter_class(F)           # optional: meataxe
            sage: C.field_to_int(y)                     # optional: meataxe
            5
            sage: y.integer_representation()
            5

        """
        return x.integer_representation()

cdef class PrimeFieldConverter_class(FieldConverter_class):
    """
    An auxiliary class, used to convert between <int> and finite field element.

    This class is for prime fields only. The methods
    :meth:`int_to_field` and :meth:`field_to_int` exist in order to
    have a common interface for elements of prime and non-prime fields;
    see :class:`FieldConverter_class`.

    EXAMPLES::

        sage: from sage.matrix.matrix_gfpn_dense import PrimeFieldConverter_class # optional: meataxe
        sage: F = GF(5)
        sage: C = PrimeFieldConverter_class(F)      # optional: meataxe
        sage: C.int_to_field(int(2))                # optional: meataxe
        2
        sage: F(2)
        2
        sage: C.field_to_int(F(2))                  # optional: meataxe
        2
        sage: int(F(2))
        2

    """
    def __init__(self, field):
        """
        INPUT:

        A finite *prime* field. This assumption is not tested.

        EXAMPLES::

            sage: from sage.matrix.matrix_gfpn_dense import PrimeFieldConverter_class  # optional: meataxe
            sage: F = GF(5)
            sage: C = PrimeFieldConverter_class(F)  # optional: meataxe
            sage: C.int_to_field(int(2))            # optional: meataxe
            2
            sage: F(2)
            2
            sage: C.field_to_int(F(2))              # optional: meataxe
            2
            sage: int(F(2))
            2

        """
        self.field = field
    cpdef object int_to_field(self, int x):
        """
        Fetch a python int into the field.

        EXAMPLES::

            sage: from sage.matrix.matrix_gfpn_dense import PrimeFieldConverter_class  # optional: meataxe
            sage: F = GF(5)
            sage: C = PrimeFieldConverter_class(F)  # optional: meataxe
            sage: C.int_to_field(int(2))            # optional: meataxe
            2
            sage: F(2)
            2

        """
        return IntegerMod_int(self.field, x)
    cpdef int field_to_int(self, x):
        """
        Represent a field element by a python int.

        EXAMPLES::

            sage: from sage.matrix.matrix_gfpn_dense import PrimeFieldConverter_class  # optional: meataxe
            sage: F = GF(5)
            sage: C = PrimeFieldConverter_class(F)      # optional: meataxe
            sage: C.field_to_int(F(2))                  # optional: meataxe
            2
            sage: int(F(2))
            2

        """
        return int(x)

cdef dict _converter_cache = {}
cdef FieldConverter_class FieldConverter(field):
    """
    Return a :class:`FieldConverter_class` or :class:`PrimeFieldConverter_class` instance,
    depending whether the field is prime or not.

    EXAMPLES::

        sage: MS = MatrixSpace(GF(5^3,'y'),2)
        sage: A = MS.random_element()
        sage: A*2 == A+A    # indirect doctest
        True
        sage: A = MS.random_element()
        sage: A*2 == A+A
        True

    """
    try:
        return _converter_cache[field]
    except KeyError:
        if field.is_prime_field():
            return _converter_cache.setdefault(field, PrimeFieldConverter_class(field))
        return _converter_cache.setdefault(field, FieldConverter_class(field))

######################################
##
## Wrapper for MeatAxe matrices
##
######################################

cdef class Matrix_gfpn_dense(Matrix_dense):
    r"""
    Dense matrices over `\mathbb F_q`, `q<255` odd and not prime.

    NOTE:

    This class uses a major modification of the Aachen C-MeatAxe
    as backend. In principle, it would also work for prime fields
    and in characteristic two. However, other matrices in Sage,
    relying on linbox, m4ri or m4rie, are more efficient in these
    cases.

    EXAMPLES::

        sage: M = MatrixSpace(GF(25,'z'),2,3)([1,2,3,4,5,6])
        sage: print(M)
        [1 2 3]
        [4 0 1]
        sage: type(M)     # optional: meataxe
        <type 'sage.matrix.matrix_gfpn_dense.Matrix_gfpn_dense'>

    The documentation of the ``__init__`` methods shows further
    ways of creating a :class:`Matrix_gfpn_dense` instance.
    However, these should only be of internal use.

    """
##################
## Init, Dealloc, Copy

    def __dealloc__(self):
        """
        TESTS::

            sage: from sage.matrix.matrix_gfpn_dense import Matrix_gfpn_dense  # optional: meataxe
            sage: Matrix_gfpn_dense.__new__(Matrix_gfpn_dense)   # optional: meataxe
            []
            sage: M = None
            sage: M = Matrix_gfpn_dense(MatrixSpace(GF(64,'z'),4), None)  # optional: meataxe
            sage: del M    # indirect doctest
        """
        if self.Data != NULL:
            MatFree(self.Data)
            self.Data = NULL

    def __init__(self, parent, entries=None, copy=None, bint coerce=False, *, bint mutable=True):
        r"""
        Matrix extension class using libmeataxe as backend.

        INPUT:

        - ``parent`` -- a matrix space over ``GF(q)`` with `q < 255`

        - ``entries`` -- see :func:`matrix`

        - ``copy`` -- ignored (for backwards compatibility)

        - ``coerce`` -- ignored

        - ``mutable`` -- if False, the resulting matrix can not be
          changed, and it can be used as key in a Python dictionary

        EXAMPLES::

            sage: from sage.matrix.matrix_gfpn_dense import Matrix_gfpn_dense  # optional: meataxe

        1. Creating a zero (3x2)-matrix::

            sage: Matrix_gfpn_dense(MatrixSpace(GF(4,'z'),3,2))  # optional: meataxe
            [0 0]
            [0 0]
            [0 0]

        2. Creating a matrix from a list or list of lists::

            sage: Matrix_gfpn_dense(MatrixSpace(GF(5),2,3),[1,2,3,4,5,6])  # optional: meataxe
            [1 2 3]
            [4 0 1]
            sage: Matrix_gfpn_dense(MatrixSpace(GF(5),2,3),[[1,2,3],[4,5,6]])    # optional: meataxe
            [1 2 3]
            [4 0 1]

        3. Creating a diagonal matrix::

            sage: M = Matrix_gfpn_dense(MatrixSpace(GF(7),5),2); M  # optional: meataxe
            [2 0 0 0 0]
            [0 2 0 0 0]
            [0 0 2 0 0]
            [0 0 0 2 0]
            [0 0 0 0 2]

        4.  Creating a matrix from a file in MeatAxe format. If the file doesn't exist,
            an error raised by the MeatAxe library is propagated::

                sage: Matrix_gfpn_dense('foobarNONEXISTING_FILE')       # optional: meataxe
                Traceback (most recent call last):
                ...
                OSError: .../foobarNONEXISTING_FILE: No such file or directory in file os.c (line 255)
                sage: Matrix_gfpn_dense('')                             # optional: meataxe
                Traceback (most recent call last):
                ...
                ValueError: Can not construct meataxe matrix from empty filename

        TESTS::

            sage: MS = MatrixSpace(GF(125,'y'),2)  # indirect doctest
            sage: A = MS(0)
            sage: A.left_kernel()
            Vector space of degree 2 and dimension 2 over Finite Field in y of size 5^3
            Basis matrix:
            [1 0]
            [0 1]
            sage: A.right_kernel()
            Vector space of degree 2 and dimension 2 over Finite Field in y of size 5^3
            Basis matrix:
            [1 0]
            [0 1]
        """
        if isinstance(parent, (bytes, str)): # load from file
            if not parent:
                raise ValueError("Can not construct meataxe matrix from empty filename")

            filename = os.path.realpath(parent)

            if type(filename) is not bytes:
                filename = str_to_bytes(filename, FS_ENCODING,
                                        'surrogateescape')

            self.Data = MatLoad(filename)
            FfSetField(self.Data.Field)
            B = GF(self.Data.Field, 'z')
            parent = MatrixSpace(B, self.Data.Nor, self.Data.Noc)
            self._is_immutable = False
            self._parent = parent
            self._base_ring = B
            self._converter = FieldConverter(B)
            self._ncols = self.Data.Noc
            self._nrows = self.Data.Nor
            self._cache = {}
            return

        ma = MatrixArgs_init(parent, entries)
        Matrix_dense.__init__(self, ma.space)
        cdef long fl = ma.base.order()
        cdef long nr = ma.nrows
        cdef long nc = ma.ncols

        self.Data = MatAlloc(fl, nr, nc)
        self._converter = FieldConverter(ma.base)

        cdef PTR x = self.Data.Data
        assert self.Data.Noc == nc
        assert self.Data.Nor == nr
        FfSetField(fl)
        FfSetNoc(nc)
        it = ma.iter(False)
        cdef long i,j
        for i in range(nr):
            for j in range(nc):
                v = self._converter.field_to_int(self._coerce_element(next(it)))
                FfInsert(x, j, FfFromInt(v))
            FfStepPtr(&x)

        self._is_immutable = not mutable

    cdef Matrix_gfpn_dense _new(self, Py_ssize_t nrows, Py_ssize_t ncols):
        r"""
        Return a new matrix with no entries set.
        """
        cdef Matrix_gfpn_dense res
        res = self.__class__.__new__(self.__class__)

        if nrows == self._nrows and ncols == self._ncols:
            res._parent = self._parent
        else:
            res._parent = self.matrix_space(nrows, ncols)
        res._ncols  = ncols
        res._nrows  = nrows
        res._base_ring = self._base_ring
        res._converter = self._converter
        return res

    def __copy__(self):
        """
        Return a copy of this matrix.

        EXAMPLES::

            sage: M = MatrixSpace(GF(25,'x'), 3, 20)([20*[0],20*[0],[1]+19*[0]])
            sage: N = copy(M)   # indirect doctest
            sage: print(N)
            [0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0]
            [0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0]
            [1 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0]
            sage: N== M
            True
            sage: N is M
            False
            sage: from sage.matrix.matrix_gfpn_dense import Matrix_gfpn_dense  # optional: meataxe
            sage: M = Matrix_gfpn_dense.__new__(Matrix_gfpn_dense)   # optional: meataxe
            sage: N = copy(M)
            sage: N                         # optional: meataxe
            []
            sage: N == M
            True
            sage: N is M
            False
        """
        cdef Matrix_gfpn_dense retval = self._new(self._nrows, self._ncols)
        retval._is_immutable = False  # a copy of a matrix is mutable!
        retval._cache = dict(self._cache) if self._cache is not None else {}
        if self.Data:
            retval.Data = MatDup(self.Data)
        else:
            retval.Data = NULL
        return retval

    def __reduce__(self):
        """
        TESTS::

            sage: M = MatrixSpace(GF(9,'x'),10,10).random_element()
            sage: M == loads(dumps(M))   # indirect doctest
            True
            sage: M is loads(dumps(M))
            False
        """
        cdef char* d
        cdef char* x
        cdef size_t i
        cdef PTR p
        cdef size_t pickle_size
        cdef bytes pickle_str
        if self.Data:
            FfSetField(self.Data.Field)
            FfSetNoc(self.Data.Noc)
            pickle_size = FfCurrentRowSizeIo*self.Data.Nor
            d = <char*>check_malloc(pickle_size)
            p = self.Data.Data
            x = d
            for i in range(self.Data.Nor):
                memcpy(x, p, FfCurrentRowSizeIo)
                sig_check()
                x += FfCurrentRowSizeIo
                FfStepPtr(&p)
            pickle_str = PyBytes_FromStringAndSize(d, pickle_size)
            sig_free(d)
            return mtx_unpickle, (self._parent, self.Data.Nor, self.Data.Noc,
                        pickle_str,
                        not self._is_immutable) # for backward compatibility with the group cohomology package
        else:
            return mtx_unpickle, (0, 0, 0, '', not self._is_immutable)

    cdef get_unsafe(self, Py_ssize_t i, Py_ssize_t j):
        """
        Get an element without checking.

        TESTS::

            sage: F.<z> = GF(9)
            sage: M = MatrixSpace(F,3)(sorted(list(F)))
            sage: type(M)               # optional: meataxe
            <type 'sage.matrix.matrix_gfpn_dense.Matrix_gfpn_dense'>
            sage: M                     # indirect doctest
            [      0       1       2]
            [      z   z + 1   z + 2]
            [    2*z 2*z + 1 2*z + 2]

        """
        if self.Data == NULL:
            raise IndexError("Matrix is empty")
        FfSetField(self.Data.Field)
        return self._converter.int_to_field(FfToInt(FfExtract(MatGetPtr(self.Data,i), j)))

    cdef inline int get_unsafe_int(self, Py_ssize_t i, Py_ssize_t j):
        # NOTE:
        # It is essential that you call FfSetField and FfSetNoc YOURSELF
        # and that you assert that the matrix is not empty!
        # This method is here for speed!
        return FfToInt(FfExtract(MatGetPtr(self.Data,i), j))

    cpdef Matrix_gfpn_dense get_slice(self, Py_ssize_t i, Py_ssize_t j):
        """
        Return a horizontal slice of this matrix.

        NOTE:

        ``M[i:j]`` may return a matrix that uses a different backend than
        MeatAxe. This method is useful when the slice has to be of type
        :class:`Matrix_gfpn_dense`.

        EXAMPLES::

            sage: from sage.matrix.matrix_gfpn_dense import Matrix_gfpn_dense as MTX  # optional: meataxe
            sage: M = MTX(MatrixSpace(GF(7), 5, 3), [[0,1,2], [1,2,3], [2,3,4], [3,4,5], [4,5,6]]) # optional: meataxe
            sage: M # optional: meataxe
            [0 1 2]
            [1 2 3]
            [2 3 4]
            [3 4 5]
            [4 5 6]
            sage: M.get_slice(1,3)  # optional: meataxe
            [1 2 3]
            [2 3 4]
            sage: type(_) is MTX    # optional: meataxe
            True

        """
        if not 0 <= i < j <= self.Data.Nor:
            raise IndexError("Indices i={}, j={} violate the condition 0 < i < j < {}".format(i,j,self.Data.Nor))
        cdef Matrix_gfpn_dense OUT = self._new(j-i, self.Data.Noc)
        OUT.Data = MatAlloc(self.Data.Field, j-i, self.Data.Noc)
        memcpy(OUT.Data.Data, FfGetPtr(self.Data.Data, i), FfCurrentRowSize*(j-i))
        return OUT

    cdef set_unsafe(self, Py_ssize_t i, Py_ssize_t j, value):
        """
        Set values without bound checking.

        TESTS:

        The following test would have failed in a preliminary version
        of this MeatAxe wrapper::

            sage: K.<x> = GF(125)
            sage: M = MatrixSpace(K,9,9)()
            sage: N = MatrixSpace(GF(9,'x'),20).random_element()
            sage: M[2,2] = x
            sage: M
            [0 0 0 0 0 0 0 0 0]
            [0 0 0 0 0 0 0 0 0]
            [0 0 x 0 0 0 0 0 0]
            [0 0 0 0 0 0 0 0 0]
            [0 0 0 0 0 0 0 0 0]
            [0 0 0 0 0 0 0 0 0]
            [0 0 0 0 0 0 0 0 0]
            [0 0 0 0 0 0 0 0 0]
            [0 0 0 0 0 0 0 0 0]

        """
        # ASSUMPTION: value's parent is the base ring
        if self.Data == NULL:
            raise IndexError("Matrix is empty")
        FfSetField(self.Data.Field)
        FfInsert(MatGetPtr(self.Data,i), j, FfFromInt(self._converter.field_to_int(value)))

    cdef set_unsafe_int(self, Py_ssize_t i, Py_ssize_t j, int value):
        # NOTE:
        # It is essential that you call FfSetField and FfSetNoc YOURSELF
        # and that you assert that the matrix is not empty!
        # This method is here for speed!
        FfInsert(FfGetPtr(self.Data.Data,i), j, FfFromInt(value))

    cdef set_slice_unsafe(self, Py_ssize_t i, Matrix_gfpn_dense S):
        # Overwrite the self[i:i+S.nrows()] by the contents of S.
        #
        # NOTE:
        # It is essential that you call FfSetField and FfSetNoc YOURSELF
        # and that the dimensions of self and S match!
        memcpy(FfGetPtr(self.Data.Data, i), S.Data.Data, FfCurrentRowSize*S.Data.Nor)

    def randomize(self, density=None, nonzero=False, *args, **kwds):
        """
        Fill the matrix with random values.

        INPUT:

        - ``density`` (optional real number between zero and one) --
          the expected density of the resulting matrix
        - ``nonzero`` (optional bool, default ``False``) --
          If true, all inserted marks are non-zero.

        EXAMPLES::

            sage: MS = MatrixSpace(GF(27,'z'),6,6)
            sage: M = MS.random_element()       # indirect doctest
            sage: M                             # optional: meataxe
            [              1           z + 1     z^2 + z + 1             z^2       2*z^2 + z           z + 1]
            [2*z^2 + 2*z + 2   2*z^2 + z + 2         z^2 + 1 2*z^2 + 2*z + 2         z^2 + z   2*z^2 + z + 1]
            [        2*z + 2     z^2 + z + 2           z + 2 2*z^2 + 2*z + 2           2*z^2           2*z^2]
            [  2*z^2 + z + 2             z^2           z + 2         z^2 + z       2*z^2 + 2         z^2 + 2]
            [      2*z^2 + z             2*z 2*z^2 + 2*z + 1       2*z^2 + 1 2*z^2 + 2*z + 1       2*z^2 + z]
            [        2*z + 1         z^2 + z             z^2             z^2     2*z^2 + 2*z           z + 1]
            sage: type(M)                           # optional: meataxe
            <type 'sage.matrix.matrix_gfpn_dense.Matrix_gfpn_dense'>
            sage: MS.random_element(nonzero=True)   # optional: meataxe
            [            2*z               1   z^2 + 2*z + 1   2*z^2 + z + 1             z^2     z^2 + z + 1]
            [    2*z^2 + 2*z   2*z^2 + z + 2         2*z + 1       z^2 + 2*z     2*z^2 + 2*z             z^2]
            [        z^2 + z     z^2 + z + 2 2*z^2 + 2*z + 1         z^2 + 2               1           2*z^2]
            [              z     2*z^2 + 2*z           2*z^2         2*z + 1           z + 2           z + 2]
            [        z^2 + z             z^2           z + 2     2*z^2 + 2*z         2*z + 1         z^2 + z]
            [    z^2 + z + 2       2*z^2 + z             z^2           z + 1     2*z^2 + 2*z   z^2 + 2*z + 1]
            sage: MS.random_element(density=0.5)    # optional: meataxe
            [        z^2 + 2               0   z^2 + 2*z + 2       2*z^2 + z               0     z^2 + z + 2]
            [              0               1               0               0               0               0]
            [  2*z^2 + z + 1   2*z^2 + z + 2               0     z^2 + z + 2               0     z^2 + z + 1]
            [              0               0               0               0               0               0]
            [2*z^2 + 2*z + 2               0               0   2*z^2 + z + 2               0         2*z + 1]
            [              0       2*z^2 + z               0               1               0   2*z^2 + z + 1]

        The following tests against a bug that was fixed in :trac:`23352`::

            sage: MS = MatrixSpace(GF(9,'x'),1,5)
            sage: MS.random_element()     # optional: meataxe
            [x + 1     x     2 x + 2 x + 2]

        """
        self.check_mutability()
        cdef int fl = self.Data.Field
        density = float(density)
        if density <= 0:
            return
        if density > 1:
            density = float(1)

        self.clear_cache()

        cdef PTR x
        cdef unsigned char *y
        x = self.Data.Data
        cdef int nr = self.Data.Nor
        cdef int nc = self.Data.Noc
        cdef int i, j, k

        FfSetField(fl)
        FfSetNoc(nc)
        cdef int MPB, tmp
        cdef unsigned char O
        cdef randstate RandState = current_randstate()

        if not nonzero:
            if density == 1:
                MPB = 0
                tmp = fl
                while tmp <= 256:
                    MPB += 1
                    tmp *= fl
                O = (fl**MPB)
                if nc%MPB:
                    for i in range(nr):
                        y = <unsigned char*>x
                        for j in range(FfCurrentRowSizeIo-1):
                            y[j] = RandState.c_random()%O
                            sig_check()
                        for j in range(nc-(nc%MPB), nc):
                            FfInsert(x, j, FfFromInt( (RandState.c_random()%fl) ))
                            sig_check()
                        FfStepPtr(&(x))
                else:
                    for i in range(nr):
                        y = <unsigned char*>x
                        for j in range(FfCurrentRowSizeIo):
                            y[j] = RandState.c_random()%O
                            sig_check()
                        FfStepPtr(&(x))
            else:
                for i in range(nr):
                    for j in range(nc):
                        if RandState.c_rand_double() < density:
                            FfInsert(x, j, FfFromInt( (RandState.c_random()%fl) ))
                            sig_check()
                    FfStepPtr(&(x))
        else:
            if density == 1:
                fl -= 1
                for i in range(nr):
                    for j in range(nc):
                        FfInsert(x, j, FfFromInt( (RandState.c_random()%fl)+1 ))
                        sig_check()
                    FfStepPtr(&(x))
            else:
                fl -= 1
                for i in range(nr):
                    for j in range(nc):
                        if RandState.c_rand_double() < density:
                            FfInsert(x, j, FfFromInt( (RandState.c_random()%fl)+1 ))
                            sig_check()
                    FfStepPtr(&(x))

## Debugging
#    def show_contents(self, r=None):
#        FfSetField(self.Data.Field)
#        FfSetNoc(self.Data.Noc)
#        cdef PTR p
#        cdef size_t i, j
#        if r is not None:
#            r_min = r
#            r_max = r+1
#        else:
#            r_min = 0
#            r_max = self.Data.Nor
#        for i in range(r_min, r_max):
#            p = FfGetPtr(self.Data.Data, i)
#            for j from 0<=j<self.Data.RowSize:
#                print("%3.3d" % p[j])
#            print

##################
## comparison
    cpdef int _cmp_(left, right) except -2:
        """
        Compare two :class:`Matrix_gfpn_dense` matrices.

        Of course, '<' and '>' doesn't make much sense for matrices.

        EXAMPLES::

            sage: M = MatrixSpace(GF(125,'x'),3,20)([20*[0],20*[0],[1]+19*[0]])
            sage: N = copy(M)
            sage: M == N
            True
            sage: M != N
            False
            sage: M < N
            False
            sage: N[2,19] = 1
            sage: M == N
            False
            sage: M != N
            True
        """
        cdef Matrix_gfpn_dense self = left
        cdef Matrix_gfpn_dense N = right
        if self is None or N is None:
            return -1
        cdef char* d1
        cdef char* d2
        if self.Data == NULL:
            if N.Data == NULL:
                return 0
            else:
                return 1
        elif N.Data == NULL:
            return -1
        if self.Data.Field != N.Data.Field:
            if self.Data.Field > N.Data.Field:
                return 1
            return -1
        if self.Data.Noc != N.Data.Noc:
            if self.Data.Noc > N.Data.Noc:
                return 1
            return -1
        if self.Data.Nor != N.Data.Nor:
            if self.Data.Nor > N.Data.Nor:
                return 1
            return -1
        d1 = <char*>(self.Data.Data)
        d2 = <char*>(N.Data.Data)
        cdef bytes s1 = PyBytes_FromStringAndSize(d1,self.Data.RowSize * self.Data.Nor)
        cdef bytes s2 = PyBytes_FromStringAndSize(d2,N.Data.RowSize * N.Data.Nor)
        if s1 != s2:
            if s1 > s2:
                return 1
            return -1
        return 0

    cpdef list _rowlist_(self, i, j=-1):
        """
        Return rows as a flat list of python ints.

        INPUT:

        - `i`: Index of the first row to be extracted
        - `j` (optional, default -1): -1, or index of the last
          row to be extracted.

        OUTPUT:

        If `j=-1` then only the `i`-th row is returned as a list.
        Otherwises, rows `i` to `j` (both included) are returned
        as a list of integers.

        EXAMPLES::

            sage: M = random_matrix(GF(25,'x'), 5,5)
            sage: M                                      # optional: meataxe
            [      4     4*x   x + 3 4*x + 2 3*x + 4]
            [  x + 2 3*x + 1       3       0       3]
            [    3*x 2*x + 4       1       0     2*x]
            [4*x + 4 2*x + 3     4*x       1 3*x + 1]
            [3*x + 3   x + 3   x + 2   x + 1 3*x + 2]
            sage: M._rowlist_(1)                         # optional: meataxe
            [7, 16, 3, 0, 3]
            sage: [M[1,i]._int_repr() for i in range(5)] # optional: meataxe
            ['7', '16', '3', '0', '3']
            sage: M._rowlist_(2,4)                       # optional: meataxe
            [15, 14, 1, 0, 10, 24, 13, 20, 1, 16, 18, 8, 7, 6, 17]
            sage: [[M[i,j]._int_repr() for j in range(5)] for i in range(2,5)] # optional: meataxe
            [['15', '14', '1', '0', '10'],
             ['24', '13', '20', '1', '16'],
             ['18', '8', '7', '6', '17']]

        """
        cdef int k
        if self.Data:
            FfSetField(self.Data.Field)
            FfSetNoc(self.Data.Noc)
        else:
            raise ValueError("Matrix is empty")
        if (i < 0) or (i >= self.Data.Nor):
            raise IndexError("Index {} out of range 0..{}",format(i,self.Data.Nor-1))
        cdef PTR p
        p = MatGetPtr(self.Data,i)
        L = [FfToInt(FfExtract(p,k)) for k in range(self.Data.Noc)]
        if j!=-1:
            if not(isinstance(j,int) or isinstance(j,Integer)):
                raise TypeError("Second index must be an integer")
            if j >= self.Data.Nor:
                raise IndexError("Index out of range")
            for k in range(i, j):
                FfStepPtr(&(p)) # This is only called after MatGetPtr, hence, after FfSetNoc.
                L.extend([FfToInt(FfExtract(p,l)) for l in range(self.Data.Noc)])
        return L

    def _list(self):
        """
        Return a flat list of all entries of this matrix.

        The result is cached.

        EXAMPLES::

            sage: MatrixSpace(GF(9,'x'),3)(sorted(list(GF(9,'x')))).list()  # indirect doctest
            [0, 1, 2, x, x + 1, x + 2, 2*x, 2*x + 1, 2*x + 2]

        """
        cdef list x = self.fetch('list')
        if not x is None:
            return x
        x = []
        cdef int i
        if self.Data:
            FfSetField(self.Data.Field)
            FfSetNoc(self.Data.Noc)
        else:
            raise IndexError("Matrix is empty")
        cdef PTR p
        p = self.Data.Data
        for i in range(1, self.Data.Nor):
            x.extend([self._converter.int_to_field(FfToInt(FfExtract(p,j))) for j in range(self.Data.Noc)])
            FfStepPtr(&(p))
            sig_check()
        x.extend([self._converter.int_to_field(FfToInt(FfExtract(p,j))) for j in range(self.Data.Noc)])
        self.cache('list', x)
        return x

#########################
## Arithmetics
    cdef rescale_row_c(self, Py_ssize_t i, s, Py_ssize_t start_col):
        """
        Rescale row number `i` in-place by multiplication with the scalar `s`.

        The argument ``start_col`` is ignored. The scalar `s` is
        converted into the base ring.

        EXAMPLES::

            sage: K.<x> = GF(25)
            sage: M = MatrixSpace(K,5,5)(sorted(list(K)))
            sage: M
            [      0       1       2       3       4]
            [      x   x + 1   x + 2   x + 3   x + 4]
            [    2*x 2*x + 1 2*x + 2 2*x + 3 2*x + 4]
            [    3*x 3*x + 1 3*x + 2 3*x + 3 3*x + 4]
            [    4*x 4*x + 1 4*x + 2 4*x + 3 4*x + 4]
            sage: M.rescale_row(1, 3)   # indirect doctest
            sage: M
            [      0       1       2       3       4]
            [    3*x 3*x + 3 3*x + 1 3*x + 4 3*x + 2]
            [    2*x 2*x + 1 2*x + 2 2*x + 3 2*x + 4]
            [    3*x 3*x + 1 3*x + 2 3*x + 3 3*x + 4]
            [    4*x 4*x + 1 4*x + 2 4*x + 3 4*x + 4]
            sage: M.rescale_row(4, x)
            sage: M
            [      0       1       2       3       4]
            [    3*x 3*x + 3 3*x + 1 3*x + 4 3*x + 2]
            [    2*x 2*x + 1 2*x + 2 2*x + 3 2*x + 4]
            [    3*x 3*x + 1 3*x + 2 3*x + 3 3*x + 4]
            [4*x + 2       2   x + 2 2*x + 2 3*x + 2]

        """
        if start_col != 0 or self.Data == NULL:
            raise ValueError("We can only rescale a full row of a non-empty matrix")
        FfMulRow(MatGetPtr(self.Data, i), FfFromInt(self._converter.field_to_int(self._base_ring(s))))

    cdef add_multiple_of_row_c(self,  Py_ssize_t row_to, Py_ssize_t row_from, multiple, Py_ssize_t start_col):
        """
        Add the ``multiple``-fold of row ``row_from`` in-place to row ``row_to``.

        EXAMPLES::

            sage: K.<x> = GF(25)
            sage: M = MatrixSpace(K,5,5)(sorted(list(K)))
            sage: M
            [      0       1       2       3       4]
            [      x   x + 1   x + 2   x + 3   x + 4]
            [    2*x 2*x + 1 2*x + 2 2*x + 3 2*x + 4]
            [    3*x 3*x + 1 3*x + 2 3*x + 3 3*x + 4]
            [    4*x 4*x + 1 4*x + 2 4*x + 3 4*x + 4]
            sage: M.add_multiple_of_row(2, 4, x)  # indirect doctest
            sage: M
            [      0       1       2       3       4]
            [      x   x + 1   x + 2   x + 3   x + 4]
            [  x + 2 2*x + 3 3*x + 4     4*x       1]
            [    3*x 3*x + 1 3*x + 2 3*x + 3 3*x + 4]
            [    4*x 4*x + 1 4*x + 2 4*x + 3 4*x + 4]

        """
        if start_col != 0 or self.Data == NULL:
            raise ValueError("We can only rescale a full row of a non-empty matrix")
        FfAddMulRow(MatGetPtr(self.Data, row_to), MatGetPtr(self.Data, row_from), FfFromInt(self._converter.field_to_int(self._base_ring(multiple))))

    cdef swap_rows_c(self, Py_ssize_t row1, Py_ssize_t row2):
        """
        Swap the rows ``row1`` and ``row2`` in-place.

        EXAMPLES::

            sage: K.<x> = GF(25)
            sage: M = MatrixSpace(K,5,5)(sorted(list(K)))
            sage: M
            [      0       1       2       3       4]
            [      x   x + 1   x + 2   x + 3   x + 4]
            [    2*x 2*x + 1 2*x + 2 2*x + 3 2*x + 4]
            [    3*x 3*x + 1 3*x + 2 3*x + 3 3*x + 4]
            [    4*x 4*x + 1 4*x + 2 4*x + 3 4*x + 4]
            sage: M.swap_rows(1, 3)    # indirect doctest
            sage: M
            [      0       1       2       3       4]
            [    3*x 3*x + 1 3*x + 2 3*x + 3 3*x + 4]
            [    2*x 2*x + 1 2*x + 2 2*x + 3 2*x + 4]
            [      x   x + 1   x + 2   x + 3   x + 4]
            [    4*x 4*x + 1 4*x + 2 4*x + 3 4*x + 4]

        """
        FfSwapRows(MatGetPtr(self.Data, row1), MatGetPtr(self.Data, row2))

    def trace(self):
        """
        Trace of this matrix, i.e., the sum of diagonal elements.

        EXAMPLES::

            sage: K.<x> = GF(125)
            sage: MatrixSpace(K,7,7)(x).trace()
            2*x

        """
        if self._nrows != self._ncols:
            raise ValueError("self must be a square matrix")
        return self._converter.int_to_field(FfToInt(MatTrace(self.Data)))

    def stack(self, Matrix_gfpn_dense other):
        """
        Stack two matrices of the same number of columns.

        EXAMPLES::

            sage: M = MatrixSpace(GF(9,'x'),1,9)(sorted(list(GF(9,'x'))))
            sage: M
            [      0       1       2       x   x + 1   x + 2     2*x 2*x + 1 2*x + 2]
            sage: M.stack(M)
            [      0       1       2       x   x + 1   x + 2     2*x 2*x + 1 2*x + 2]
            [      0       1       2       x   x + 1   x + 2     2*x 2*x + 1 2*x + 2]

        """
        if self._ncols != other._ncols:
            raise TypeError("Both numbers of columns must match.")
        if self._nrows == 0 or self.Data == NULL:
            return other.__copy__()
        if other._nrows == 0 or other.Data == NULL:
            return self.__copy__()
        cdef Matrix_gfpn_dense OUT = self._new(self._nrows+other._nrows, self._ncols)
        OUT.Data = MatAlloc(self.Data.Field, self.Data.Nor+other.Data.Nor, self.Data.Noc)
        memcpy(OUT.Data.Data, self.Data.Data, FfCurrentRowSize*self.Data.Nor)
        memcpy(MatGetPtr(OUT.Data, self.Data.Nor), other.Data.Data, FfCurrentRowSize*other.Data.Nor)
        return OUT

    cpdef _add_(self, right):
        """
        TESTS::

            sage: K.<x> = GF(9)
            sage: M = MatrixSpace(K,3,3)(sorted(list(K)))
            sage: N = MatrixSpace(K,3,3)(2*x)
            sage: M+N           # indirect doctest
            [    2*x       1       2]
            [      x       1   x + 2]
            [    2*x 2*x + 1   x + 2]

        """
        cdef Matrix_gfpn_dense Self = self
        cdef Matrix_gfpn_dense Right = right
        assert Self is not None
        assert Right is not None
        if Self.Data == NULL or Right.Data == NULL:
            raise NotImplementedError("The matrices must not be empty")
        cdef Matrix_gfpn_dense Left = Self.__copy__()
        Left._cache = {}
        MatAdd(Left.Data, Right.Data)
        return Left

    cpdef _sub_(self, right):
        """
        TESTS::

            sage: K.<x> = GF(9)
            sage: M = MatrixSpace(K,3,3)(sorted(list(K)))
            sage: N = MatrixSpace(K,3,3)(2*x)
            sage: M-N    # indirect doctest
            [      x       1       2]
            [      x 2*x + 1   x + 2]
            [    2*x 2*x + 1       2]

        """
        cdef Matrix_gfpn_dense Self = self
        cdef Matrix_gfpn_dense Right = right
        assert Self is not None
        assert Right is not None
        if Self.Data == NULL or Right.Data == NULL:
            raise NotImplementedError("The matrices must not be empty")
        cdef Matrix_gfpn_dense Left = Self.__copy__()
        Left._is_immutable = False
        Left._cache = {}
        MatAddMul(Left.Data, Right.Data, mtx_taddinv[1])
        return Left

    def __neg__(self):
        """
        TESTS::

            sage: M = MatrixSpace(GF(9,'x'),3,3)(sorted(list(GF(9,'x'))))
            sage: -M
            [      0       2       1]
            [    2*x 2*x + 2 2*x + 1]
            [      x   x + 2   x + 1]

        ::

            sage: M = MatrixSpace(GF(125,'x'),10,30).random_element()
            sage: N = MatrixSpace(GF(125,'x'),10,30).random_element()
            sage: M + (-N) == M - N == -(N - M)
            True

        """
        if self.Data == NULL:
            raise ValueError("The matrix must not be empty")
        return self._lmul_(self._base_ring(-1))

    cpdef _lmul_(self, Element right):
        """
        EXAMPLES::

            sage: M = MatrixSpace(GF(9,'x'),3,3)(sorted(list(GF(9,'x'))))
            sage: K.<x> = GF(9)
            sage: M = MatrixSpace(K,3,3)(sorted(list(K)))
            sage: x*M    # indirect doctest
            [      0       x     2*x]
            [  x + 1 2*x + 1       1]
            [2*x + 2       2   x + 2]
            sage: M*x    # indirect doctest
            [      0       x     2*x]
            [  x + 1 2*x + 1       1]
            [2*x + 2       2   x + 2]
            sage: -M == (-1)*M
            True

        TESTS:

        Make sure that :trac:`25076` remains fixed::

            sage: M == M*int(4) == int(4)*M
            True

        """
        if self.Data == NULL:
            return self.__copy__()
        FfSetField(self.Data.Field)
        cdef Matrix_gfpn_dense OUT = self.__copy__()
        OUT._cache = {}
        MatMulScalar(OUT.Data, FfFromInt(self._converter.field_to_int(right)))
        return OUT

    cdef int _strassen_default_cutoff(self, sage.matrix.matrix0.Matrix right) except -2:
        # Surprisingly, Winograd-Strassen can compete with school book
        # multiplication for smallish matrices, and of course it is
        # asymptotically faster. So, we used it by default.
        return 0

    cpdef Matrix_gfpn_dense _multiply_classical(Matrix_gfpn_dense self, Matrix_gfpn_dense right):
        """
        Multiplication using the cubic school book multiplication algorithm.

        EXAMPLES:

        Since by default the asymptotically faster Strassen-Winograd
        multiplication algorithm is used, the following is a valid
        consistency check::

            sage: M = MatrixSpace(GF(9,'x'),1000,500).random_element()
            sage: N = MatrixSpace(GF(9,'x'),500,2000).random_element()
            sage: M*N == M._multiply_classical(N)                       # optional: meataxe
            True

        """
        "multiply two meataxe matrices by the school book algorithm"
        if self.Data == NULL or right.Data == NULL:
            raise ValueError("The matrices must not be empty")
        if self._ncols != right._nrows:
            raise ArithmeticError("left ncols must match right nrows")
        cdef Matrix_gfpn_dense OUT = self._new(self._nrows, right._ncols)
        sig_on()
        OUT.Data = MatDup(self.Data)
        MatMul(OUT.Data,right.Data)
        sig_off()
        OUT._is_immutable = False
        OUT._cache = {}
        return OUT

    cpdef Matrix_gfpn_dense _multiply_strassen(Matrix_gfpn_dense self, Matrix_gfpn_dense right, cutoff=0):
        """
        Matrix multiplication using the asymptotically fast Strassen-Winograd algorithm.

        INPUT:

        - ``right`` -- a matrix of dimensions suitable to do multiplication
        - ``cutoff`` (optional integer) -- indicates the minimal size of submatrices
          that will be considered in the divide-and-conquer algorithm. The size is
          *not* expressed by the number of rows/columns, but the rowsize expressed
          in bytes. Depending on the base field, one byte may represent up to eight
          entries in a matrix row. The default is ``sizeof(long)^2/2`` byte.

        EXAMPLES:

        We test that different cutoffs yield the same result::

            sage: M = MatrixSpace(GF(9,'x'),1500,600).random_element()
            sage: N = MatrixSpace(GF(9,'x'),600,1500).random_element()
            sage: M._multiply_strassen(N) == M._multiply_strassen(N,80) == M._multiply_strassen(N,2) # optional: meataxe
            True

        """
        if self.Data == NULL or right.Data == NULL:
            raise ValueError("The matrices must not be empty")
        if self._ncols != right._nrows:
            raise ArithmeticError("left ncols must match right nrows")
        MS = self.matrix_space(self._nrows, right._ncols, False)
        cdef Matrix_gfpn_dense OUT = Matrix_gfpn_dense(MS, None)
        # Now, OUT.Data is initialised, which is needed for MatMulStrassen to work.
        cutoff = cutoff//sizeof(long)
        StrassenSetCutoff(cutoff)
        sig_on()
        MatMulStrassen(OUT.Data, self.Data, right.Data)
        sig_off()
        return OUT

    cdef _mul_long(self, long n):
        """
        Multiply an MTX matrix with a field element represented by an integer.
        """
        if self.Data == NULL:
            raise ValueError("The matrix must not be empty")
        cdef Matrix_gfpn_dense left
        cdef FEL r
        if n < 0:
            r = mtx_taddinv[FfFromInt(-n)]
        else:
            r = FfFromInt(n)
        left = self.__copy__()
        left._cache = {}
        MatMulScalar(left.Data, r)
        return left

    def __div__(Matrix_gfpn_dense self, p):
        """
        Divide a matrix by a scalar.

        EXAMPLES::

            sage: K.<x> = GF(9)
            sage: M = MatrixSpace(K,3,3)(sorted(list(K)))
            sage: M
            [      0       1       2]
            [      x   x + 1   x + 2]
            [    2*x 2*x + 1 2*x + 2]
            sage: M/2                   # indirect doctest
            [      0       2       1]
            [    2*x 2*x + 2 2*x + 1]
            [      x   x + 2   x + 1]
            sage: M/x
            [      0   x + 2 2*x + 1]
            [      1       x 2*x + 2]
            [      2   x + 1     2*x]

        """
        if self.Data == NULL:
            return self.__copy__()
        if not p:
            raise ZeroDivisionError
        if p not in self._base_ring:
            raise ValueError("{} is not a scalar".format(p))
        p = self._base_ring(p)
        FfSetField(self.Data.Field)
        cdef Matrix_gfpn_dense OUT = self.__copy__()
        OUT._cache = {}
        cdef FEL r = mtx_tmultinv[FfFromInt(self._converter.field_to_int(p))]
        MatMulScalar(OUT.Data, r)
        return OUT

    def __invert__(Matrix_gfpn_dense self):
        """
        Multiplicative inverse of this matrix (if available).

        TESTS::

            sage: MS = MatrixSpace(GF(9,'x'),500)
            sage: while 1:
            ....:     M = MS.random_element()
            ....:     if M.rank() == 500:
            ....:         break
            sage: Minv = ~M    # indirect doctest
            sage: Minv*M == M*Minv == 1
            True

        We use the occasion to demonstrate that errors in MeatAxe are
        correctly handled in Sage::

            sage: MS = MatrixSpace(GF(25,'x'),5)
            sage: while 1:
            ....:     M = MS.random_element(density=0.4)
            ....:     if M.rank() < 5:
            ....:         break
            sage: ~M                    # optional: meataxe
            Traceback (most recent call last):
            ...
            ZeroDivisionError: Division by zero in file matinv.c (line 50)

        """
        if self.Data == NULL:
            raise ValueError("The matrix must not be empty")
        if not self.is_square():
            raise ArithmeticError("self must be a square matrix")
        cdef Matrix_gfpn_dense OUT = self._new(self._nrows, self._ncols)
        OUT._is_immutable = False
        OUT._cache = {}
        sig_on()
        try:
            OUT.Data = MatInverse(self.Data)
        except ZeroDivisionError:
            # Attempting to invert singular matrices happens
            # in the tests, and we make the special case here
            # so that the sig_on/off count is fine.
            sig_off()
            raise
        sig_off()
        if OUT.Data != NULL:
            return OUT
        raise ArithmeticError("This matrix is not invertible")

    def transpose(Matrix_gfpn_dense self):
        """
        Return the transposed matrix.

        EXAMPLES::

            sage: K.<x> = GF(9)
            sage: M = MatrixSpace(K, 2,4)(sorted(list(K)[1:]))
            sage: M
            [      1       2       x   x + 1]
            [  x + 2     2*x 2*x + 1 2*x + 2]
            sage: M.transpose()
            [      1   x + 2]
            [      2     2*x]
            [      x 2*x + 1]
            [  x + 1 2*x + 2]

        """
        if self.Data == NULL:
            raise ValueError("The matrix must not be empty")
        cdef Matrix_gfpn_dense OUT = self._new(self._ncols, self._nrows)
        OUT._is_immutable = False
        OUT._cache = {}
        sig_on()
        OUT.Data = MatTransposed(self.Data)
        sig_off()
        return OUT

    def order(self):
        """
        Return the multiplicative order of this matrix.

        EXAMPLES::

            sage: K.<x> = GF(27)
            sage: M = MatrixSpace(K, 4)([2*x^2 + 2*x, 2*x^2 + x, 2*x^2 + x + 1,
            ....: x^2 + x + 2, x + 2, x^2, 2*x + 2, 2*x^2 + 2*x, 2*x^2 + 1,
            ....: 1, 2, x^2 + 2*x + 1, x^2 + x + 2, x + 1, 2*x^2 + 2*x, x^2 + x])
            sage: M.order()                 # optional: meataxe
            104
            sage: M^104 == 1
            True
            sage: M^103 == 1
            False

        """
        if self.Data == NULL:
            raise ValueError("The matrix must not be empty")
        if self.Data.Nor != self.Data.Noc:
            raise ValueError("only defined for square matrices")
        sig_on()
        o = MatOrder(self.Data)
        sig_off()
        if o == -1:
            raise ArithmeticError("order too large")
        else:
            return o

###################
## Gauss algorithm

    def left_kernel_matrix(self):
        """
        Return the null space of this matrix, represented as a matrix.

        NOTE:

        - For a matrix `M`, ``M.left_kernel_matrix()*M`` is a null matrix.
        - The command `M.left_kernel()` uses a generic implementation in Sage,
          that relies on computing the echelon form of the transposed
          matrix. This method however uses a MeatAxe function to compute
          the left kernel matrix.

        EXAMPLES::

            sage: K.<x> = GF(25)
            sage: M = MatrixSpace(K, 10)()
            sage: entries = [((0, 2), x), ((0, 4), 3*x + 2),
            ....: ((0, 8), 2*x), ((1, 1), x + 3), ((1, 5), 3*x),
            ....: ((1, 6), x + 4), ((2, 3), 2*x), ((2, 5), 4*x + 1),
            ....: ((2, 6), 4), ((3, 4), x + 4), ((3, 5), x + 1),
            ....: ((5, 5), 3*x), ((5, 7), x + 3), ((6, 1), x),
            ....: ((6, 2), x + 1), ((6, 5), x + 1), ((8, 2), 4),
            ....: ((8, 8), 4), ((8, 9), x + 3), ((9, 8), 4*x + 2)]
            sage: for (i,j),v in entries: M[i,j] = v
            sage: M.left_kernel()
            Vector space of degree 10 and dimension 2 over Finite Field in x of size 5^2
            Basis matrix:
            [0 0 0 0 1 0 0 0 0 0]
            [0 0 0 0 0 0 0 1 0 0]
            sage: M.left_kernel_matrix()    # optional: meataxe
            [0 0 0 0 1 0 0 0 0 0]
            [0 0 0 0 0 0 0 1 0 0]

        """
        cdef Matrix_gfpn_dense OUT = self.fetch("left_kernel_matrix")
        if OUT is not None:
            return OUT
        if self.Data == NULL:
            raise ValueError("The matrix must not be empty")
        OUT = type(self).__new__(type(self))
        OUT.Data = MatNullSpace(self.Data)
        OUT._nrows = OUT.Data.Nor
        OUT._ncols = OUT.Data.Noc
        OUT._is_immutable = False
        OUT._parent = self.matrix_space(OUT._nrows, OUT._ncols, False)
        OUT._base_ring = self._base_ring
        OUT._converter = self._converter
        OUT._cache = {}
        self.cache("left_kernel_matrix", OUT)
        return OUT

    def _echelon_in_place_classical(self, reduced=True, **kwds):
        """
        Change this matrix into echelon form, using classical Gaussian elimination.

        INPUT:

        - ``reduced`` (optional, default ``True``) -- will result
          in the row-reduced echelon form (otherwise, only a
          semi-echelon form results).

        EXAMPLES::

            sage: K.<x> = GF(25)
            sage: M = MatrixSpace(K, 10)()
            sage: entries = [((0, 2), x), ((0, 4), 3*x + 2),
            ....: ((0, 8), 2*x), ((1, 1), x + 3), ((1, 5), 3*x),
            ....: ((1, 6), x + 4), ((2, 3), 2*x), ((2, 5), 4*x + 1),
            ....: ((2, 6), 4), ((3, 4), x + 4), ((3, 5), x + 1),
            ....: ((5, 5), 3*x), ((5, 7), x + 3), ((6, 1), x),
            ....: ((6, 2), x + 1), ((6, 5), x + 1), ((8, 2), 4),
            ....: ((8, 8), 4), ((8, 9), x + 3), ((9, 8), 4*x + 2)]
            sage: for (i,j),v in entries: M[i,j] = v
            sage: M
            [      0       0       x       0 3*x + 2       0       0       0     2*x       0]
            [      0   x + 3       0       0       0     3*x   x + 4       0       0       0]
            [      0       0       0     2*x       0 4*x + 1       4       0       0       0]
            [      0       0       0       0   x + 4   x + 1       0       0       0       0]
            [      0       0       0       0       0       0       0       0       0       0]
            [      0       0       0       0       0     3*x       0   x + 3       0       0]
            [      0       x   x + 1       0       0   x + 1       0       0       0       0]
            [      0       0       0       0       0       0       0       0       0       0]
            [      0       0       4       0       0       0       0       0       4   x + 3]
            [      0       0       0       0       0       0       0       0 4*x + 2       0]
            sage: M.echelon_form()   # indirect doctest
            [      0       1       0       0       0       0       0       0       0 4*x + 4]
            [      0       0       1       0       0       0       0       0       0 4*x + 2]
            [      0       0       0       1       0       0       0       0       0 3*x + 4]
            [      0       0       0       0       1       0       0       0       0 3*x + 3]
            [      0       0       0       0       0       1       0       0       0 2*x + 3]
            [      0       0       0       0       0       0       1       0       0       x]
            [      0       0       0       0       0       0       0       1       0 2*x + 2]
            [      0       0       0       0       0       0       0       0       1       0]
            [      0       0       0       0       0       0       0       0       0       0]
            [      0       0       0       0       0       0       0       0       0       0]

        A semi-echelon form can be produced by invoking the single-underscore
        method directly::

            sage: N = copy(M)
            sage: N._echelon_in_place_classical(reduced=False)      # optional: meataxe
            sage: N                                                 # optional: meataxe
            [      0       0       x       0 3*x + 2       0       0       0     2*x       0]
            [      0   x + 3       0       0       0     3*x   x + 4       0       0       0]
            [      0       0       0     2*x       0 4*x + 1       4       0       0       0]
            [      0       0       0       0   x + 4   x + 1       0       0       0       0]
            [      0       0       0       0       0     3*x       0   x + 3       0       0]
            [      0       0       0       0       0       0 2*x + 2     4*x 3*x + 3       0]
            [      0       0       0       0       0       0       0   x + 1       1   x + 3]
            [      0       0       0       0       0       0       0       0 4*x + 2       0]
            [      0       0       0       0       0       0       0       0       0       0]
            [      0       0       0       0       0       0       0       0       0       0]

        TESTS:

        We verify that the above echelon form is consistent with Sage's generic
        implementation of dense matrices::

            sage: type(M)                           # optional: meataxe
            <type 'sage.matrix.matrix_gfpn_dense.Matrix_gfpn_dense'>
            sage: MS = MatrixSpace(M.base_ring(), M.nrows(), M.ncols(), implementation='generic')
            sage: X = MS(M)
            sage: type(X)
            <type 'sage.matrix.matrix_generic_dense.Matrix_generic_dense'>
            sage: X.echelon_form()
            [      0       1       0       0       0       0       0       0       0 4*x + 4]
            [      0       0       1       0       0       0       0       0       0 4*x + 2]
            [      0       0       0       1       0       0       0       0       0 3*x + 4]
            [      0       0       0       0       1       0       0       0       0 3*x + 3]
            [      0       0       0       0       0       1       0       0       0 2*x + 3]
            [      0       0       0       0       0       0       1       0       0       x]
            [      0       0       0       0       0       0       0       1       0 2*x + 2]
            [      0       0       0       0       0       0       0       0       1       0]
            [      0       0       0       0       0       0       0       0       0       0]
            [      0       0       0       0       0       0       0       0       0       0]

        The following was a problem in a preliminary version of the code::

            sage: K.<a> = GF(25)
            sage: M = MatrixSpace(K, 2, 4)([4, 4, 1, 0, 0, 2*a+1, a+2, 1])
            sage: M
            [      4       4       1       0]
            [      0 2*a + 1   a + 2       1]
            sage: M.echelonize()
            sage: M
            [      1       0 3*a + 4 2*a + 2]
            [      0       1     2*a 3*a + 3]

        """
        if self._nrows == 0 or self._ncols == 0:
            self.cache('in_echelon_form',True)
            self.cache('rank', 0)
            self.cache('pivots', ())
            return self
        sig_on()
        MatEchelonize(self.Data)
        sig_off()
        self._cache = {}
        # Now, self.Data is in semi-echelon form.
        r = self.Data.Nor
        cdef size_t i, j, pos
        cdef PTR old, dest, src
        cdef FEL piv
        self.cache('rank', r)
        # Next, we do permutations to achieve the reduced echelon form,
        # if requested.
        if reduced:
            pivs = [(self.Data.PivotTable[i],i) for i in range(r)]
            pivs.sort()
            if pivs != [(self.Data.PivotTable[i],i) for i in range(r)] or self.Data.Nor < self._nrows:
                # We copy the row one by one, sorting their pivot positions
                old = self.Data.Data
                self.Data.Data = FfAlloc(self._nrows)
                for i, (pos,j) in enumerate(pivs):
                    # We have to move row j to row i
                    dest = self.Data.Data+FfCurrentRowSize*i
                    memcpy(dest, old+FfCurrentRowSize*j, FfCurrentRowSize)
                    self.Data.PivotTable[i] = pos
                    sig_check()
                sig_free(old)
                self.Data.Nor = self._nrows
            # Now, the pivot columns are strictly increasing.
            # We now normalize each row, and annulate everything
            # above the pivot (currently, we only know that the matrix
            # is zero below the pivots).
            for i in range(r):
                src = MatGetPtr(self.Data, i)
                piv = FfExtract(src, self.Data.PivotTable[i])
                assert piv!=FF_ZERO
                if piv != FF_ONE:
                    FfMulRow(src, mtx_tmultinv[piv])
                sig_check()
                for j in range(i):
                    dest = MatGetPtr(self.Data, j)
                    piv = FfExtract(dest, self.Data.PivotTable[i])
                    if piv != FF_ONE:
                        FfAddMulRow(dest, src, mtx_taddinv[piv])
                    else:
                        FfSubRow(dest, src)
                    sig_check()
        elif self.Data.Nor < self._nrows:
            # Some rows may have vanished. In SageMath, we
            # want that the number of rows does not change,
            # thus, we have to append zero rows.
            self.Data.Data = <PTR>check_realloc(self.Data.Data, FfCurrentRowSize*self._nrows)
            memset(self.Data.Data + FfCurrentRowSize*self.Data.Nor, FF_ZERO, FfCurrentRowSize*(self._nrows-self.Data.Nor))
            self.Data.Nor = self._nrows
        self.cache('pivots', tuple(self.Data.PivotTable[i] for i in range(r)))
        self.cache('in_echelon_form',True)

from sage.misc.superseded import deprecation

def mtx_unpickle(f, int nr, int nc, bytes Data, bint m):
    r"""
    Helper function for unpickling.

    EXAMPLES::

        sage: K.<x> = GF(9)
        sage: M = MatrixSpace(K,10,10).random_element()
        sage: M == loads(dumps(M))   # indirect doctest
        True
        sage: M is loads(dumps(M))
        False

    We also test pickles with zero rows and columns, as they may constitute
    corner cases. Note that in the following case, if ``sizeof(long)==8``,
    two matrix entries are stored in one byte, and therefore the last byte of
    a row is only half filled::

        sage: M = matrix(K,3,5, [x, 0, 1, 0,-1, 0, 0, 0, 0, 0, -1, 0, 1, 0, x])
        sage: loads(dumps(M)) == M
        True
        sage: M = matrix(K,3,5, [0, 1, 0,-1, 0, x, 0, 1, 0, -1, 0, 0, 0, 0, 0])
        sage: loads(dumps(M)) == M
        True

    TESTS:

    We test that a pickle created by one machine can be understood
    by other machines with different architecture (see :trac:`23411`).
    Internally, a row is stored in a memory block of length a multiple
    of ``sizeof(long)``, which may be machine dependent, but in a pickle,
    only the bytes actually containing data of the row are stored, which
    is machine independent. We chose a matrix over the field with `13` elements.
    Since `13^2<255<13^3`, two columns will be stored in one byte. Our matrix
    has five columns, thus, one row will occupy three bytes in the pickle,
    but eight bytes (if ``sizeof(long)==8``) in memory, and the pickle
    string will be six bytes, since we have two rows::

        sage: s = b'Uq\x82\xa7\x8bh'
        sage: len(s)
        6
        sage: from sage.matrix.matrix_gfpn_dense import mtx_unpickle, Matrix_gfpn_dense  # optional: meataxe
        sage: MS = MatrixSpace(GF(13), 2, 5, implementation=Matrix_gfpn_dense) # optional: meataxe
        sage: N = mtx_unpickle(MS, 2, 5, s, True)            # optional: meataxe
        sage: N                                              # optional: meataxe
        [ 6  7  8  9 10]
        [12 11 10  9  8]
        sage: type(N)                                        # optional: meataxe
        <type 'sage.matrix.matrix_gfpn_dense.Matrix_gfpn_dense'>

    We demonstrate that a slightly different pickle format can be understood
    as well, that was at some point used by some optional package::

        sage: N == mtx_unpickle(int(13), 2, 5, s, True)      # optional: meataxe
        True

    In a previous version of this optional module, the whole memory chunk
    used to store the matrix was stored. The result would have been, as
    in the following example, a string of length 16. Unpickling works, but
    results in a warning::

        sage: t = b'Uq\x82\x00\x00\x00\x00\x00\xa7\x8bh\x00\x00\x00\x00\x00'
        sage: len(t)
        16
        sage: N == mtx_unpickle(MS, 2, 5, t, True)           # optional: meataxe
        doctest:warning
        ...
        DeprecationWarning: Reading this pickle may be machine dependent
        See http://trac.sagemath.org/23411 for details.
        True

    Unpickling would even work in the case that the machine creating
    the deprecated pickle had ``sizeof(long)==9``::

        sage: t = b'Uq\x82\x00\x00\x00\x00\x00\x00\xa7\x8bh\x00\x00\x00\x00\x00\x00'
        sage: len(t)
        18
        sage: N == mtx_unpickle(MS, 2, 5, t, True)           # optional: meataxe
        True

    The data may be empty, which results in the zero matrix::

        sage: mtx_unpickle(MS, 2, 5, b'', True)              # optional: meataxe
        [0 0 0 0 0]
        [0 0 0 0 0]

    We test further corner cases. A ``ValueError`` is raised if the number
    of bytes in the pickle does not comply with either the old or the new
    pickle format (we test several code paths here)::

        sage: t = b'Uq\x82\x00\x00\x00\x00\x00\xa7\x8bh\x00\x00\x00\x00\x00\x00'
        sage: mtx_unpickle(MS, 2, 5, t, True)                # optional: meataxe
        Traceback (most recent call last):
        ...
        ValueError: Expected a pickle with 3*2 bytes, got 17 instead
        sage: t = b'Uq\x82\x00\x00\x00\x00\x00\xa7\x8bh\x00\x00\x00\x00\x00\x00'
        sage: mtx_unpickle(MS, 2, 5, t[:4], True)                # optional: meataxe
        Traceback (most recent call last):
        ...
        ValueError: Expected a pickle with 3*2 bytes, got 2*2 instead
        sage: MS = MatrixSpace(GF(13), 0, 5)
        sage: mtx_unpickle(MS, 0, 5, s, True)                # optional: meataxe
        Traceback (most recent call last):
        ...
        ValueError: This matrix pickle contains data, thus, the number of rows
        and columns must be positive
        sage: MS = MatrixSpace(GF(13), 3, 5)
        sage: mtx_unpickle(MS, 2, 5, s, True)                # optional: meataxe
        Traceback (most recent call last):
        ...
        ValueError: Inconsistent dimensions in this matrix pickle
        sage: mtx_unpickle(MatrixSpace(GF(19),0,5), 0, 5, b'', True) # optional: meataxe
        []

    """
    cdef Matrix_gfpn_dense OUT
    OUT = Matrix_gfpn_dense.__new__(Matrix_gfpn_dense)
    if isinstance(f, (int, long)):
        # This is for old pickles created with the group cohomology spkg
        Matrix_dense.__init__(OUT, MatrixSpace(GF(f, 'z'), nr, nc, implementation=Matrix_gfpn_dense))
    else:
        if f.nrows() != nr or f.ncols() != nc:
            raise ValueError("Inconsistent dimensions in this matrix pickle")
        Matrix_dense.__init__(OUT, f)
        f = OUT._base_ring.order()
    OUT.Data = MatAlloc(f, nr, nc)
    OUT._is_immutable = not m
    OUT._converter = FieldConverter(OUT._base_ring)
    cdef char *x
    cdef PTR pt
    cdef size_t lenData = len(Data)
    cdef size_t pickled_rowsize
    cdef size_t i
    if Data:
        if nr <= 0 or nc <= 0:
            raise ValueError("This matrix pickle contains data, thus, the number of rows and columns must be positive")
        pickled_rowsize = lenData//nr
        if lenData != pickled_rowsize*nr:
            raise ValueError(f"Expected a pickle with {FfCurrentRowSizeIo}*{nr} bytes, got {lenData} instead")
        x = PyBytes_AsString(Data)
        if pickled_rowsize == FfCurrentRowSizeIo:
            pt = OUT.Data.Data
            for i in range(nr):
                memcpy(pt,x,FfCurrentRowSizeIo)
                x += FfCurrentRowSizeIo
                FfStepPtr(&(pt))
        elif pickled_rowsize >= FfCurrentRowSizeIo:
            deprecation(23411, "Reading this pickle may be machine dependent")
            if pickled_rowsize == FfCurrentRowSize:
                memcpy(OUT.Data.Data, x, OUT.Data.RowSize*OUT.Data.Nor)
            else:
                pt = OUT.Data.Data
                for i in range(nr):
                    memcpy(pt,x,FfCurrentRowSizeIo)
                    x += pickled_rowsize
                    FfStepPtr(&(pt))
        else:
            raise ValueError(f"Expected a pickle with {FfCurrentRowSizeIo}*{nr} bytes, got {pickled_rowsize}*{nr} instead")
    return OUT
