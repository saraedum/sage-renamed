from sage.libs.flint.types cimport fmpz, slong, ulong, fmpz_t

cdef extern from "flint/fmpz_vec.h":
    ulong _fmpz_vec_max_limbs(const fmpz *, slong)
    void _fmpz_vec_scalar_mod_fmpz(fmpz *, const fmpz *, long, const fmpz_t)
