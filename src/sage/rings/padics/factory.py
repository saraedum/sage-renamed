"""
Factories

Factory classes and constructor functions to create `p`-adic rings

AUTHORS:

- David Roe

- Julian Rueth (2012-10-24): rewrote large parts, added support for two step
  extensions and generic extensions

EXAMPLES::

    sage: K = Qp(5); K
    5-adic Field with capped relative precision 20
    sage: R = Zp(5); R
    5-adic Ring with capped relative precision 20

Unramified extensions::

    sage: K.<u> = Qq(25); K
    Unramified Extension in u defined by (1 + O(5^20))*x^2 + (4 + O(5^20))*x + 2 + O(5^20) of 5-adic Field with capped relative precision 20
    sage: R.<u> = Zq(25); R
    Unramified Extension in u defined by (1 + O(5^20))*x^2 + (4 + O(5^20))*x + 2 + O(5^20) of 5-adic Ring with capped relative precision 20

Eisenstein extensions::

    sage: K = Qp(5)
    sage: R.<a> = K[]
    sage: L.<a> = K.extension(a^2 + 5); L
    Eisenstein Extension of 5-adic Field with capped relative precision 20 in a defined by (1 + O(5^20))*a^2 + 5 + O(5^21)

    It fills in unspecified values and checks for contradictions in the input.  It also standardizes irrelevant options so that duplicate parents are not created.

Trivial extensions::

    sage: K = Qp(5)
    sage: R.<t> = K[]
    sage: L.<t> = K.extension(t + 1); L
    Trivial extension in t defined by (1 + O(5^20))*t + 1 + O(5^20) of 5-adic Field with capped relative precision 20

    sage: K.<u> = Qq(25)
    sage: R.<t> = K[]
    sage: L.<t> = K.extension(t + u); L
    Trivial extension in t defined by (1 + O(5^20))*t + u + O(5^20) of Unramified Extension in u defined by (1 + O(5^20))*x^2 + (4 + O(5^20))*x + 2 + O(5^20) of 5-adic Field with capped relative precision 20

A totally ramified extension not defined by an Eisenstein polynomial::

    sage: K = Qp(5)
    sage: R.<a> = K[]
    sage: L.<a> = K.extension(a^2 + 125*a + 125); L
    Totally ramified extension in a defined by (1 + O(5^20))*a^2 + (5^3 + O(5^23))*a + 5^3 + O(5^23) of 5-adic Field with capped relative precision 20

An iterated Eisenstein extension::

    sage: K = Qp(5)
    sage: R.<a> = K[]
    sage: L.<a> = K.extension(a^2 + 5)
    sage: R.<b> = L[]
    sage: M.<b> = L.extension(b^2 + a); M
    Eisenstein extension in b defined by (1 + O(a^40))*b^2 + a + O(a^41) of Eisenstein Extension of 5-adic Field with capped relative precision 20 in a defined by (1 + O(5^20))*a^2 + 5 + O(5^21)
    sage: R.<c> = M[]
    sage: N.<c> = M.extension(c^2 + b); N
    Eisenstein extension in c defined by (1 + O(b^80))*c^2 + b + O(b^81) of Eisenstein extension in b defined by (1 + O(a^40))*b^2 + a + O(a^41) of Eisenstein Extension of 5-adic Field with capped relative precision 20 in a defined by (1 + O(5^20))*a^2 + 5 + O(5^21)

An unramified extension not defined by a polynomial with irreducible
reduction::

    sage: K = Qp(5)
    sage: R.<u> = K[]
    sage: L.<u> = K.extension(u^2 + 5*u + 25); L
    Unramified extension in u defined by (1 + O(5^20))*u^2 + (5 + O(5^21))*u + 5^2 + O(5^22) of 5-adic Field with capped relative precision 20

Unramified extension over Eisenstein extension::

    sage: K = Qp(5)
    sage: R.<a> = K[]
    sage: L.<a> = K.extension(a^2 + 125*a + 125)
    sage: R.<u> = L[]
    sage: M.<u> = L.extension(u^2 + u + 1); M
    Unramified extension in u defined by (1 + O(pi^20))*u^2 + (1 + O(pi^20))*u + 1 + O(pi^20) of Totally ramified extension in a defined by (1 + O(5^20))*a^2 + (5^3 + O(5^23))*a + 5^3 + O(5^23) of 5-adic Field with capped relative precision 20

A splitting field::

    sage: K = Qp(2)
    sage: R.<x> = K[]
    sage: f = x^4+2*x^3+2*x^2-2*x+2
    sage: f.is_irreducible()
    True
    sage: L.<a> = K.extension(f)
    sage: g = f.change_ring(L)//(x-a)
    sage: g.is_irreducible()
    True
    sage: M.<b> = L.extension(g) # long time
    sage: h = g.change_ring(M)//(x-b) # long time
    sage: h.is_irreducible() # long time
    True
    sage: N.<c> = M.extension(h, check=False) # long time, check is False for speed
    sage: len(f.change_ring(N).roots(multiplicities=False)) # long time
    4
    sage: len(f.change_ring(N).factor()) # long time
    4

.. _padic_precision:

Precision
---------

There are two notions of precision for `p`-adic elements.

The first is relative precision, which gives the number of known `p`-adic
digits::

    sage: R = Zp(5)
    sage: a = R(675); a
    2*5^2 + 5^4 + O(5^22)
    sage: a.precision_relative()
    20

The second one is absolute precision, which gives the power of the uniformizer
that this element is defined modulo::

    sage: a.precision_absolute()
    22

When creating a `p`-adic ring, one can chose from several implementations which
determine how elements keep track of their precision.

In a *capped-relative* ring, the relative precision of elements is bounded,
this is the default implementation::

    sage: R = Zp(5, 10); R
    5-adic Ring with capped relative precision 10

When an exact element is brought into such a ring, its relative precision is
truncated to the precision cap of the ring::

    sage: R(5)
    5 + O(5^11)

Consequently, an exact zero is stored to infinite absolute precision::

    sage: R(0).precision_absolute()
    +Infinity

In a *capped-absolute* ring, the absolute precision of elements is bounded::

    sage: R = Zp(5, 10, 'capped-abs')
    sage: R(5)
    5 + O(5^10)

In a *fixed-mod* ring, the absolute precision of all elements is the same. All
computations are performed module a power of the uniformizer and the elements
do not keep track of precision losses::

    sage: R = Zp(5, 10, 'fixed-mod')
    sage: R(5)
    5 + O(5^10)
    sage: R(0)
    O(5^10)

Notice how the following computation differs in these three precision models::

    sage: R = Zp(5, 10, 'fixed-mod')
    sage: a = R(5^9); a
    5^9 + O(5^10)
    sage: b = a>>9; b
    1 + O(5^10)
    sage: a + b
    1 + 5^9 + O(5^10)

    sage: R = Zp(5, 10, 'capped-abs')
    sage: a = R(5^9); a
    5^9 + O(5^10)
    sage: b = a>>9; b
    1 + O(5)
    sage: a + b
    1 + O(5)

    sage: R = Zp(5, 10, 'capped-rel')
    sage: a = R(5^9); a
    5^9 + O(5^19)
    sage: b = a>>9; b
    1 + O(5^10)
    sage: a + b
    1 + 5^9 + O(5^10)

Eventually, in a *lazy* implementation, elements will be able to increase their
precision upon request. This is currently not implemented.

.. _padic_printing:

Printing
--------

Upon creation of a `p`-adic ring, several parameters control how elements
print. The following list describe the effect of different values for the
parameter ``print_mode``:

* ``'series'`` (the default):

    Elements are displayed as series in the uniformizer::

        sage: K = Qp(5, 10, print_mode='series')
        sage: K(70700)
        3*5^2 + 3*5^4 + 2*5^5 + 4*5^6 + O(5^12)
        sage: K(-70700)
        2*5^2 + 4*5^3 + 5^4 + 2*5^5 + 4*5^7 + 4*5^8 + 4*5^9 + 4*5^10 + 4*5^11 + O(5^12)

        sage: K.<u> = Qq(9, 10, 'capped-rel', print_mode='series')
        sage: (1+2*u)^4
        2 + (2*u + 2)*3 + (2*u + 1)*3^2 + O(3^10)
        sage: -3*(1+2*u)^4
        3 + u*3^2 + 3^3 + (2*u + 2)*3^4 + (2*u + 2)*3^5 + (2*u + 2)*3^6 + (2*u + 2)*3^7 + (2*u + 2)*3^8 + (2*u + 2)*3^9 + (2*u + 2)*3^10 + O(3^11)
        sage: ~(3*u+18)
        (u + 2)*3^-1 + 1 + 2*3 + (u + 1)*3^2 + 3^3 + 2*3^4 + (u + 1)*3^5 + 3^6 + 2*3^7 + (u + 1)*3^8 + O(3^9)

    ``print_pos`` controls whether negative integers can be used in the
    coefficients::

        sage: K = Qp(5, 10, print_mode='series', print_pos=False)
        sage: K(70700)
        -2*5^2 + 5^3 - 2*5^4 - 2*5^5 + 5^7 + O(5^12)
        sage: K(-70700)
        2*5^2 - 5^3 + 2*5^4 + 2*5^5 - 5^7 + O(5^12)

    This also works for extensions::

        sage: K.<u> = Qq(9, print_mode='series', print_pos=False)
        sage: (1+2*u)^4
        -1 - u*3 - 3^2 + (u + 1)*3^3 + O(3^20)
        sage: -3*(1+2*u)^4
        3 + u*3^2 + 3^3 + (-u - 1)*3^4 + O(3^21)

    ``names`` affects how the generator is printed. For base rings, this
    controls how the prime is printed::

        sage: K.<p> = Qp(5)
        sage: p
        p + O(p^21)

    In general, ``ram_name`` controls how the uniformizer is printed::

        sage: K.<u> = Qq(9, print_mode='series', ram_name='p')
        sage: 3*(1+2*u)^4
        2*p + (2*u + 2)*p^2 + (2*u + 1)*p^3 + O(p^21)

    ``print_max_ram_terms`` limits the number of powers of the
    uniformizer that appear::

        sage: K = Qp(5, 10, print_mode='series', print_max_ram_terms=4)
        sage: repr(R(-70700)) # have to use repr() here so the doctest does not get confused by the ...
        '2*5^2 + 4*5^3 + 5^4 + 2*5^5 + ... + O(5^12)'

        sage: K.<u> = Qq(9, print_mode='series', print_max_ram_terms=4)
        sage: repr(-3*(1+2*u)^4)
        '3 + u*3^2 + 3^3 + (2*u + 2)*3^4 + ... + O(3^21)'

    In extensions, ``print_max_unram_terms`` limits the number of terms that
    appear in a coefficient of a power of the uniformizer::

        sage: K.<u> = Qq(128, prec = 8, print_mode='series')
        sage: repr((1+u)^9)
        '(u^3 + 1) + (u^5 + u^4 + u^3 + u^2)*2 + (u^6 + u^5 + u^4 + u + 1)*2^2 + (u^5 + u^4 + u^2 + u + 1)*2^3 + (u^6 + u^5 + u^4 + u^3 + u^2 + u + 1)*2^4 + (u^5 + u^4)*2^5 + (u^6 + u^5 + u^4 + u^3 + u + 1)*2^6 + (u + 1)*2^7 + O(2^8)'
        sage: K.<u> = Qq(128, prec = 8, print_mode='series', print_max_unram_terms = 3)
        sage: repr((1+u)^9)
        '(u^3 + 1) + (u^5 + u^4 + ... + u^2)*2 + (u^6 + u^5 + ... + 1)*2^2 + (u^5 + u^4 + ... + 1)*2^3 + (u^6 + u^5 + ... + 1)*2^4 + (u^5 + u^4)*2^5 + (u^6 + u^5 + ... + 1)*2^6 + (u + 1)*2^7 + O(2^8)'
        sage: K.<u> = Qq(128, prec = 8, print_mode='series', print_max_unram_terms = 2)
        sage: repr((1+u)^9)
        '(u^3 + 1) + (u^5 + ... + u^2)*2 + (u^6 + ... + 1)*2^2 + (u^5 + ... + 1)*2^3 + (u^6 + ... + 1)*2^4 + (u^5 + u^4)*2^5 + (u^6 + ... + 1)*2^6 + (u + 1)*2^7 + O(2^8)'
        sage: K.<u> = Qq(128, prec = 8, print_mode='series', print_max_unram_terms = 1)
        sage: repr((1+u)^9)
        '(u^3 + ...) + (u^5 + ...)*2 + (u^6 + ...)*2^2 + (u^5 + ...)*2^3 + (u^6 + ...)*2^4 + (u^5 + ...)*2^5 + (u^6 + ...)*2^6 + (u + ...)*2^7 + O(2^8)'
        sage: K.<u> = Qq(128, prec = 8, print_mode='series', print_max_unram_terms = 0)
        sage: repr((1+u)^9 - 1 - u^3)
        '(...)*2 + (...)*2^2 + (...)*2^3 + (...)*2^4 + (...)*2^5 + (...)*2^6 + (...)*2^7 + O(2^8)'

    ``print_sep``, ``print_alphabet``, and ``print_max_terse_terms`` have no effect.

* ``'val-unit'``:

    Elements are displayed as ``pi^k*u``::

        sage: K = Qp(5, print_mode='val-unit')
        sage: K(70700)
        5^2 * 2828 + O(5^22)
        sage: K(-707/5)
        5^-1 * 95367431639918 + O(5^19)

    ``print_pos`` controls whether to use negative integers::

        sage: K = Qp(5, print_mode='val-unit', print_pos=False)
        sage: K(-70700)
        5^2 * (-2828) + O(5^22)

    This also works for extensions::

        sage: K.<u> = Qq(9, 7, print_mode='val-unit', print_pos=False)
        sage: b = (1+3*u)^9 - 1; b
        3^3 * (15 - 17*u) + O(3^7)
        sage: ~b
        3^-3 * (-40 + u) + O(3)

    ``names`` affects how the generator is printed. For base rings, this
    changes how the prime is printed::

        sage: K.<pi> = Qp(5, print_mode='val-unit')
        sage: K(70700)
        pi^2 * 2828 + O(pi^22)

    In general, ``ram_name`` controls how the uniformizer is printed::

        sage: K.<u> = Qq(5, ram_name='p')
        sage: u
        p + O(p^21)

    In an extension, ``print_max_terse_terms`` controls how many terms appear
    in the unit part::

        sage: K.<u> = Qq(17^4, 6, print_mode='val-unit', print_max_terse_terms=3)
        sage: b = ~(17*(u^3-u+14)); b
        17^-1 * (22110411 + 11317400*u + 20656972*u^2 + ...) + O(17^5)
        sage: b*17*(u^3-u+14)
        1 + O(17^6)

    ``print_max_ram_terms``, ``print_sep``, ``print_max_unram_terms``, and
    ``print_alphabet`` have no effect.

* ``'terse'``

    Elements are displayed as an integer in base 10 or the quotient of an
    integer by a power of `p` (still in base 10)::

        sage: K = Qp(5, print_mode='terse')
        sage: K(70700)
        70700 + O(5^22)
        sage: K(-70700)
        2384185790944925 + O(5^22)
        sage: K(707/5^2)
        707/5^2 + O(5^18)

    ``print_pos`` controls whether to use a balanced representation::

        sage: K = Qp(5, print_mode='terse', print_pos=False)
        sage: K(-70700)
        -70700 + O(5^22)
        sage: K(-707/5)
        -707/5 + O(5^19)

    ``names`` affects how the generator is printed. For a base field, this
    changes how the prime is printed::

        sage: K.<unif> = Qp(5, print_mode='terse')
        sage: K(-707/5)
        95367431639918/unif + O(unif^19)
        sage: K(-707/5^10)
        95367431639918/unif^10 + O(unif^10)

    In an extension, ``ram_name`` controls how the uniformizer is printed::

        sage: K.<u> = Qq(125, print_mode='terse', ram_name='p')
        sage: (u - 1/5)^6
        95367431620001/p^6 + 18369/p^5*u + 1353/p^3*u^2 + O(p^14)

    ``print_max_terse_terms`` controls how many terms of the polynomial are
    shown::

        sage: K.<u> = Qq(625, print_mode='terse', print_max_terse_terms=2)
        sage: (u-1/5)^6
        106251/5^6 + 49994/5^5*u + ... + O(5^14)

    ``print_max_ram_terms``, ``print_max_unram_terms``, ``print_sep`` and
    ``print_alphabet`` have no effect.

* ``'digits'``:

    Elements are displayed as a string of base `p` digits::

        sage: K = Qp(5, print_mode='digits')
        sage: repr(K(70700)) # the repr() is necessary in these doctests to handle the leading ...
        '...4230300'
        sage: repr(K(-70700))
        '...4444444444444440214200'
        sage: repr(K(-707/5))
        '...4444444444444443413.3'
        sage: repr(K(-707/5^2))
        '...444444444444444341.33'

    Note that it's not possible to read off the precision from the
    representation in this mode.

    Naturally, this mode can not be used in unramified extensions::

        sage: K.<u> = Qq(25, print_mode='digits')
        Traceback (most recent call last):
        ...
        ValueError: digits printing mode only usable for totally ramified extensions with p at most the length of the alphabet (default 62).  Try using print_mode = 'bars' instead.

    ``print_max_ram_terms`` limits the number of digits that are printed.  Note
    that if the valuation of the element is very negative, more digits will be
    printed::

        sage: K = Qp(5, print_mode='digits', print_max_ram_terms=4)
        sage: repr(K(-70700))
        '...214200'
        sage: repr(K(-707/5^2))
        '...41.33'
        sage: repr(K(-707/5^6))
        '...?.434133'
        sage: repr(K(-707/5^6,absprec=-2))
        '...?.??4133'
        sage: repr(K(-707/5^4))
        '...?.4133'

    ``print_alphabet`` defines the symbols used to print the digits, defaults
    to the tuple of length 62 composed of ``'0'`` to ``'9'``, followed by
    ``'A'`` to ``'Z'``, followed by ``'a'`` to ``'z'``.

    The digits printing mode is only available if `p` is at most the length of
    ``print_alphabet``::

        sage: K = Qp(5, print_mode='digits', print_alphabet=('zero','one','two','three','four'))
        sage: repr(K(707))
        '...onezerothreeonetwo'

        sage: K = Qp(7, print_mode='digits', print_alphabet=('zero','one','two','three','four'))
        Traceback (most recent call last):
        ...
        ValueError: digits printing mode only usable for totally ramified extensions with p at most the length of the alphabet (default 62).  Try using print_mode = 'bars' instead.

    Restriction: you can only use the digits printing mode for
    small primes.  Namely, `p` must be less than the length of the
    alphabet tuple (default alphabet has length 62).::

    ``print_max_terse_terms``, ``print_max_unram_terms``, ``print_pos``,
    ``names`` and ``print_sep`` have no effect.

* ``'bars'``:

   Elements are displayed as a string of base `p` digits with separators::

        sage: K = Qp(5, print_mode='bars')
        sage: repr(K(70700))
        '...4|2|3|0|3|0|0'
        sage: repr(K(-70700))
        '...4|4|4|4|4|4|4|4|4|4|4|4|4|4|4|0|2|1|4|2|0|0'
        sage: repr(K(-707/5^2))
        '...4|4|4|4|4|4|4|4|4|4|4|4|4|4|4|3|4|1|.|3|3'

    This also works for extensions::

        sage: K.<u> = Qq(125)
        sage: (u+5)^6
        (4*u^2 + 3*u + 4) + (3*u^2 + 2*u)*5 + (u^2 + u + 1)*5^2 + (3*u + 2)*5^3 + (3*u^2 + u + 3)*5^4 + (2*u^2 + 3*u + 2)*5^5 + O(5^20)
        sage: K.<u> = Qq(125, print_mode='bars', prec=8)
        sage: repr((u+5)^6)
        '...[2, 3, 2]|[3, 1, 3]|[2, 3]|[1, 1, 1]|[0, 2, 3]|[4, 3, 4]'
        sage: repr((u-5)^6)
        '...[0, 4]|[1, 4]|[2, 0, 2]|[1, 4, 3]|[2, 3, 1]|[4, 4, 3]|[2, 4, 4]|[4, 3, 4]'

    Note that elements with negative valuation are shown with a
    decimal point at valuation 0.::

        sage: repr((u+1/5)^6)
        '...[3]|[4, 1, 3]|.|[1, 2, 3]|[3, 3]|[0, 0, 3]|[0, 1]|[0, 1]|[1]'
        sage: repr((u+1/5)^2)
        '...[0, 0, 1]|.|[0, 2]|[1]'

    If not enough precision is known, ``'?'`` is used instead.::

        sage: repr((u+K(1/5,relprec=3))^7)
        '...|.|?|?|?|?|[0, 1, 1]|[0, 2]|[1]'

    Again, it is not possible to read off the precision from this
    representation::

        sage: b = u + 3; repr(b)
        '...[3, 1]'
        sage: c = u + K(3, 4); repr(c)
        '...[3, 1]'
        sage: b.precision_absolute()
        8
        sage: c.precision_absolute()
        4

    ``print_pos`` controls whether the digits can be negative::

        sage: K = Qp(5, print_mode='bars',print_pos=False)
        sage: repr(K(-70700))
        '...-1|0|2|2|-1|2|0|0'

    ``print_max_ram_terms`` limits the number of digits that are printed.  Note
    that if the valuation of the element is very negative, more digits will be
    printed::

        sage: K = Qp(5, print_mode='bars', print_max_ram_terms=4)
        sage: repr(K(-70700))
        '...2|1|4|2|0|0'
        sage: repr(K(-707/5^2))
        '...4|1|.|3|3'
        sage: repr(K(-707/5^6))
        '...|.|4|3|4|1|3|3'
        sage: repr(K(-707/5^6,absprec=-2))
        '...|.|?|?|4|1|3|3'
        sage: repr(K(-707/5^4))
        '...|.|4|1|3|3'

    Note that this puts a cap on the relative precision, not the
    absolute precision::

        sage: K.<u> = Qq(125, print_mode='bars', print_max_ram_terms=3, print_pos=False)
        sage: repr((u-5)^6)
        '...[0, 0, -1]|[-2]|[-1, -2, -1]'
        sage: repr(5*(u-5)^6+50)
        '...[0, 0, -1]|[]|[-1, -2, -1]|[]'

    However, if the element has negative valuation, digits are shown
    up to the decimal point.::

        sage: repr((u-1/5)^6)
        '...|.|[-2, -1, -1]|[2, 2, 1]|[0, 0, -2]|[0, -1]|[0, -1]|[1]'

    ``print_sep`` controls the separation character::

        sage: K = Qp(5, print_mode='bars', print_sep='][')
        sage: repr(K(70700))
        '...4][2][3][0][3][0][0'

    In an extension, ``print_max_unram_terms`` controls how many terms are
    shown in each *digit*::

        sage: K.<u> = Qq(125, print_mode='bars')
        sage: b = (u+5)^6
        sage: with local_print_mode(K, {'max_unram_terms': 3}): repr(b)
        '...[2,..., 3, 2]|[3,..., 1, 3]|[2, 3]|[1,..., 1, 1]|[0,..., 2, 3]|[4,..., 3, 4]'
        sage: with local_print_mode(K, {'max_unram_terms': 2}): repr(b)
        '...[2,..., 2]|[3,..., 3]|[2, 3]|[1,..., 1]|[0,..., 3]|[4,..., 4]'
        sage: with local_print_mode(K, {'max_unram_terms': 1}): repr(b)
        '...[..., 2]|[..., 3]|[..., 3]|[..., 1]|[..., 3]|[..., 4]'
        sage: with local_print_mode(K, {'max_unram_terms':0}): repr(b-75*a)
        '...[...]|[...]|[...]|[...]|[...]|[...]|[...]|[...]|[...]|[]|[]|[]|[]|[]|[...]|[...]|[...]|[...]|[...]|[...]'

    ``names``, ``print_max_terse_terms``, and ``print_alphabet`` have no
    effect.

In general, equality of rings depends on printing options::

    sage: K = Qp(5, print_max_ram_terms=4)
    sage: L = Qp(5, print_max_ram_terms=5)
    sage: K == L
    False

However, irrelevant options are not taken into account::

    sage: K = Qp(5, print_alphabet=())
    sage: L = Qp(5, print_alphabet=('0'))
    sage: K == L
    True

.. _padic_modulus:

Moduli
------

To create an extension ring, the modulus can be given in a number of ways:

* Implicitely:

    For unramified extensions, the modulus does not have to be specified::

        sage: K.<a> = Qq(27); K
        Unramified Extension in a defined by (1 + O(3^20))*x^3 + (2 + O(3^20))*x + 1 + O(3^20) of 3-adic Field with capped relative precision 20

    In this case, the modulus is the standard lift of the generator chosen for
    `\mathbb{F}_q`::

        sage: GF(27, 'a').modulus()
        x^3 + 2*x + 1
        sage: K.modulus()
        (1 + O(3^20))*x^3 + (2 + O(3^20))*x + 1 + O(3^20)

* As a polynomial:

    The base ring can be `\mathbb{Z}`, `\mathbb{Q}`, `\mathbb{Z}_p`, `\mathbb{Q}_p`, `\mathbb{F}_p`.::

        sage: P.<x> = ZZ[]
        sage: R.<a> = Qq(27, modulus = x^3 + 2*x + 1); R.modulus()
        (1 + O(3^20))*x^3 + (2 + O(3^20))*x + 1 + O(3^20)
        sage: P.<x> = QQ[]
        sage: S.<a> = Qq(27, modulus = x^3 + 2*x + 1)
        sage: P.<x> = Zp(3)[]
        sage: T.<a> = Qq(27, modulus = x^3 + 2*x + 1)
        sage: P.<x> = Qp(3)[]
        sage: U.<a> = Qq(27, modulus = x^3 + 2*x + 1)
        sage: P.<x> = GF(3)[]
        sage: V.<a> = Qq(27, modulus = x^3 + 2*x + 1)

    Which form the modulus is given in has no effect on the extension
    produced::

        sage: R == S, S == T, T == U, U == V
        (True, True, True, False)

    unless the precision of the modulus differs. In the case of ``V``, the
    modulus is only given to precision 1, so the resulting field has a
    precision cap of 1::

        sage: V.precision_cap()
        1
        sage: U.precision_cap()
        20
        sage: P.<x> = Qp(3)[]
        sage: modulus = x^3 + (2 + O(3^7))*x + (1 + O(3^10))
        sage: modulus
        (1 + O(3^20))*x^3 + (2 + O(3^7))*x + 1 + O(3^10)
        sage: W.<a> = Qq(27, modulus = modulus); W.precision_cap()
        7

* As a symbolic expression:

        sage: x = var('x')
        sage: X.<a> = Qq(27, modulus = x^3 + 2*x + 1)
        sage: X.modulus()
        (1 + O(3^20))*x^3 + (2 + O(3^20))*x + 1 + O(3^20)
        sage: X == R
        True

"""
#*****************************************************************************
#       Copyright (C) 2007-2010 David Roe <roed@math.harvard.edu>
#                     2012-2013 Julian Rueth <julian.rueth@fsfe.org>
#
#  Distributed under the terms of the GNU General Public License (GPL)
#  as published by the Free Software Foundation; either version 2 of
#  the License, or (at your option) any later version.
#                  http://www.gnu.org/licenses/
#*****************************************************************************

from sage.rings.integer_ring import ZZ
from sage.structure.factory import UniqueFactory
import padic_printing

class AbstractFactory(UniqueFactory):
    r"""
    Abstract base class for factories for `p`-adic rings.

    INPUT:

    - ``constructors`` -- a dictionary from strings to callables, mapping
      precision types to their respective implementation

    EXAMPLES::

        sage: from sage.rings.padics.factory import AbstractFactory
        sage: zp = AbstractFactory("zp", {"capped-rel" : ZpCR})

    """
    def __init__(self, name, constructors):
        r"""
        Initialization.

        TESTS::

            sage: from sage.rings.padics.factory import AbstractFactory
            sage: isinstance(Zp, AbstractFactory)
            True
            sage: isinstance(Qp, AbstractFactory)
            True

        """
        UniqueFactory.__init__(self, name)
        self._constructors = constructors

    def _create_key_printing(self, print_mode, defaults, print_pos, print_sep, print_alphabet, print_max_ram_terms, print_max_unram_terms, print_max_terse_terms, names):
        r"""
        Shared functionality for ``create_key`` to normalize parameters related
        to printing and fill in default values.

        TESTS::

            sage: Zp._create_key_printing(None, {"print_mode":"series"}, None, None, None, None, None, None, None)
            ('series', None, None, None, None, None, None, None)

        """
        # if print_mode is a dictionary of parameters, pull out the parameters
        # if they don't contradict the parameters explicitely given
        if isinstance(print_mode, dict):
            for a,b in [("pos",print_pos), ("sep",print_sep), ("alphabet",print_alphabet), ("max_ram_terms",print_max_ram_terms), ("max_unram_terms",print_max_unram_terms), ("max_terse_terms",print_max_terse_terms)]:
                if a in print_mode:
                    if b is not None and print_mode[a] != b:
                        raise ValueError("contradicting parameters given for `%s`: `%s` and `%s`"%(a,print_mode[a],b))
                else:
                    print_mode[a] = b

            print_pos = print_mode["pos"]
            print_sep = print_mode["sep"]
            print_alphabet = print_mode["alphabet"]
            print_max_ram_terms = print_mode["max_ram_terms"]
            print_max_unram_terms = print_mode["max_unram_terms"]
            print_max_terse_terse = print_mode["max_terse_terms"]
            if "mode" in print_mode:
                print_mode = print_mode["mode"]
            else:
                print_mode = None

        # fill unspecified parameters with default values
        def fill_with_default(key, value):
            if value is None:
                if key in defaults:
                    return defaults[key]
            return value

        print_mode = fill_with_default("print_mode", print_mode)
        print_pos = fill_with_default("print_pos", print_pos)
        print_sep = fill_with_default("print_sep", print_sep)
        print_alphabet = fill_with_default("print_alphabet", print_alphabet)
        if print_alphabet is not None: print_alphabet = tuple(print_alphabet)
        print_max_ram_terms = fill_with_default("print_max_ram_terms", print_max_ram_terms)
        print_max_unram_terms = fill_with_default("print_max_unram_terms", print_max_unram_terms)
        print_max_terse_terms = fill_with_default("print_max_terse_terms", print_max_terse_terms)

        # eliminate irrelevant print options
        if print_mode == "series":
            print_alphabet = None
            print_sep = None
            print_max_terse_terms = None
        elif print_mode == "val-unit":
            print_alphabet = None
            print_max_ram_terms = None
            print_sep = None
            print_max_unram_terms = None
        elif print_mode == "terse":
            print_alphabet = None
            print_max_ram_terms = None
            print_sep = None
            print_max_unram_terms = None
        elif print_mode == "digits":
            print_pos = None
            print_sep = None
            print_max_terse_terms = None
            print_max_unram_terms = None
        elif print_mode == "bars":
            print_alphabet = None
            print_max_terse_terms = None
        else:
            raise ValueError("unknown print mode `%s`"%print_mode)

        return print_mode, print_pos, print_sep, print_alphabet, print_max_ram_terms, print_max_unram_terms, print_max_terse_terms, names

    def _normalize_version(self, version, key):
        r"""
        Bring a ``key`` of an older ``version`` into the current format.

        INPUT:

        - ``version`` -- a version tuple

        - ``key`` -- a tuple of parameters

        EXAMPLES::

            sage: Qp._normalize_version((3,1), (2, 10, "capped-rel", "terse", None))
            (2, 10, 'capped-rel', 'terse', '2', None, None, None, None, None)

        """
        return key

    def create_object(self, version, key):
        """
        Create an object from the ``key``.

        TESTS::

            sage: Qp.create_object((3,4,2),(5, 41, 'capped-rel', 'series', '5', True, '|', (), -1))
            5-adic Field with capped relative precision 41

        """
        key = self._normalize_version(version, key)
        type, kwargs = self._decode_key(key)

        if type not in self._constructors:
            raise ValueError("unsupported precision type `%s`"%(type,))

        return self._constructors[type](**kwargs)

#####################################
#                                   #
#    p-adic base rings Zp and Qp    #
#                                   #
#####################################
class BaseFactory(AbstractFactory):
    r"""
    Return a `p`-adic ring.

    INPUT:

    - ``p`` -- an integer, the `p` in `\mathbb{Q}_p`

    - ``prec`` -- an integer or ``None`` (default: ``None``), the precision cap
      of the ring, see :ref:`padic_precision`

    - ``type`` -- a string (default: ``'capped-rel'``), the precision type of
      this ring, see :ref:`padic_precision`

    - ``print_mode`` -- a dictionary or one of ``'series'``, ``'val-unit'``,
      ``'terse'``, ``'digits'``, ``'bars'``, or ``None`` (default: ``None``),
      the way elements of this ring are printed, see :ref:`padic_printing`. If
      this is a dictionary, then the other printing parameters are read from it.

    - ``halt`` -- an integer or ``None`` (default: ``None``), currently
      irrelevant (to be used for lazy ring)

    - ``names`` -- a string, tuple consisting of a single string, or ``None``
      (default: ``None``), the string to print for `p`

    - ``print_pos`` -- a boolean (default: ``False``), whether to only use
      positive integers in the representations of elements, see
      :ref:`padic_printing`.

    - ``print_sep`` -- a string or ``None`` (default: ``None``), the separator
      character used when ``print_mode`` is ``'bars'``, see :ref:`padic_printing`

    - ``print_alphabet`` -- a tuple of strings or ``None`` (default: ``None``),
      the digits to use when ``print_mode`` is ``'digits'``, see
      :ref:`padic_printing`

    - ``print_max_ram_terms`` -- an integer or ``None`` (default: ``None``),
      the maximum number of terms to show in the series expansion, see
      :ref:`padic_printing`

    - ``check`` -- a boolean (default: ``True``), whether to check that ``p``
      is prime.

    EXAMPLES::

        sage: K = Qp(5); K
        5-adic Field with capped relative precision 20
        sage: R = Zp(5); R
        5-adic Ring with capped relative precision 20

    TESTS::

        sage: K = Qp(15, check=False)
        sage: a = K(999); a
        9 + 6*15 + 4*15^2 + O(15^20)

    """
    def create_key(self, p, prec = None, type = 'capped-rel', print_mode = None, halt = None, names = None, ram_name = None, print_pos = None, print_sep = None, print_alphabet = None, print_max_ram_terms = None, check = True, implementation = None):
        r"""
        Create a key which can be used to cache the `p`-adic ring specified by
        the parameters.

        See the classes docstring for the meaning of the parameters.

        This method essentially normalizes the parameters and fills in default
        values.

        TESTS::

            sage: Qp.create_key(5)
            (5, 20, 'capped-rel', 'series', '5', True, None, None, -1, None)
            sage: Zp.create_key(5)
            (5, 20, 'capped-rel', 'series', '5', True, None, None, -1, None)

        """
        # normalize parameters and fill in default values
        p = ZZ(p)
        if check:
            if not p.is_prime():
                raise ValueError("p must be prime")

        if prec is None:
            prec = 20
        prec = ZZ(prec)

        if halt is None:
            halt = 40
        halt = ZZ(halt)

        if isinstance(names, tuple):
            if len(names) != 1:
                raise ValueError("names must be a tuple consisting of one string")
            names = names[0]
        if ram_name is not None and names is not None:
            if ram_name != names:
                raise ValueError("ram_name and names must coincide")
        if ram_name is not None:
            names = ram_name
        if names is None:
            names = str(p)
        names = (names,)

        print_mode, print_pos, print_sep, print_alphabet, print_max_ram_terms, print_max_unram_terms, print_max_terse_terms, names = self._create_key_printing(print_mode, {"print_mode":padic_printing._printer_defaults.mode(), "print_pos":not padic_printing._printer_defaults.allow_negatives(), "print_sep":padic_printing._printer_defaults.sep(), "print_alphabet":padic_printing._printer_defaults.alphabet(), "print_max_ram_terms":padic_printing._printer_defaults.max_series_terms()}, print_pos, print_sep, print_alphabet, print_max_ram_terms, None, None, names)

        # eliminate irrelevant print options not handled by _create_key_printing
        if p == 2:
            print_pos = None

        return p, prec, type, print_mode, names[0], print_pos, print_sep, print_alphabet, print_max_ram_terms, implementation

    def _normalize_version(self, version, key):
        r"""
        Bring a ``key`` of an older ``version`` into the current format.

        INPUT:

        - ``version`` -- a version tuple

        - ``key`` -- a tuple of parameters

        EXAMPLES::

            sage: Qp._normalize_version((3,1), (2, 10, "capped-rel", "terse", None))
            (2, 10, 'capped-rel', 'terse', '2', None, None, None, None, None)

        """
        version = (version[0], version[1] if len(version)>1 else 0, version[2] if len(version)>2 else 0)

        if version[0] < 3 or (version[0] == 3 and version[1] < 2) or (version[0] == 3 and version[1] == 2 and version[2] < 3):
            p, prec, type, print_mode, names = key
            return self.create_key(p, prec, type, print_mode, None, names, None, None, None, None, None, False)

        if version[0] < 4 or (len(version) > 1 and version[0] == 4 and version[1] < 5) or (len(version) > 2 and version[0] == 4 and version[1] == 5 and version[2] < 3):
            # keys changed in order to reduce irrelevant duplications: e.g. two Qps with print_mode 'series' that are identical except for different 'print_alphabet' now return the same object.
            p, prec, type, print_mode, names, print_pos, print_sep, print_alphabet, print_max_ram_terms = key
            return self.create_key(p, prec, type, print_mode, None, names, None, print_pos, print_sep, print_alphabet, print_max_ram_terms, False)

        return key

    def _decode_key(self, key):
        r"""
        Split a ``key`` into the type, determining the implementation, and the
        parameters needed to construct an instance.

        INPUT:

        - ``key`` -- a tuple

        OUTPUT:

        A string determining the type of the implementation and a dictonary of
        parameters.

        EXAMPLES:

            sage: Qp._decode_key((2, 10, 'capped-rel', 'terse', '2', None, None, None, None, None))
            ('capped-rel',
             {'implementation': None,
              'names': '2',
              'p': 2,
              'prec': 10,
              'print_mode': {'alphabet': None,
               'max_ram_terms': None,
               'mode': 'terse',
               'pos': None,
               'ram_name': '2',
               'sep': None}})

        """
        p, prec, type, print_mode, names, print_pos, print_sep, print_alphabet, print_max_ram_terms, implementation = key
        print_mode = { "mode":print_mode, "pos":print_pos, "sep":print_sep, "alphabet":print_alphabet, "ram_name":names, "max_ram_terms":print_max_ram_terms }
        return type, {"p":p, "prec":prec, "print_mode":print_mode, "names":names, "implementation":implementation}

import padic_base_leaves
Qp = BaseFactory("Qp", { "capped-rel":padic_base_leaves.pAdicFieldCappedRelative })
Zp = BaseFactory("Zp", { "capped-rel":padic_base_leaves.pAdicRingCappedRelative,
                         "capped-abs":padic_base_leaves.pAdicRingCappedAbsolute,
                         "fixed-mod":padic_base_leaves.pAdicRingFixedMod })

def create_base_factory_with_type(base_factory, type):
    """
    Return a function which creates `p`-adic base rings.

    EXAMPLES:

        sage: from sage.rings.padics.factory import create_base_factory_with_type
        sage: zpca = create_base_factory_with_type(Zp, "capped-abs")
        sage: zpca(3)
        3-adic Ring with capped absolute precision 20

    """
    def create_ring(p, prec=None, print_mode=None, halt=None, names=None, print_pos=None, print_sep=None, print_alphabet=None, print_max_ram_terms=None, check=True, implementation=None):
        """
        Shortcut function to create a %s ring.

        See documentation for ``Zp`` and ``Qp`` for a description of the input
        parameters.

        EXAMPLES::

            sage: ZpCR(3, 10)
            3-adic Ring with capped relative precision 10
            sage: QpCR(3, 10)
            3-adic Field with capped relative precision 10
            sage: ZpCA(3, 10)
            3-adic Ring with capped absolute precision 10
            sage: ZpFM(3, 10)
            3-adic Ring of fixed modulus 3^10

        """%type
        return base_factory(p=p, prec=prec, print_mode=print_mode, halt=halt, names=names, print_pos=print_pos, print_sep=print_sep, print_alphabet=print_alphabet, print_max_ram_terms=print_max_ram_terms, check=check, type=type, implementation=implementation)
    return create_ring

QpCR = create_base_factory_with_type(Qp, "capped-rel")
ZpCR = create_base_factory_with_type(Zp, "capped-rel")
ZpCA = create_base_factory_with_type(Zp, "capped-abs")
ZpFM = create_base_factory_with_type(Zp, "fixed-mod")

####################################
#                                  #
#   unramified extension rings     #
#                                  #
####################################
def create_unramified_factory(base_factory):
    """
    Return a function which creates unramified extensions over a `p`-adic base
    ring.

    EXAMPLES::

        sage: from sage.rings.padics.factory import create_unramified_factory
        sage: zq = create_unramified_factory(Zp)
        sage: R.<u> = zq(9); R
        Unramified Extension in u defined by (1 + O(3^20))*x^2 + (2 + O(3^20))*x + 2 + O(3^20) of 3-adic Ring with capped relative precision 20

    """
    def create_unramified_ring(q, prec=None, type="capped-rel", modulus=None, names=None, print_mode=None, halt=None, ram_name=None, res_name=None, print_pos=None, print_sep=None, print_max_ram_terms=None, print_max_unram_terms=None, print_max_terse_terms=None, check=True, implementation=None, base_implementation=None):
        """
        Given a prime power `q = p^n`, return the unique unramified extension ring
        of degree `n`.

        INPUT:

        - ``q`` -- an integer

        - ``prec`` -- an integer or ``None`` (default: ``None``), the precision cap
          of the ring, see :ref:`padic_precision`.

        - ``type`` -- a string (default: ``'capped-rel'``), the precision type of
          this ring, see :ref:`padic_precision`

        - ``modulus`` -- a polynomial or ``None`` (default: ``None``), a polynomial
          defining an unramified extension of `\mathbb{Q}_p`, see
          :ref:`padic_modulus`.

        - ``names`` -- a string or a tuple consisting of a single string, the name
          of the generator, reducing to a generator of the residue field.

        - ``print_mode`` -- a dictionary or one of ``'series'``, ``'val-unit'``,
          ``'terse'``, ``'digits'``, ``'bars'``, or ``None`` (default: ``None``),
          the way elements of this ring are printed, see :ref:`padic_printing`. If
          this is a dictionary, then the other printing parameters are read from
          it.

        - ``halt`` -- an integer or ``None`` (default: ``None``), currently
          irrelevant (to be used for lazy ring)

        - ``ram_name`` -- a string or ``None`` (default: ``None``), controls how
          the uniformizer is printed, see :ref:`padic_printing`.

        - ``res_name`` -- a string or ``None`` (default: ``None``), the name of the
          reduction of the generator; if ``None``, ``'0'`` is appended to the name
          of the generator.

        - ``print_pos`` -- a boolean (default: ``False``), whether to only use
          positive integers in the representations of elements, see
          :ref:`padic_printing`.

        - ``print_sep`` -- a string or ``None`` (default: ``None``), the separator
          character used when ``print_mode`` is ``'bars'``, see
          :ref:`padic_printing`

        - ``print_max_ram_terms`` -- an integer or ``None`` (default: ``None``),
          the maximum number of powers of the uniformizer to print, see
          :ref:`padic_printing`

        - ``print_max_unram_terms`` -- an integer or ``None`` (default: ``None``),
          the maximum number of entries shown in a coefficient of `p`, see
          :ref:`padic_printing`

        - ``print_max_terse_terms`` -- an integer or ``None`` (default: ``None``),
          the maximum number of terms to print in a polynomial representation of an
          element, see :ref:`padic_printing`

        - ``check`` -- a boolean (default: ``True``), whether to check that ``q``
          is the power of a prime

        EXAMPLES::

            sage: R.<u> = Zq(9); R
            Unramified Extension in u defined by (1 + O(3^20))*x^2 + (2 + O(3^20))*x + 2 + O(3^20) of 3-adic Ring with capped relative precision 20
            sage: K.<u> = Qq(9); K
            Unramified Extension in u defined by (1 + O(3^20))*x^2 + (2 + O(3^20))*x + 2 + O(3^20) of 3-adic Field with capped relative precision 20

        """
        q = ZZ(q)
        F = q.factor()
        if len(F) != 1 or (check and not F[0][0].is_prime()):
            raise ValueError("q must be a prime power")
        p = F[0][0]

        if prec is None:
            prec = 20
        prec = ZZ(prec)

        if halt is None:
            halt = 40
        halt = ZZ(halt)

        base = base_factory(p=p, prec=prec, type=type, print_mode=print_mode, halt=halt, names=ram_name, print_pos=print_pos, print_sep=print_sep, print_max_ram_terms=print_max_ram_terms, check=False, implementation=base_implementation)

        if F[0][1] == 1:
            return base

        if names is None:
            raise ValueError("generator name must be specified")
        if not isinstance(names, tuple):
            names = (names,)

        if res_name is None:
            res_name = names[0] + '0'

        if modulus is None:
            from sage.rings.finite_rings.constructor import FiniteField as GF
            from sage.rings.all import PolynomialRing
            modulus = PolynomialRing(base, 'x')([base(c,prec) for c in (GF(q, res_name).modulus().change_ring(ZZ)).list()])

        return ExtensionFactory(base=base, premodulus=modulus, prec=prec, print_mode=print_mode, halt=halt, names=names, res_name=res_name, ram_name=ram_name, print_pos=print_pos, print_sep=print_sep, print_max_ram_terms=print_max_ram_terms, print_max_unram_terms=print_max_unram_terms, print_max_terse_terms=print_max_terse_terms, check=False, implementation=implementation) # no need to check irreducibility of the modulus

    return create_unramified_ring

Qq = create_unramified_factory(Qp)
Zq = create_unramified_factory(Zp)

def create_unramified_factory_with_type(base_factory, type):
    """
    Return a function which creates an unramified `p`-adic extension ring.

    EXAMPLES:

        sage: from sage.rings.padics.factory import create_unramified_factory_with_type
        sage: zqca = create_unramified_factory_with_type(Zq, "capped-abs")
        sage: zqca(3)
        3-adic Ring with capped absolute precision 20

    """
    def create_ring(q, prec=None, modulus=None, names=None, print_mode=None, halt=None, ram_name=None, print_pos=None, print_sep=None, print_max_ram_terms=None, print_max_unram_terms=None, print_max_terse_terms=None, check=True, implementation=None):
        """
        Shortcut function to create an unramified %s ring.

        See documentation for ``Zq`` and ``Qq`` for a description of the input
        parameters.

        EXAMPLES::

            sage: R.<u> = ZqCR(9, 10); R
            Unramified Extension in u defined by (1 + O(3^10))*x^2 + (2 + O(3^10))*x + 2 + O(3^10) of 3-adic Ring with capped relative precision 10
            sage: K.<u> = QqCR(9, 10); K
            Unramified Extension in u defined by (1 + O(3^10))*x^2 + (2 + O(3^10))*x + 2 + O(3^10) of 3-adic Field with capped relative precision 10
            sage: R.<u> = ZqCA(9, 10); R
            Unramified Extension in u defined by (1 + O(3^10))*x^2 + (2 + O(3^10))*x + (2 + O(3^10)) of 3-adic Ring with capped absolute precision 10
            sage: R.<u> = ZqFM(9, 10); R
            Unramified Extension in u defined by (1 + O(3^10))*x^2 + (2 + O(3^10))*x + (2 + O(3^10)) of 3-adic Ring of fixed modulus 3^10

        """%type
        return base_factory(q=q, prec=prec, modulus=modulus, names=names, print_mode=print_mode, halt=halt, ram_name=ram_name, print_pos=print_pos, print_sep=print_sep, print_max_ram_terms=print_max_ram_terms, print_max_unram_terms=print_max_unram_terms, print_max_terse_terms=print_max_terse_terms, check=check, type=type, implementation=implementation)
    return create_ring

ZqCR = create_unramified_factory_with_type(Zq, "capped-rel")
QqCR = create_unramified_factory_with_type(Qq, "capped-rel")
ZqCA = create_unramified_factory_with_type(Zq, "capped-abs")
ZqFM = create_unramified_factory_with_type(Zq, "fixed-mod")

###########################################
#                                         #
#    Eisenstein and general extensions    #
#                                         #
###########################################
class GenericExtensionFactory(AbstractFactory):
    """
    Create an extension of ``base``.

    See :meth:`ExtensionFactory` for a description of the parameters.

    EXAMPLES::

        sage: from sage.rings.padics.factory import QpExtensionFactory
        sage: K = Qp(2)
        sage: R.<x> = K[]
        sage: QpExtensionFactory(base=K, premodulus=x^2+x+1, unram_name="u")
        Unramified Extension in u defined by (1 + O(2^20))*x^2 + (1 + O(2^20))*x + 1 + O(2^20) of 2-adic Field with capped relative precision 20

    TESTS:

    A difficult totally ramified case::

        sage: K = Qp(3,60)
        sage: R.<T> = K[]
        sage: alpha = T^3/4
        sage: G = 3^3*T^3*(alpha^4 - alpha)^2 - (4*alpha^3 - 1)^3
        sage: G = G/G.leading_coefficient()
        sage: L.<a> = K.extension(G); L # long time
        Totally ramified extension in a defined by (1 + O(3^60))*T^27 + (2*3 + 3^4 + 2*3^6 + 3^9 + 3^10 + 2*3^11 + 3^14 + 3^15 + 2*3^16 + 3^19 + 3^20 + 2*3^21 + 3^24 + 3^25 + 2*3^26 + 3^29 + 3^30 + 2*3^31 + 3^34 + 3^35 + 2*3^36 + 3^39 + 3^40 + 2*3^41 + 3^44 + 3^45 + 2*3^46 + 3^49 + 3^50 + 2*3^51 + 3^54 + 3^55 + 2*3^56 + 3^59 + O(3^60))*T^18 + (3 + 3^2 + 3^5 + 3^6 + 2*3^7 + 3^9 + 3^11 + 3^12 + 2*3^13 + 3^16 + 3^17 + 2*3^18 + 3^21 + 3^22 + 2*3^23 + 3^26 + 3^27 + 2*3^28 + 3^31 + 3^32 + 2*3^33 + 3^36 + 3^37 + 2*3^38 + 3^41 + 3^42 + 2*3^43 + 3^46 + 3^47 + 2*3^48 + 3^51 + 3^52 + 2*3^53 + 3^56 + 3^57 + 2*3^58 + O(3^60))*T^9 + (2 + 2*3 + 2*3^4 + 2*3^5 + 3^6 + 3^7 + 2*3^8 + 2*3^10 + 2*3^11 + 3^12 + 3^13 + 2*3^15 + 2*3^16 + 3^17 + 3^18 + 2*3^20 + 2*3^21 + 3^22 + 3^23 + 2*3^25 + 2*3^26 + 3^27 + 3^28 + 2*3^30 + 2*3^31 + 3^32 + 3^33 + 2*3^35 + 2*3^36 + 3^37 + 3^38 + 2*3^40 + 2*3^41 + 3^42 + 3^43 + 2*3^45 + 2*3^46 + 3^47 + 3^48 + 2*3^50 + 2*3^51 + 3^52 + 3^53 + 2*3^55 + 2*3^56 + 3^57 + 3^58 + O(3^60)) of 3-adic Field with capped relative precision 60

        sage: K = Qp(2,10)
        sage: A.<x> = K[]
        sage: K1.<alpha> = K.extension(x^2+2)
        sage: B.<y> = K1[]
        sage: K2.<beta> = K1.extension(y^2+alpha)
        sage: beta^2 == -alpha
        True
        sage: beta^4 == -2
        True

    """
    @staticmethod
    def krasner_check(poly, names=None):
        r"""
        Check whether the Eisenstein polynomial ``poly`` uniquely defines an
        extension by Krasner's lemma.

        INPUT:

        - ``poly`` -- a Eisenstein polynomial over a `p`-adic ring

        - ``names`` -- a tuple of strings or ``None`` (default: ``None``), used
          internally to create an extension; a good choice can lead to speedups
          due to caching of `p`-adic extensions

        OUTPUT:

        Raise a ``ValueError`` if ``poly`` does not uniquely determine an
        extension or if its precision is insufficient to apply the algorithm.

        ALGORITHM:

        By Krasner's lemma, given `a,b` algebraic over `K`, we have that
        `K(a)\subseteq K(b)` if `v(a-b)>v(a_i-a)` for all conjugates `a_i` of
        `a`.

        We can therefore guarantee that ``poly`` uniquely defines an extension,
        if for all `a` and `c` whose minimal polynomials `f` and `g` reduce to
        ``poly``, there is a conjugate `b` of `c` such that `a,b` satisfy
        Krasner's lemma and vice versa.

        One can show that the distance `d(f,g)=min\{v(g_i-f_i)+1/n\}` with `n`
        the degree of `f` and `g` satisfies
        `d(f,g)=\sum_{a_i}\min\{v(a-b),v(a-a_i)\}` for `b` the conjugate of `c`
        closest to `a`.

        A direct computation shows that `v(a-b)>v(a_i-a)` for all `a_i` iff
        `d(f,g)<\max_{a_i\neq a}\{v(a-a_i)\}\sum_{a_i\neq a} v(a-a-i)`. The
        right hand side of this expression can be computed from the Newton
        polygon of `f(x+a)`.

        In other words, to decide if ``poly`` uniquely defines an extension, we
        compute these `v(a-a_i)` and we compute a bound on `d(f,g)`.

        EXAMPLES::

            sage: from sage.rings.padics.factory import QpExtensionFactory

            sage: K = Qp(2,2)
            sage: R.<x> = K[]
            sage: QpExtensionFactory.krasner_check( x^2 + 2*x + 2 )
            sage: QpExtensionFactory.krasner_check( x^2 + 2 )
            Traceback (most recent call last):
            ...
            ValueError: polynomial does probably not determine a unique totally ramified extension

            sage: K = Qp(2,3)
            sage: R.<x> = K[]
            sage: QpExtensionFactory.krasner_check( x^2 + 2*x + 2 )
            sage: QpExtensionFactory.krasner_check( x^2 + 2 )

        """
        if not GenericExtensionFactory.is_eisenstein(poly):
            raise ValueError("only implemented for Eisenstein polynomials")

        K = poly.base_ring()
        n = ZZ(poly.degree())

        if names is None:
            names = poly.parent().variable_names()

        # a_i-a are the roots of f(x+a)
        # the valuation of a_i-a is therefore given by the slopes of the Newton
        # polygon of f(x+a)/x which can be determined from its Taylor expansion

        # to compute the Taylor expansion, we have to work in the quotient L = K[x]/(f)
        L = K.extension(poly, names=names, check=False)
        coeffs = [(poly.derivative(i)(L.gen()),L(ZZ(i).factorial())) for i in range(1,n+1)]
        vals = [a.valuation() - b.valuation() for a,b in coeffs]

        from newton_polygon import NewtonPolygon
        NP = NewtonPolygon(vals)
        assert NP == NP.principal_part()

        for i,((c,_),v) in enumerate(zip(coeffs,vals)):
            if c.is_zero() and NP[i] == v:
                raise ValueError("insufficient precision to determine whether polynomial defines a unique extension")

        # the valuations of the a-a_i
        conjugate_vals = []
        for side,slope in zip(NP.sides(),NP.slopes()):
            conjugate_vals.extend([-slope]*(side[1][0]-side[0][0]))
        assert len(conjugate_vals) == n - 1

        # now we compute a bound on d(f,g)
        dfg = min([n*poly[i].precision_absolute() + i for i in range(n)])

        if dfg <= sum(conjugate_vals) + max(conjugate_vals):
            raise ValueError("polynomial does probably not determine a unique totally ramified extension")

    @staticmethod
    def is_eisenstein(poly):
        """
        Return whether the monic irreducible polynomial ``poly`` is Eisenstein.

        A polynomial is Eisenstein if its leading coefficient is one, the
        constant term has valuation 1 and all other coefficients have positive
        valuation.

        INPUT:

        - ``poly`` -- a polynomial over a `p`-adic ring

        EXAMPLES::

            sage: R = Zp(5)
            sage: S.<x> = R[]
            sage: f = x^4 - 75*x + 15
            sage: from sage.rings.padics.factory import ZpExtensionFactory
            sage: ZpExtensionFactory.is_eisenstein(f)
            True
            sage: g = x^4 + 75
            sage: ZpExtensionFactory.is_eisenstein(g)
            False
            sage: h = x^7 + 27*x -15
            sage: ZpExtensionFactory.is_eisenstein(h)
            False
        """
        if not poly.is_monic():
            raise ValueError("poly must be monic")
        if poly[0].valuation() != 1:
            return False
        if not all([c.valuation() for c in poly.list()[:-1]]):
            return False
        return True

    @staticmethod
    def is_trivial(poly):
        """
        Return whether the monic irreducible polynomial ``poly`` defines a
        trivial extension, i.e., whether it is linear.

        EXAMPLES::

            sage: R = Zp(5)
            sage: S.<x> = R[]
            sage: f = x^4 + 14*x + 9
            sage: from sage.rings.padics.factory import ZpExtensionFactory
            sage: ZpExtensionFactory.is_trivial(f)
            False
            sage: f = x + 1
            sage: ZpExtensionFactory.is_trivial(f)
            True

        """
        if not poly.is_monic():
            raise ValueError("poly must be monic")
        return poly.degree() == 1

    @staticmethod
    def is_totally_ramified(poly):
        """
        Return whether the monic irreducible polynomial ``poly`` defines a
        totally ramified extension.

        EXAMPLES::

            sage: R = Zp(5)
            sage: S.<x> = R[]
            sage: f = x^4 + 14*x + 9
            sage: from sage.rings.padics.factory import ZpExtensionFactory
            sage: ZpExtensionFactory.is_totally_ramified(f)
            False
            sage: f = x^2 + 5*x + 25
            sage: ZpExtensionFactory.is_totally_ramified(f) # not tested, not implemented for rings
            False

        """
        if not poly.is_monic():
            raise ValueError("poly must be monic")

        return poly.base_ring().valuation().is_totally_ramified(poly)

    @staticmethod
    def is_unramified(poly):
        """
        Return whether the monic polynomial ``poly`` is unramified.

        A monic polynomial is unramified if its reduction modulo the maximal
        ideal is irreducible.

        EXAMPLES::

            sage: R = Zp(5)
            sage: S.<x> = R[]
            sage: f = x^4 + 14*x + 9
            sage: from sage.rings.padics.factory import ZpExtensionFactory
            sage: ZpExtensionFactory.is_unramified(f)
            True
            sage: g = x^6 + 17*x + 6
            sage: ZpExtensionFactory.is_unramified(g)
            False

        TESTS:

            sage: K = Qp(3)
            sage: S.<x> = K[]
            sage: L.<x> = K.extension(209/3*x^2 + 309*x + 47/9) # indirect doctest
            Traceback (most recent call last):
            ...
            NotImplementedError: modulus not integral after normalization

        """
        if not poly.is_monic():
            raise ValueError("poly must be monic")
        if poly[0].valuation() > 0 or poly[poly.degree()].valuation() > 0:
            return False
        if any([c.valuation()<0 for c in list(poly)]):
            return False
        if not poly.map_coefficients(lambda c:c.residue(), poly.base_ring().residue_class_field()).is_irreducible():
            return False
        return True

    def _normalize_modulus(self, base, premodulus, check):
        from sage.symbolic.expression import is_Expression
        from sage.rings.polynomial.polynomial_element import is_Polynomial
        if is_Expression(premodulus):
            if len(premodulus.variables()) != 1:
                raise ValueError("modulus must be in one variable")
            modulus = premodulus.polynomial(base)
        elif is_Polynomial(premodulus):
            if premodulus.parent().ngens() != 1:
                raise ValueError("modulus must be univariate")
            modulus = premodulus.change_ring(base)
        else:
            raise ValueError("modulus must be a univariate polynomial or symbolic expression")

        if not modulus.is_monic():
            if base.is_field():
                # TODO: modulus /= modulus.leading_coefficient() does not work. There is a bug in (padic?) polynomials: /= will coerce the rhs into the lhs parent and then do the division which puts this into the fraction field of the polynomial ring
                modulus = modulus / modulus.leading_coefficient()
            else:
                modulus *= modulus.leading_coefficient().inverse_of_unit()
                if modulus.leading_coefficient().valuation() <= min(c.valuation() for c in modulus.list()):
                    modulus = modulus.map_coefficients(lambda c:c>>modulus.leading_coefficient().valuation())
                else:
                    raise NotImplementedError("modulus with leading coefficient with high valuation")

        if any([c.valuation()<0 for c in modulus.list()]):
            raise NotImplementedError("modulus not integral after normalization")

        if check:
            if modulus.is_constant():
                raise ValueError("modulus must not be constant")
            if len(modulus.list()) > modulus.degree()+1:
                raise ValueError("modulus must not have leading zero coefficients")
            if not self.is_eisenstein(modulus): # checking for Eisenstein is much faster than a general check for irreducibility (TODO: move this into the is_irreducible)
                if not modulus.is_irreducible():
                    raise ValueError("modulus must be irreducible but %s is not irreducible over %s"%(modulus,base))

        assert modulus.is_monic()
        return modulus

    def create_key_and_extra_args(self, base, premodulus, prec = None, print_mode = None, halt = None, names = None, var_name = None, res_name = None, unram_name = None, ram_name = None, print_pos = None, print_sep = None, print_max_ram_terms = None, print_max_unram_terms = None, print_max_terse_terms = None, print_alphabet=None, check=True, implementation=None):
        r"""
        Create a key which can be used to cache the `p`-adic ring specified by
        the parameters.

        See the classes docstring for the meaning of the parameters.

        This method essentially normalizes the parameters and fills in default
        values.

        TESTS::

            sage: from sage.rings.padics.factory import QpExtensionFactory
            sage: K = Qp(2)
            sage: R.<x> = K[]
            sage: QpExtensionFactory.create_key_and_extra_args(base=K, premodulus=x^2+x+1, unram_name="u")
            (('u', 2-adic Field with capped relative precision 20, (1 + O(2^20))*x^2 + (1 + O(2^20))*x + 1 + O(2^20), (1 + O(2^20))*x^2 + (1 + O(2^20))*x + 1 + O(2^20), ('u', 'u0'), 20, 40, 'series', True, None, None, -1, -1, None, 'FLINT'), {'check': True})

        """
        # a univariate polynomial over base, the actual modulus to use for the extension
        modulus = self._normalize_modulus(base, premodulus, check)

        # decide on the extension class: unramified, Eisenstein, or general
        ext = None
        if modulus.degree() == 1:
            ext = "?"
        elif self.is_eisenstein(modulus):
            ext = "e"
        elif self.is_unramified(modulus):
            ext = "u"
        else:
            ext = "?"

        print_mode, print_pos, print_sep, print_alphabet, print_max_ram_terms, print_max_unram_terms, print_max_terse_terms, names = self._create_key_printing(print_mode, {"print_mode":base.print_mode(), "print_pos":base._printer._pos(), "print_sep":base._printer._sep(), "print_max_ram_terms":base._printer._max_ram_terms(), "print_max_unram_terms":base._printer._max_unram_terms(), "print_max_terse_terms":base._printer._max_terse_terms()}, print_pos, print_sep, print_alphabet, print_max_ram_terms, print_max_unram_terms, print_max_terse_terms, names)

        # merge ram_name, unram_name into names
        if not isinstance(names, (list, tuple)):
            names = (names,)
        names = list(names)
        if names[0] is None:
            if var_name is not None:
                names[0] = var_name
            else:
                if ext == "?":
                    pass
                elif ext == "e":
                    names[0] = ram_name
                elif ext == "u":
                    names[0] = unram_name
                else:
                    assert(False)

        if names[0] is None:
            raise ValueError("name of the generator must be specified")

        if ext=="e" and ram_name is not None and ram_name != names[0]:
            raise ValueError("name of the generator is inconsistent with ram_name")
        if ext=="u" and unram_name is not None and unram_name != names[0]:
            raise ValueError("name of the generator is inconsistent with unram_name")

        # merge res_name into names
        if ext == "u":
            if len(names) == 1:
                if res_name is None:
                    res_name = names[0]+"0"
                names.append(res_name)
            if len(names) == 2:
                if res_name is None:
                    res_name = names[1]
                if names[1] != res_name:
                    raise ValueError("name of residue extension generator inconsistent")
            if len(names) > 2:
                raise ValueError("too many generators specified")
        else:
            if len(names) != 1:
                raise ValueError("wrong number of generators specified")

        names = tuple(names)

        if halt is None:
            halt = 40

        # set default for prec - if this is a ramified extension that is not
        # Eisenstein, then this number will be multiplied with the ramification
        # index by the implementing ring
        if prec is None:
            prec = base.precision_cap()
        prec = min(prec,base.precision_cap(),min([c.precision_absolute() for c in modulus.list()]))
        if ext == "u":
            modulus = modulus.map_coefficients(lambda c:c.add_bigoh(prec))
        elif ext == "e":
            from sage.rings.all import infinity
            modulus = modulus.parent()([c.add_bigoh(prec + (1 if i != modulus.degree() else 0)) for i,c in enumerate(modulus.list())])
        if ext == "e":
            prec *= modulus.degree()

        # set a default implementation
        if implementation is None:
            if ext == "u" and base.ground_ring_of_tower() is base:
                implementation = "FLINT"
            elif ext == "e" and base.ground_ring_of_tower() is base:
                implementation = "NTL"
            else:
                implementation = None

        return (ext, base, premodulus, modulus, names, prec, halt, print_mode, print_pos, print_sep, None, print_max_ram_terms, print_max_unram_terms, print_max_terse_terms, implementation), {"check":check}

    def get_object(self, version, key, extra_args):
        check = True
        if "check" in extra_args:
            check = extra_args["check"]
            extra_args.pop("check")
        assert len(extra_args)==0
        ret = AbstractFactory.get_object(self,version,key,extra_args)
        if check and hasattr(ret,"_check"):
            ret._check()
            assert ret.modulus()(ret.gen()).is_zero()
        return ret

    def _decode_key(self, key):
        r"""
        Split a ``key`` into the type, determining the implementation, and the
        parameters needed to construct an instance.

        INPUT:

        - ``key`` -- a tuple

        OUTPUT:

        A pair of strings determining the type of the implementation and a
        dictonary of parameters.

        EXAMPLES:

            sage: K = Qp(2)
            sage: R.<x> = K[]
            sage: from sage.rings.padics.factory import QpExtensionFactory
            sage: QpExtensionFactory._decode_key(('u', K, (1 + O(2^20))*x^2 + (1 + O(2^20))*x + (1 + O(2^20)), (1 + O(2^20))*x^2 + (1 + O(2^20))*x + (1 + O(2^20)), ('u', 'u0'), 20, 40, 'series', True, None, None, -1, -1, -1, None))
            (('u', 'capped-rel'),
             {'halt': 40,
              'implementation': None,
              'names': ('u', 'u0'),
              'poly': (1 + O(2^20))*x^2 + (1 + O(2^20))*x + 1 + O(2^20),
              'prec': 20,
              'prepoly': (1 + O(2^20))*x^2 + (1 + O(2^20))*x + 1 + O(2^20),
              'print_mode': {'alphabet': None,
               'max_ram_terms': -1,
               'max_terse_terms': -1,
               'max_unram_terms': -1,
               'mode': 'series',
               'pos': True,
               'sep': None}})

        """
        ext, base, premodulus, modulus, names, prec, halt, print_mode, print_pos, print_sep, print_alphabet, print_max_ram_terms, print_max_unram_terms, print_max_terse_terms, implementation = key

        precision_type = None
        if base.is_capped_relative():
            precision_type = "capped-rel"
        if base.is_capped_absolute():
            precision_type = "capped-abs"
        if base.is_fixed_mod():
            precision_type = "fixed-mod"
        assert precision_type

        print_mode = { "mode":print_mode, "pos":print_pos, "sep":print_sep, "alphabet":print_alphabet, "max_ram_terms":print_max_ram_terms, "max_unram_terms":print_max_unram_terms, "max_terse_terms":print_max_terse_terms }
        return (ext, precision_type), {"prepoly":premodulus, "poly":modulus, "names":names, "prec":prec, "halt":halt, "print_mode":print_mode, "implementation":implementation}

from padic_extension_leaves import EisensteinExtensionFieldCappedRelative, UnramifiedExtensionFieldCappedRelative, GeneralExtensionFieldCappedRelative, EisensteinExtensionRingCappedRelative, EisensteinExtensionRingCappedAbsolute, EisensteinExtensionRingFixedMod, UnramifiedExtensionRingCappedRelative, UnramifiedExtensionRingCappedAbsolute, UnramifiedExtensionRingFixedMod, GeneralExtensionRingCappedRelative, GeneralExtensionRingCappedAbsolute, GeneralExtensionRingFixedMod, TwoStepExtensionFieldCappedRelative, TwoStepExtensionRingCappedRelative, TwoStepExtensionRingCappedAbsolute, TwoStepExtensionRingFixedMod

QpExtensionFactory = GenericExtensionFactory("QpExtensionFactory", { ("e", "capped-rel") : EisensteinExtensionFieldCappedRelative,
                                                                     ("u", "capped-rel") : UnramifiedExtensionFieldCappedRelative,
                                                                     ("?", "capped-rel") : GeneralExtensionFieldCappedRelative,
                                                                   })
ZpExtensionFactory = GenericExtensionFactory("ZpExtensionFactory", { ("e", "capped-rel") : EisensteinExtensionRingCappedRelative,
                                                                     ("e", "capped-abs") : EisensteinExtensionRingCappedAbsolute,
                                                                     ("e", "fixed-mod") : EisensteinExtensionRingFixedMod,
                                                                     ("u", "capped-rel") : UnramifiedExtensionRingCappedRelative,
                                                                     ("u", "capped-abs") : UnramifiedExtensionRingCappedAbsolute,
                                                                     ("u", "fixed-mod") : UnramifiedExtensionRingFixedMod,
                                                                     ("?", "capped-rel") : GeneralExtensionRingCappedRelative,
                                                                     ("?", "capped-abs") : GeneralExtensionRingCappedAbsolute,
                                                                     ("?", "fixed-mod") : GeneralExtensionRingFixedMod,
                                                                   })

QpIteratedExtensionFactory = GenericExtensionFactory("QpIteratedExtensionFactory", { ("e", "capped-rel") : GeneralExtensionFieldCappedRelative,
                                                                                     ("u", "capped-rel") : GeneralExtensionFieldCappedRelative,
                                                                                     ("?", "capped-rel") : GeneralExtensionFieldCappedRelative,
                                                                                   })
ZpIteratedExtensionFactory = GenericExtensionFactory("ZpIteratedExtensionFactory", { ("e", "capped-rel") : GeneralExtensionRingCappedRelative,
                                                                                     ("e", "capped-abs") : GeneralExtensionRingCappedAbsolute,
                                                                                     ("e", "fixed-mod") : GeneralExtensionRingFixedMod,
                                                                                     ("u", "capped-rel") : GeneralExtensionRingCappedRelative,
                                                                                     ("u", "capped-abs") : GeneralExtensionRingCappedAbsolute,
                                                                                     ("u", "fixed-mod") : GeneralExtensionRingFixedMod,
                                                                                     ("?", "capped-rel") : GeneralExtensionRingCappedRelative,
                                                                                     ("?", "capped-abs") : GeneralExtensionRingCappedAbsolute,
                                                                                     ("?", "fixed-mod") : GeneralExtensionRingFixedMod,
                                                                                   })

QpTwoStepExtensionFactory = GenericExtensionFactory("QpTwoStepExtensionFactory", { ("e", "capped-rel") : TwoStepExtensionFieldCappedRelative,
                                                               })

ZpTwoStepExtensionFactory = GenericExtensionFactory("ZpTwoStepExtensionFactory", { ("e", "capped-rel") : TwoStepExtensionRingCappedRelative,
                                                                 ("e", "capped-abs") : TwoStepExtensionRingCappedAbsolute,
                                                                 ("e", "fixed-mod") : TwoStepExtensionRingFixedMod,
                                                               })

def ExtensionFactory(base, premodulus, prec = None, print_mode = None, halt = None, names = None, var_name = None, res_name = None, unram_name = None, ram_name = None, print_pos = None, print_sep = None, print_alphabet=None, print_max_ram_terms = None, print_max_unram_terms = None, print_max_terse_terms = None, check = True, implementation = None):
    """
    Create an extension of ``base``.

    INPUT:

    - ``base`` -- a `p`-adic ring

    - ``premodulus`` -- a modulus for the extension, see :ref:`padic_modulus`

    - ``prec`` -- an integer or ``None`` (default: ``None``), the precision cap
      of this ring. If ``None``, the precision cap will be set to the precision
      cap of ``base`` times the ramification index; or less if ``premodulus``
      is not given to sufficient precision.

    - ``print_mode`` -- a dictionary or one of ``'series'``, ``'val-unit'``,
      ``'terse'``, ``'digits'``, ``'bars'``, or ``None`` (default: ``None``),
      the way elements of this ring are printed, see :ref:`padic_printing`. If
      this is a dictionary, then the other printing parameters are read from
      it. If ``None``, then the print mode will be the same as in ``base``.

    - ``halt`` -- an integer or ``None`` (default: ``None``), currently
      irrelevant (to be used for lazy ring)

    - ``names`` -- a string or a tuple consisting of a single string, the name
      of the generator of this extension

    - ``res_name`` -- a string or ``None`` (default: ``None``), if this
      extension has an unramified part, the name of the generator of the
      residue field extension; per default, this is ``unram_name`` with a
      ``'0'`` appended.

    - ``unram_name`` -- a string or ``None`` (default: ``None``), if this
      extension has an unramified part, the name of the generator of that part;
      if this extension is unramified, this is the same as ``names``.

    - ``ram_name`` -- a string or ``None`` (default: ``None``), if this
      extension is ramified, the name of the generator of the totally ramified
      part; if ``premodulus`` is Eisenstein, this is the same as ``names``.

    - ``print_pos`` -- a boolean or ``None`` (default: ``None``), whether to
      only use positive integers in the representations of elements, see
      :ref:`padic_printing`. If ``None``, the value of ``base`` is used.

    - ``print_sep`` -- a string or ``None`` (default: ``None``), the separator
      character used when ``print_mode`` is ``'bars'``, see
      :ref:`padic_printing`. If ``None``, the value of ``base`` is used.

    - ``print_max_ram_terms`` -- an integer or ``None`` (default: ``None``),
      the maximum number of powers of the uniformizer to print, see
      :ref:`padic_printing`. If ``None``, the value of ``base`` is used.

    - ``print_max_unram_terms`` -- an integer or ``None`` (default: ``None``),
      the maximum number of entries shown in a coefficient of the uniformizer,
      see :ref:`padic_printing`. If ``None``, the value of ``base`` is used.

    - ``print_max_terse_terms`` -- an integer or ``None`` (default: ``None``),
      the maximum number of terms to print in a polynomial representation of an
      element, see :ref:`padic_printing`. If ``None``, the value of ``base`` is
      used.

    - ``check`` --  a boolean (default: ``True``), whether to perform expensive
      checks on the input parameters

    EXAMPLES::

        TODO
    """
    args = base, premodulus, prec, print_mode, halt, names, var_name, res_name, unram_name, ram_name, print_pos, print_sep, print_max_ram_terms, print_max_unram_terms, print_max_terse_terms, print_alphabet, check, implementation
    if base is base.ground_ring_of_tower():
        if base.is_field():
            return QpExtensionFactory(*args)
        else:
            return ZpExtensionFactory(*args)
    else:
        if base.is_field():
            return QpIteratedExtensionFactory(*args)
        else:
            return ZpIteratedExtensionFactory(*args)

pAdicExtension = ExtensionFactory

def TwoStepExtensionFactory(base, premodulus, prec = None, print_mode = None, halt = None, names = None, res_name = None, unram_name = None, ram_name = None, print_pos = None, print_sep = None, print_max_ram_terms = None, print_max_unram_terms = None, print_max_terse_terms = None, print_alphabet = None, check = True):
    """
    Create an extension that is an Eisenstein extension of an unramified
    extension of a `p`-adic base ring.

    This is a helper function for :class:`GeneralExtensionGeneric` and its
    subclasses.

    The input parameters are the same as for :meth:`ExtensionFactory`, except
    for ``base`` which must be a simple unramified extension of a `p`-adic base
    ring.

    EXAMPLES::

        TODO
    """
    args = base, premodulus, prec, print_mode, halt, names, names, res_name, unram_name, ram_name, print_pos, print_sep, print_max_ram_terms, print_max_unram_terms, print_max_terse_terms, print_alphabet, check
    if base.maximal_unramified_subextension() is not base or base.base() is not base.ground_ring_of_tower():
        raise ValueError("base must be a simple unramified extension")

    if base.is_field():
        return QpTwoStepExtensionFactory(*args)
    else:
        return ZpTwoStepExtensionFactory(*args)
