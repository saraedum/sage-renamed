## -*- encoding: utf-8 -*-
"""
This file (./integration_doctest.sage) was *autogenerated* from ./integration.tex,
with sagetex.sty version 2011/05/27 v2.3.1.
It contains the contents of all the sageexample environments from this file.
You should be able to doctest this file with:
sage -t ./integration_doctest.sage
It is always safe to delete this file; it is not used in typesetting your
document.

Sage example in ./integration.tex, line 44::

    sage: x = var('x'); f(x) = exp(-x^2) * log(x)
    sage: N(integrate(f, x, 1, 3))
    0.035860294991267694
    sage: plot(f, 1, 3, fill='axis')
    Graphics object consisting of 2 graphics primitives

Sage example in ./integration.tex, line 103::

    sage: fp = plot(f, 1, 3, color='red')
    sage: n = 4
    sage: interp_points = [(1+2*u/(n-1), N(f(1+2*u/(n-1))))
    ....:                  for u in range(n)]
    sage: A = PolynomialRing(RR, 'x')
    sage: pp = plot(A.lagrange_polynomial(interp_points), 1, 3, fill='axis')
    sage: show(fp+pp)

Sage example in ./integration.tex, line 346::

    sage: N(integrate(exp(-x^2)*log(x), x, 17, 42)) # rel tol 7e-15
    2.5657285006962035e-127

Sage example in ./integration.tex, line 355::

    sage: integrate(log(1+x)*x, x, 0, 1)
    1/4
    sage: N(integrate(log(1+x)*x, x, 0, 1))
    0.250000000000000

Sage example in ./integration.tex, line 372::

    sage: numerical_integral(exp(-x^2)*log(x), 17, 42) # rel tol 7e-12
    (2.5657285006962035e-127, 3.3540254049238093e-128)

Sage example in ./integration.tex, line 394::

    sage: numerical_integral(exp(-x^100), 0, 1.1)
    (0.99432585119150..., 4.0775730...e-09)
    sage: numerical_integral(exp(-x^100), 0, 1.1, algorithm='qng')
    (0.994327538576531..., 0.016840666914...)

Sage example in ./integration.tex, line 404::

    sage: integrate(exp(-x^2)*log(x), x, 17, 42)
    integrate(e^(-x^2)*log(x), x, 17, 42)

Sage example in ./integration.tex, line 412::

    sage: N(integrate(exp(-x^2)*log(x), x, 17, 42), 200) # rel tol 7e-15
    2.5657285006962035e-127

Sage example in ./integration.tex, line 417::

    sage: N(integrate(sin(x)*exp(cos(x)), x, 0, pi), 200)
    2.3504023872876029137647637011912016303114359626681917404591

Sage example in ./integration.tex, line 430::

    sage: sage.calculus.calculus.nintegral(sin(sin(x)), x, 0, 1)
    (0.430606103120690..., 4.78068810228705...e-15, 21, 0)

Sage example in ./integration.tex, line 436::

    sage: g(x) = sin(sin(x))
    sage: g.nintegral(x, 0, 1)
    (0.430606103120690..., 4.78068810228705...e-15, 21, 0)

Sage example in ./integration.tex, line 465::

    sage: gp('intnum(x=17, 42, exp(-x^2)*log(x))') # rel tol 1e-17
    2.5657285005610514829176211363206621657 E-127

Sage example in ./integration.tex, line 474::

    sage: gp('intnum(x=0, 1, sin(sin(x)))')
    0.430606103120690604912377355...
    sage: old_prec = gp.set_precision(50)
    sage: gp('intnum(x=0, 1, sin(sin(x)))')
    0.43060610312069060491237735524846578643360804182200

Sage example in ./integration.tex, line 490::

    sage: p = gp.set_precision(old_prec) # on remet la pr??cision par d??faut
    sage: gp('intnum(x=0, 1, x^(-1/2))')
    1.99999999999999999999...

Sage example in ./integration.tex, line 496::

    sage: gp('intnum(x=[0, -1/2], 1, x^(-1/2))')
    2.000000000000000000000000000...

Sage example in ./integration.tex, line 504::

    sage: gp('intnum(x=[0, -1/42], 1, x^(-1/2))')
    1.99999999999999999999...

Sage example in ./integration.tex, line 518::

    sage: import mpmath
    sage: mpmath.mp.prec = 53
    sage: mpmath.quad(lambda x: mpmath.sin(mpmath.sin(x)), [0, 1])
    mpf('0.43060610312069059')

Sage example in ./integration.tex, line 526::

    sage: mpmath.mp.prec = 113
    sage: mpmath.quad(lambda x: mpmath.sin(mpmath.sin(x)), [0, 1])
    mpf('0.430606103120690604912377355248465809')
    sage: mpmath.mp.prec = 114
    sage: mpmath.quad(lambda x: mpmath.sin(mpmath.sin(x)), [0, 1])
    mpf('0.430606103120690604912377355248465785')

Sage example in ./integration.tex, line 550::

    sage: mpmath.quad(sin(sin(x)), [0, 1])
    Traceback (most recent call last):
    ...
    TypeError: no canonical coercion from
    <type 'sage.libs.mpmath.ext_main.mpf'> to Symbolic Ring

Sage example in ./integration.tex, line 565::

    sage: g(x) = max_symbolic(sin(x), cos(x))
    sage: mpmath.mp.prec = 100
    sage: mpmath.quadts(lambda x: g(N(x, 100)), [0, 1])
    mpf('0.873912416263035435957979086252')

Sage example in ./integration.tex, line 574::

    sage: mpmath.mp.prec = 170
    sage: mpmath.quadts(lambda x: g(N(x, 190)), [0, 1])
    mpf('0.87391090757400975205393005981962476344054148354188794')
    sage: N(sqrt(2) - cos(1), 100)
    0.87391125650495533140075211677

Sage example in ./integration.tex, line 585::

    sage: mpmath.quadts(lambda x: g(N(x, 170)), [0, mpmath.pi / 4, 1])
    mpf('0.87391125650495533140075211676672147483736145475902551')

Sage example in ./integration.tex, line 750::

    sage: T = ode_solver()

Sage example in ./integration.tex, line 761::

    sage: def f_1(t,y,params): return [y[1],params[0]*(1-y[0]^2)*y[1]-y[0]]
    sage: T.function = f_1

Sage example in ./integration.tex, line 776::

    sage: def j_1(t,y,params):
    ....:     return [[0, 1],
    ....:             [-2*params[0]*y[0]*y[1]-1, params[0]*(1-y[0]^2)],
    ....:             [0,0]]
    sage: T.jacobian = j_1

Sage example in ./integration.tex, line 786::

    sage: T.algorithm = "rk8pd"
    sage: T.ode_solve(y_0=[1,0], t_span=[0,100], params=[10],
    ....:             num_points=1000)
    sage: f = T.interpolate_solution()

Sage example in ./integration.tex, line 801::

    sage: plot(f, 0, 100)
    Graphics object consisting of 1 graphics primitive

Sage example in ./integration.tex, line 838::

    sage: t, y = var('t, y')
    sage: desolve_rk4(t*y*(2-y), y, ics=[0,1], end_points=[0, 1], step=0.5)
    [[0, 1], [0.5, 1.12419127424558], [1.0, 1.461590162288825]]

Sage example in ./integration.tex, line 861::

    sage: import mpmath
    sage: mpmath.mp.prec = 53
    sage: sol = mpmath.odefun(lambda t, y: y, 0, 1)
    sage: sol(1)
    mpf('2.7182818284590451')
    sage: mpmath.mp.prec = 100
    sage: sol(1)
    mpf('2.7182818284590452353602874802307')
    sage: N(exp(1), 100)
    2.7182818284590452353602874714

Sage example in ./integration.tex, line 889::

    sage: mpmath.mp.prec = 53
    sage: f = mpmath.odefun(lambda t, y: [-y[1], y[0]], 0, [1, 0])
    sage: f(3)
    [mpf('-0.98999249660044542'), mpf('0.14112000805986721')]
    sage: (cos(3.), sin(3.))
    (-0.989992496600445, 0.141120008059867)

Sage example in ./integration.tex, line 939::

    sage: mpmath.mp.prec = 10
    sage: sol = mpmath.odefun(lambda t, y: y, 0, 1)
    sage: sol(1)
    mpf('2.7148')
    sage: mpmath.mp.prec = 100
    sage: sol(1)
    mpf('2.7135204235459511323824699502438')

"""
# This file was *autogenerated* from the file integration_doctest.sage.
