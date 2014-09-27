from sage.rings.padics.padic_valuation import pAdicValuation
from sage.rings.padics.gauss_valuation import GaussValuation
from sage.rings.padics.function_field_valuation import RationalFunctionFieldValuation

def hard_example():
    p = 2
    K = QQ
    vK = pAdicValuation(K, p)
    R.<x> = K[]
    vKx = GaussValuation(R, vK)
    Kx.<x> = FunctionField(K)
    vLxx = RationalFunctionFieldValuation(Kx, vKx)
    R.<t> = Kx[]
    x = R(x)
    v = GaussValuation(R, vLxx)
    w = v.extension(t^3+x,1)
    ww = w.extension(w.lift_to_key(w.residue_ring().gen()^2 + w.residue_field().base().gen()), 3)
    G = ww.lift(ww.residue_ring().gen()^2+ww.residue_field().base().gen()^2)
    return ww,G

def epp(G, K, L, uniformizer):
    vL = pAdicValuation(L, L(uniformizer).factor()[0][0])
    p = vL.residue_field().characteristic()
    vLx = GaussValuation(R, vL)
    Lx.<x> = FunctionField(L)
    vLxx = RationalFunctionFieldValuation(Lx, vLx)
    R.<t> = Lx[]
    x = R(x)
    D = G(t,x).degree()

    W = vLxx.mac_lane_approximants(G(t,x)) # TODO: this is too expensive, don't do the full mac lane algorithm; break when we see ramification (or factorization?)
    for w in W:
        if w.E() == 1:
            continue

        while w._base_valuation.E() != 1:
            w = w._base_valuation

        E = w.E()
        print "One extension of %s is not weakly unramified. The critical step in MacLane's algorithm produces %s which is ramified with ramification index %s"%(vLxx,w,E)
        if len(E.factor()) or E.factor()[0][0]!=p:
            raise NotImplementedError("Abhyankar")

        # If we just took an Eth root of the uniformizer, then the MacLane
        # algorithm would give a weakly unramified w in this step. In the next
        # step, we take the w.phi()-adic expansion of G (drop some trailing
        # terms) multiply it with an equivalence-reciprocal R and factor in
        # reduction.
        # Let us assume that the reduction of R*G has degree d.
        # We want to make sure that the reduction does not factor as linear^d.
        # I hope (not proven yet) that this can be achieved by modifying the
        # constant term until it not a d-th power anymore or until any other
        # coefficient appears in reduction.
        # To do this, I increase the valuation of the constant term by
        # modifying the constant term of the constant term of the constant term
        # of [...] the key polynomial. This process will terminate because
        # otherwise the constant term of R*G would get arbitrarily large
        # valuation (and with it the corresponding key polynomial). At the same
        # time, the field extension does not change anymore (Krasner's Lemma).
        # Putting this together, there is a sequence of key polynomials of
        # constant degree (< "effective" degree of R*G) which converge against
        # a factor of G. But such behaviour would be detected by MacLane's
        # algorithm, i.e., R*G would factor non-trivially in reduction.
        d = w.phi().degree()

        w = w._base_valuation
        #print "We win if %s 
        valuations = [ val - w(w.phi())*i for i,val in enumerate(w.valuations(G(t,x)))]
        d = len(valuations)
        constant = next(w.coefficients(G(t,x)))


    if len(W)>1:
        print "%s factors over the completion as %s"%(G(t,x),W)
        raise NotImplementedError
    else:
        print "%s remains irreducible over the completion"%G(t,x)

        w = W[0]
        if w.E() == 1:
            print "%s is weakly unramified."
            return
        if not vL.residue_field().characteristic().divides(w.E()):
            print "%s is only tamely ramified."
            return

        v = GaussValuation(R, vLxx)
        shift = R.zero()
        for s in shift:
            shift += s
        v = GaussValuation(R, vLxx).extension(t+shift, 0, check=False)

        constant = list(v.coefficients(G(t,x)))[0]
        if constant.degree() >= 1:
            raise NotImplementedError

        if not constant.denominator().is_one():
            raise NotImplementedError

        constant = constant.numerator()
        critical_degrees = [i for i,vi in enumerate(list(vLx.valuations(constant))) if vi == vLx(constant)]
        assert critical_degrees
        print "The valuation of the constant term is caused in degrees %s"%critical_degrees

        if not all([G.degree().divides(critical_degrees)]):
            print "Taking any extension of degree %s will work."%w.E()
            return

        critical_degree = critical_degrees[0]
        print "Improving valuation in degree %s"%critical_degree

        xpower = critical_degree//G(t,x).degree()

        if len(polys) < xpower+1:
            print "This is the first time we work on degree %s. Let me change the setup and restart."%critical_degree
            while len(polys) < xpower+1:
                R.<a> = K[]
                polys.append(a^G(t,x).degree())
                shifts.append(K.zero())
            return epp(G, K, uniformizer, polys, shifts)

            xpower = i//arg_min if arg_min else 0
            if L.degree() != 1 and shift.numerator()[xpower].is_zero():
                return L, shift+L.gen()^vd*Lx.gen()^xpower
            else:
                poly += c.numerator()[arg_min].polynomial(L.variable_name())
                minpoly = poly.factor()[0][0]
                relative_degree = minpoly.degree()/L.degree()
                L = L.base().extension(minpoly,names=L.variable_names())
                Lx.<x> = FunctionField(L)
                assert shift.denominator().is_one()
                shift = shift.numerator().map_coefficients(lambda c: c.polynomial('a')(L.gen()), L)(x)
            return L, shift+L.gen()*Lx.gen()^xpower

def best_linear_approximation(G, L, uniformizer):
    global t,x
    vL = pAdicValuation(L, uniformizer)
    R.<x> = L[]
    vLx = GaussValuation(R, vL)

    L.<x> = FunctionField(L)
    vLx = RationalFunctionFieldValuation(L, vLx)

    R.<t> = L[]
    x = R(x)

    v = GaussValuation(R, vLx)
    while True:
        w = v.mac_lane_step(G(t,x))
        if len(w)>1:
            raise NotImplementedError
        if w[0].phi().degree()>1:
            return v
        v = w[0]

#def best_linear_approximation(G, L, uniformizer, const=0):
#    global t,x
#    vL = pAdicValuation(L, uniformizer)
#    R.<x> = L[]
#    vLx = GaussValuation(R, vL)
#
#    L.<x> = FunctionField(L)
#    vLx = RationalFunctionFieldValuation(L, vLx)
#
#    R.<t> = L[]
#    x = R(x)
#
#    v = GaussValuation(R, vLx)
#
#    G = G(t-const,x)
#    d = G.degree()
#    def additive_error(frm,to=0):
#        assert frm > 0 and frm <= G.degree()
#        assert to >= 0 and to < frm
#        return list(v.valuations(G))[frm] + vL(binomial(frm,to))
#
#    def multiplicative_error(frm,to=0):
#        assert frm > 0 and frm <= G.degree()
#        assert to >= 0 and to < frm
#        return frm-to
#
#    v0 = vLx(G[0])
#    print "Constant term %s has valuation %s"%(G[0],v0)
#
#    print "Are we in the strange (impossible?) case that a low valuation disturbation can fix a high valuation error?"
#    for i in range(1,d):
#        if d*additive_error(i) < (d-i)*v0:
#            print "Yes! Degree %s has an additive error of %s."%(i,additive_error(i))
#            raise NotImplementedError()
#    else:
#        print "No."
#
#    print "In which degrees can we fix the constant error?"
#    for i in range(1,d+1):
#        va = (v0-additive_error(i))/multiplicative_error(i)
#        if va <= 0:
#            continue
#        if d*va < v0:
#            print "We could fix it in degree %s, but this would introduce an error of %s from degree %s"%(i,d*va,d)
#            continue
#        print "in degree %s"%i
#        if i != d:
#            raise NotImplementedError
#
#    shift_val = v0/d
#    print "Trying to shift the key polynomial by an error of valuation %s"%(shift_val)
#
#    print "Can the error be fixed by an extension of the base field?"
#    if not G[0].denominator().is_one():
#        raise NotImplementedError
#    n = G[0].numerator()
#    shift_pow = n.parent().zero()
#    for j,c in enumerate(n.coeffs()):
#        if vL(c) == v0:
#            if not shift_val.denominator().divides(j):
#                raise NotImplementedError("are we done?")
#            shift_pow += c*n.parent().gen()**j
#    print "Yes. We have to take an (approximate) %s-th root of %s"%(d,shift_pow)
#
#    for i in range(d):
#        err_val = additive_error(d,i) + shift_val*multiplicative_error(d,i)
#        if err_val <= list(v.valuations(G))[i]:
#            print "This changes the valuation in degree %s: %s -> %s"%(i,list(v.valuations(G))[i],err_val)

def generate_example(p=2, d=[1,2], lam=[1/2,1]):
    R.<x> = QQ[]
    vK = pAdicValuation(QQ, p)
    vKx = GaussValuation(R, vK)

    K.<x> = FunctionField(QQ)
    vKx = RationalFunctionFieldValuation(K, vKx)

    R.<t> = K[]
    v0 = GaussValuation(R, vKx)
    v1 = v0.extension(t + p*x, lam[0])

    def random_key(v, d):
        while True:
            R.<t,x> = v.residue_field().constant_base_field()[]
            f = R.random_element(degree=p*d)
            D = { (a,b):c for (a,b),c in f.dict().items() if a < d and b < 3 }
            D[(d,0)]=1
            f = R(D)
            f = f(v.residue_ring().gen(), v.residue_ring()(v._base_valuation.residue_field().gen()))
            if f in v.residue_field():
                continue
            if f.leading_coefficient() != 1:
                continue
            if not f.is_irreducible():
                continue
            if f.degree() != d:
                continue
            f = v.lift_to_key(f)
            if f.degree() == v.phi().degree():
                continue
            break

        return f

    f1 = random_key(v1, d[0])
    v2 = v1.extension(f1, v1(f1)+lam[1])
    f2 = random_key(v2, d[1])

    R.<t,x> = ZZ[]
    G = eval(str(f2).replace('^','**'))
    return G

def maclane(G, L, uniformizer):
    vL = pAdicValuation(L, uniformizer)
    R.<x> = L[]
    vLx = GaussValuation(R, vL)

    L.<x> = FunctionField(L)
    vLx = RationalFunctionFieldValuation(L, vLx)

    R.<t> = L[]
    x = R(x)
    w = vLx.mac_lane_approximants(G(t,x))
    if len(w)>1:
        print "Polynomial is not irreducible."
        return w
    w = w[0]
    print "Ramification index = %s"%w.E()
    return w

# e.g.
# G = load("hard_ramified_polynomial")
# R.<a> = QQ[]
# L.<a> = QQ.extension(a^3-3)
# epp(G, L, a)

# a confusing case
"""
sage: R.<t,x> = QQ[]
sage: G = t^12 + 4*t^9*x + 6*t^6*x^2 + 8*t^6*x + 4*t^3*x^3 + 16*t^3*x^2 + x^4 + 8*x^3 + 64*t^2 + 16*x^2
sage:
sage: maclane(G, QQ, 2)
[ Gauss valuation induced by Valuation on rational function field induced by Gauss valuation induced by 2-adic valuation, v(t^3 + x) = 1, v(t^6 + 2*x*t^3 + 8*t + x^2 + 4*x) = 7/2 ]
sage:
sage: R.<a> = QQ[]
sage: L.<a> = QQ.extension(a^2-2)
sage: w = maclane(G, L, L.factor(2)[0][0]); w
[ Gauss valuation induced by Valuation on rational function field induced by Gauss valuation induced by Fractional ideal (a)-adic valuation, v(t^3 + x) = 2, v(t^6 + 2*x*t^3 + (8*a + 8)*t + x^2 + 4*x) = 15/2 ]
sage: t, x = w.domain().gen(), w.domain().base_ring().rational_function_field().gen()
sage:
sage: v = w._base_valuation
sage: w = v.extension(t^6 + 2*x*t^3 + 8*t + x^2 + 4*x, 7)
sage: w.reduce(w.equivalence_unit(-w(G(t,x)))*G(t,x)).factor()
(t + u1)^2
sage: w.coefficients(G(t,x)).next()
128*t^2
sage:
sage:
sage: R.<b> = QQ[]
sage: L.<b> = QQ.extension(b^2-2*b-2)
sage: w = maclane(G, L, L.factor(2)[0][0]); w
[ Gauss valuation induced by Valuation on rational function field induced by Gauss valuation induced by Fractional ideal (b)-adic valuation, v(t^3 + x) = 2, v(t^6 + 2*x*t^3 + (120*b + 88)*t + x^2 + (464*b + 340)*x) = 8, v(t^12 + 4*x*t^9 + (6*x^2 + 8*x)*t^6 + (4*x^3 + 16*x^2)*t^3 + 64*t^2 + x^4 + 8*x^3 + 16*x^2) = +Infinity ]
sage:
sage: w = w._base_valuation
sage: t, x = w.domain().gen(), w.domain().base_ring().rational_function_field().gen()
sage: w.is_key(G(t,x))
True
sage: w.reduce(w.equivalence_unit(-w(G(t,x)))*G(t,x)).factor()
t^2 + u1*t + u1^2 + x*u1 + x^2
sage: w.coefficients(G(t,x)).next()
(49920*b + 36608)*t^2 + ((385024*b + 281856)*x)*t + (742400*b + 543488)*x^2
sage:
sage: v = w._base_valuation
sage: w = v.extension(t^6 + 2*x*t^3 + 8*t + x^2 + (464*b + 340)*x, 8)
sage: w.is_key(G(t,x))
False
sage: w.reduce(w.equivalence_unit(-w(G(t,x)))*G(t,x)).factor()
u1^2
sage: w.coefficients(G(t,x)).next()
128*t^2 + ((7424*b + 5376)*x)*t + (742400*b + 543488)*x^2

### [ Gauss valuation induced by Valuation on rational function field induced by Gauss valuation induced by Fractional ideal (a)-adic valuation, v(t^3 + x) = 2, v(t^6 + 2*x*t^3 + 8*t + x^2 + 4*x) = 7 ]
### but this expands to
### [ Gauss valuation induced by Valuation on rational function field induced by Gauss valuation induced by Fractional ideal (a)-adic valuation, v(t^3 + x) = 2, v(t^6 + 2*x*t^3 + (8*a + 8)*t + x^2 + 4*x) = 15/2 ]
### over Q(x^2-2*x-2)
### [ Gauss valuation induced by Valuation on rational function field induced by Gauss valuation induced by Fractional ideal (b)-adic valuation, v(t^3 + x) = 2, v(t^6 + 2*x*t^3 + (120*b + 88)*t + x^2 + (136*b + 100)*x) = 7 ]
### which expands to
### [ Gauss valuation induced by Valuation on rational function field induced by Gauss valuation induced by Fractional ideal (b)-adic valuation, v(t^3 + x) = 2, v(t^6 + 2*x*t^3 + (120*b + 88)*t + x^2 + (464*b + 340)*x) = 8 ]
### which expands to
### [ Gauss valuation induced by Valuation on rational function field induced by Gauss valuation induced by Fractional ideal (b)-adic valuation, v(t^3 + x) = 2, v(t^6 + 2*x*t^3 + (120*b + 88)*t + x^2 + (464*b + 340)*x) = 8, v(t^12 + 4*x*t^9 + (6*x^2 + 8*x)*t^6 + (4*x^3 + 16*x^2)*t^3 + 64*t^2 + x^4 + 8*x^3 + 16*x^2) = +Infinity ]
### is it enough to fix the constant?
### If we let w:= [ Gauss valuation induced by Valuation on rational function field induced by Gauss valuation induced by Fractional ideal (b)-adic valuation, v(t^3 + x) = 2, v(t^6 + 2*x*t^3 + 8*t + x^2 + (136*b + 100)*x) = 7 ]
### then actually w8.equivalence_decomposition(G(t,x)) = t^12 + 4*x*t^9 + (6*x^2 + 8*x)*t^6 + (4*x^3 + 16*x^2)*t^3 + 64*t^2 + x^4 + 8*x^3 + 16*x^2

###
### If we let w':= [ Gauss valuation induced by Valuation on rational function field induced by Gauss valuation induced by Fractional ideal (b)-adic valuation, v(t^3 + x) = 2, v(t^6 + 2*x*t^3 + 8*t + x^2 + 4*x) = 7 ]
### then the constant of t^12 + 4*x*t^9 + (6*x^2 + 8*x)*t^6 + (4*x^3 + 16*x^2)*t^3 + 64*t^2 + x^4 + 8*x^3 + 16*x^2 is 128*t^2
### but for w the constant is
### 128*t^2 + ((7424*b + 5376)*x)*t + (742400*b + 543488)*x^2
### so this is a worse approximation
"""
