from sage.rings.padics.padic_valuation import pAdicValuation
from sage.rings.padics.gauss_valuation import GaussValuation
from sage.rings.padics.function_field_valuation import RationalFunctionFieldValuation

def epp(G, L, uniformizer, shift=None):
    vL = pAdicValuation(L, uniformizer)
    R.<x> = L[]
    vLx = GaussValuation(R, vL)

    Lx.<x> = FunctionField(L)
    if shift is None:
        shift = Lx.zero()
    vLxx = RationalFunctionFieldValuation(Lx, vLx)

    R.<t> = Lx[]
    x = R(x)

    v = GaussValuation(R, vLxx)
    # v = best_linear_approximation(G, vL.domain(), uniformizer)
    # phi = v.phi()
    v = GaussValuation(R, vLxx).extension(t+shift, 0, check=False)
    G = G(t,x)
    d = G.degree()

    poly = L.polynomial()
    poly = poly^(d//poly.degree())

    coeffs = list(v.coefficients(G))
    c = coeffs[0]
    print "Will improve the constant term %s"%c
    if c.degree() >= 1:
        raise NotImplementedError
    c = c[0]

    if not c.denominator().is_one():
        raise NotImplementedError

    def additive_error(frm,to=0):
        assert frm > 0 and frm <= G.degree()
        assert to >= 0 and to < frm
        return list(v.valuations(G))[frm] + vL(binomial(frm,to))

    def multiplicative_error(frm,to=0):
        assert frm > 0 and frm <= G.degree()
        assert to >= 0 and to < frm
        return frm-to

    print "The constant term %s has valuation %s"%(c,vLxx(c))
    assert c.denominator().is_one()
    vals = list(vLx.valuations(c.numerator()))
    arg_min = [i for i,vi in enumerate(vals) if vi == min(vals)]
    assert arg_min
    print "The error is caused in %s-degrees %s"%(x,arg_min)

    if any([not d.divides(am) for am in arg_min]):
        print "Done."
        return
    arg_min = arg_min[0]
    print "Let's focus on the first one, i.e., %s"%arg_min

    for i in srange(1,d+1):
        if not i.divides(arg_min):
            print "We can not produce %s^%s in degree %s."%(x,arg_min,i)
            continue
        vd = (vals[arg_min]-additive_error(i))/multiplicative_error(i)
        print "We can produce %s^%s in degree %s and fix the error if we had an element of valuation %s."%(x,arg_min,i,vd)
        if vd < 0:
            print "[not an option]"
            continue
        for j in srange(1,d+1):
            if i==j: continue
            j_error = additive_error(j)+multiplicative_error(j)*vd
            if j_error < min(vals):
                print "...but this would give a worse error of %s from degree %s"%(j_error,j)
                break
        else:
            if i != d:
                raise NotImplementedError
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
