def epp(G, vx):
    if not G.parent().base() is vx.domain():
        raise ValueError

    R = G.parent()
    K = R.base().constant_base_field()
    Kx = R.base()
    t = G.parent().gen()
    p = vx.residue_field().characteristic()
    v0 = GaussValuation(R,vx)

    W = vx.mac_lane_approximants(G)
    E = lcm([w.value_group().denominator().gen(0) for w in W])
    if not p.divides(E):
        return K.totally_ramified_extension(E)

    f0 = -G[0]

    if vx(f0) != 0:
        raise ValueError

    if not vx.reduce(f0).is_nth_power(p):
        raise ValueError("no ramification here")

    h = vx.lift(vx.reduce(f0).nth_root(p))
    v1 = v0.extension(t-h, infinity)

    def nred(g=None):
        if g is None: g = g0()
        if g.parent() is R:
            assert g.degree() <= 0
            g = g[0]
        return vx.reduce(vx.shift(g,-vx(g)))

    def is_a(g=None):
        if g is None: g = g0()
        return vx(g)/vx(p) >= p/(p-1)

    def is_b(g=None):
        if g is None: g = g0()
        return not nred(g).is_nth_power(p)

    def is_633(g=None):
        if g is None: g = g0()
        return is_a(g) or is_b(g) or (vx(g)/p not in ZZ)

    def g0():
        return v1.coefficients(G).next()[0]

    def h():
        return -v1.phi()[0]

    # LEMMA 6.33
    while not is_633():
        alpha = vx.lift(nred().nth_root(p))
        s = vx(g0())
        assert p.divides(s)
        v1 = v1._base_valuation.extension(v1.phi()+vx.shift(alpha,s//p),infinity)
    if is_a():
        raise ValueError("any totally ramified extension works")
    if is_b():
        return K.totally_ramified_extension(p)
    assert vx(g0())/p not in ZZ

    if nred().is_constant():
        vx_,v0_,v1_,G_ = vx,v0,v1,G

        vK = vx._base_valuation.constant_valuation()
        S.<Phi> = K[]
        F = Phi^p + vK.shift(vK.lift(nred().element().numerator()[0]), vx(g0()))

        vx1 = vx._base_valuation
        if vx1.phi().degree()!=1:
            raise NotImplementedError

        while True:
            print F
            L.<phi> = K.extension(F)
            Lx_ = PolynomialRing(L,names=Kx.variable_names())
            wx0 = GaussValuation(Lx_)
            wx1 = wx0.extension(vx1.phi().change_ring(L), vx1._mu*p)
            Lx = FunctionField(L,names=Kx.variable_names())
            wx = RationalFunctionFieldValuation(Lx,wx1)

            if not h().denominator().is_one():
                raise NotImplementedError
            delta = Lx.zero()
            hh = Lx(h().numerator().map_coefficients(L,L)) + phi + delta

            wR = R.change_ring(Lx)
            w0 = GaussValuation(wR, wx)
            w1 = w0.extension(wR.gen() - hh, infinity)
            wG = G.change_ring(Lx)

            ppprint(list(w1.coefficients(wG)))

            vx,v0,v1,G = wx,w0,w1,wG
            try:
                vg0 = ZZ(vx(g0()))
                bi = nred()
                print bi,vg0
                if is_a():
                    return L
                if is_b():
                    return L
                i = vg0%p
                if i == 0:
                    raise NotImplementedError
                else:
                    if not bi.is_constant():
                        break
                    else:
                        bi = g0()/(phi**i)
                        r = wx(bi)/p
                        assert r in ZZ
                        r = ZZ(r)
                        beta0 = wx.reduce(bi/K.uniformizer()**r)
                        assert beta0.is_constant()
                        beta0 = beta0.numerator()[0]
                        beta0 = vK.lift(beta0)
                        F += vK.shift(beta0,r)*F.parent().gen()**i
            finally:
                vx,v0,v1,G = vx_,v0_,v1_,G_

    raise NotImplementedError

def stars(vx,L,p):
    g = L.random_element().minpoly()
    M = L.degree()
    if g.degree()<M:
        print "weird."
        return
    while vx(g[0])<0: g = g(t/vx.uniformizer())*(vx.uniformizer()^M)
    vf = [vx(c) for c in list(g)]
    print vf
    if vf[0]/M in ZZ:
        print "leo failed."
    if min(vf[1:-1]) < min([v for i,v in enumerate(vf) if not p.divides(i)]):
        print "cancer failed."
    for j in range(1,M):
        vff = [vx(binomial(i,j))+vf[i] for i in range(j,M+1)]
        mins = [v for v in vff if v==min(vff)]
        if len(mins)!=1:
            print "gemini failed for j=%s"%j
            print vff
            break
    return g

