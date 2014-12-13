def solve_algebraic(equations):
    constants = {}
    while any([e.degree() == 1 for e in equations]):
        for e in equations:
            if e.degree()==1:
                v = e.variables()[-1]
                f = -e/e[v] + v
                constants[v]= f
                for i in range(len(equations)):
                    equations[i] = equations[i].subs({v:f})
    equations = [e for e in equations if e]
    print equations
    solve_algebraic_recursive(equations)

def solve_algebraic_recursive(equations):
    """
    sage: R.<x,y,z> = PolynomialRing(QQ,order='lp') 
    sage: solve_algebraic([x^2+y^2+1,x-y,z-1])
    [Ring morphism:
      From: Multivariate Polynomial Ring in x, y, z over Algebraic Field
      To:   Algebraic Field
      Defn: x |--> -0.7071067811865475?*I
            y |--> -0.7071067811865475?*I
            z |--> 1, Ring morphism:
      From: Multivariate Polynomial Ring in x, y, z over Algebraic Field
      To:   Algebraic Field
      Defn: x |--> 0.7071067811865475?*I
            y |--> 0.7071067811865475?*I
            z |--> 1]
    """
    I = equations[0].parent().ideal(equations)
    G = I.groebner_basis()
    G = reversed(G)
    G = [g.change_ring(QQbar) for g in G]
    return solve_algebraic_groebner(G)

def make_univariate(g):
    R = PolynomialRing(QQbar, names=g.variables())
    h = g.parent().hom([R(v) if v in g.variables() else R(0) for v in g.parent().gens()])
    return h(g)

def lift_with_identity(s,domain):
    codomain = PolynomialRing(QQbar, names=tuple([v for v in domain.variable_names() if v not in s.domain().variable_names()]))
    if codomain.ngens()==0:
        codomain = QQbar
    s = s.extend_codomain(codomain)
    return domain.hom([s(s.domain()(v)) if v in s.domain().variable_names() else codomain(v) for v in domain.variable_names()])

def solve_algebraic_univariate(g):
    return [g.parent().hom([r]) for r in g.roots(multiplicities=False)]

def merge(s,ss):
    return s.domain().hom([QQbar(ss(ss.domain()(v))) if v in ss.domain().variable_names() else QQbar(s(s.domain()(v))) for v in s.domain().variable_names()])

def solve_algebraic_groebner(G):
    if len(G)==0:
        return [Hom(QQbar,QQbar).identity()]
    else:
        ret = []
        g = G[-1]
        S = solve_algebraic_univariate(make_univariate(g))
        S = [lift_with_identity(s,g.parent()) for s in S]
        for s in S:
            new_G = [s(h) for h in G[:-1]]
            ret += [merge(s,ss) for ss in solve_algebraic_groebner(new_G)]
        return ret

