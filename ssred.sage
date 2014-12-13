"""
# KAI 1
%attach ssred.sage
%runfile epp.sage
Kx,Rt,vx = SmartRationalFunctionFieldValuation(QQ,3)
G = t^3 - 1 - 3*x^3 - 3*x^5
# is the special fiber of the model of P1 reduced?
vx.value_group() == vx._base_valuation.constant_valuation().value_group()
# is the special of the normalization reduced?
vx.value_group() == prod([v.value_group() for v in vx.mac_lane_approximants(G)])
# make it reduced
R.<pi> = QQ[]
L.<pi> = NumberField(pi^3-3)
Kx,Rt,vx = SmartRationalFunctionFieldValuation(L,3)
vL = vx._base_valuation.constant_valuation()
G = t^3 - 1 - 3*x^3 - 3*x^5
vx.value_group() == prod([v.value_group() for v in vx.mac_lane_approximants(G)])
# compute the special fiber of the normalization
I,gens = normalization_gauss(Kx.extension(G),vL)
C = AffineSpace(I.ring()).subscheme(I)
C.is_smooth()
# where are the singularities?
J = C.Jacobian()
AffineSpace(I.ring()).subscheme(I+J).rational_points()
gens # to see what the coordinates mean

# blow up in x=0 with radius lambda=1/12
Kx,Rt,vx = SmartRationalFunctionFieldValuation(L, 3, 1/4)
# is the model of P1 reduced?
vx.value_group() == vx._base_valuation.constant_valuation().value_group()
# make it reduced
R.<pi> = QQ[]
L.<pi> = NumberField(pi^12-3)
Kx,Rt,vx = SmartRationalFunctionFieldValuation(L, 3, 1)
vx.value_group() == vx._base_valuation.constant_valuation().value_group()
# is the special fiber of the normalization reduced?
G = t^3 - 1 - 3*x^3 - 3*x^5
vx.value_group() == prod([v.value_group() for v in vx.mac_lane_approximants(G)])
# no, so make it reduced
R.<pi> = QQ[]
L.<pi> = NumberField(pi^36-3)
Kx,Rt,vx = SmartRationalFunctionFieldValuation(L, 3, 3)
G = t^3 - 1 - 3*x^3 - 3*x^5
vx.value_group() == prod([v.value_group() for v in vx.mac_lane_approximants(G)])
# compute the special fiber of the normalization
I,gens = normalization(vx, Kx.extension(G))
C = AffineSpace(I.ring()).subscheme(I)
C.is_smooth()
J = C.Jacobian()
D = AffineSpace(I.ring()).subscheme(I+J)
# find the singularities over a sufficiently large field
k.<a> = GF(9)
rational_points(D,k)

# enlarge the base field so we have F9 in the residue field
R.<a> = L[]
M.<a> = L.extension(a^2+2*a+2)
L.<b> = M.absolute_field()
L.<b> = NumberField(L.polynomial().change_variable_name('b'),maximize_at_primes=[3])
pi = b^2+2*b+2
R.<a> = L[];
a = (a^2+2*a+2).any_root()
Kx,Rt,vx = SmartRationalFunctionFieldValuation(L, 3, 3, a)
# is the model of P1 reduced?
vx.value_group() == vx._base_valuation.constant_valuation().value_group()
# is the special fiber of the normalization reduced?
G = t^3 - 1 - 3*x^3 - 3*x^5
vx.value_group() == prod([v.value_group() for v in vx.mac_lane_approximants(G)])
I,gens = normalization(vx, Kx.extension(G))







"""

def rational_points(C, F=None):
    equations = list(C.defining_polynomials())
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
    S = equations[0].parent()
    R = S.remove_var(*constants.keys())
    equations = [R(e) for e in equations]
    print "After removal of trivial equations: %s"%equations
    print "With groebner basis: %s"%R.ideal(equations).groebner_basis()
    D = AffineSpace(R).subscheme(equations)
    ret = D.rational_points(F)
    ret = [[constants[v] if v in constants else r[R.gens().index(v)] for v in S.gens()] for r in ret]
    print ret
    return 

    C = AffineSpace

# compute the normalization of the component (minus one point) corresponding to the Gauss valuation in L
# the missing point is x=infinity
def normalization_gauss(L, vK, assume_wu=False):
    K = vK.domain()
    Kx = L.base()
    G = L.polynomial()
    R = Kx.maximal_order()._ring
    v0 = GaussValuation(R, vK)
    vx = RationalFunctionFieldValuation(Kx,v0)

    if not assume_wu:
        W = vx.mac_lane_approximants(G)
        if any([w.value_group() != vK.value_group() for w in W]):
            raise ValueErrror("all extensions must be weakly unramified over vK")

    S.<x,t> = vK.domain()[]
    if not all([c.denominator().is_one() for c in G.coefficients()]):
        raise ValueError
    F = G.map_coefficients(lambda c:c.numerator(), R)(t)
    print "F=%s"%F
    print "L=%s"%L
    if not AffineSpace(S).subscheme(F).is_smooth():
        raise NotImplementedError("F must define a smooth curve.")

    B = [L.gen()]
    B_ = [None]
    extra = []
    while True:
        print "B=< %s >"%(B,)
        names = ['z%s'%i for i in range(len(B))]
        R_ = PolynomialRing(vK.residue_field(), [Kx.variable_name()] + names)
        for i,b in enumerate(B):
            if B_[i] is None:
                print "determining equation for %s"%b
                B_[i] = B[i].charpoly(names[i])
                print "charpoly is %s"%(B_[i],)
                assert([c.denominator().is_one() for c in B_[i].coefficients()])
                B_[i] = B_[i].map_coefficients(lambda c:c.numerator(),R)(S.gen(1))
                B_[i] = B_[i].map_coefficients(vK.reduce,vK.residue_field())(R_.gen(0),R_.gen(i+ 1))
                print "which reduces to %s"%(B_[i],)
        I = R_.ideal(B_+extra)
        print I
        J = I.radical()
        print J
        print AffineSpace(J.ring()).subscheme(J).irreducible_components()
        for i,g in enumerate(J.gens()):
            if g not in I:
                print "g=%s not in I"%g
                z = g.change_ring(K)([x]+B[:len(names)])
                w = z/vK.uniformizer()
                assert w not in B 
                if B_[-1] is not None:
                    B.append(w)
                    B_.append(None)
                    extra.append(g)
        if all(B_):
            return J, [L(Kx.gen())]+B

# compute the normalization of the component (minus one point) corresponding to v in L
def normalization(v, L, assume_wu=False):
    # substitute so v looks like a Gauss valuation
    Kx = L.base()
    if v.domain() is not Kx:
        raise ValueError("v must be defined on the rational function field underlying L")
    vK = v._base_valuation.constant_valuation()

    v1 = v._base_valuation
    if v1.phi().degree()!=1:
        raise ValueError("v must be geometrically irreducible")
    # v1(x+delta) = v(pi)
    delta = v1.phi()[0]
    pi = vK.uniformizer()**v1._mu
    # y = (x+delta)/pi
    # → x = y*pi-delta
    G = L.polynomial()
    if not all([c.denominator().is_one() for c in G.coefficients()]):
        raise NotImplementedError
    H = G.map_coefficients(lambda c:c.numerator()(c.numerator().parent().gen()*pi - delta))
    LH = Kx.extension(H)
    J,gens = normalization_gauss(LH, vK, assume_wu)
    # substitute back
    x_ = Kx._ring.gen()
    gens = [g.element().map_coefficients(lambda c:Kx._field(c.numerator()((x_+delta)/pi),c.denominator()((x_+delta)/pi))) for g in gens]
    return J,gens
