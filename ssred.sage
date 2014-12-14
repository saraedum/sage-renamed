def kai1():
    R.<t,x> = ZZ[]
    G = t^3- 1 - 3*x^3 - 3*x^5
    observer.log("EXAMPLE: G = %s"%G)
    K = Qp(3,3)
    try:
        ssred(G, K, 0, 0)
    except NormalizationNotReducedError: pass
    else: assert(False)

    observer.log("\n\nExtending base field to make special fiber reduced!")
    R.<pi> = K[]
    L.<pi> = K.extension(pi^3-3)
    ssred(G, L, 0, 0)

    observer.log("\n\nShrinking disk!")
    try:
        ssred(G, L, 1/12, 0)
    except P1NotReducedError: pass
    else: assert(False)

    observer.log("\n\nExtending base field to make special fiber of P¹ reduced!")
    R.<pi> = K[]
    L.<pi> = K.extension(pi^12-3)
    try:
        ssred(G, L, 1/12, 0)
    except NormalizationNotReducedError: pass
    else: assert(False)

    observer.log("\n\nExtending base field to make special fiber reduced!")
    R.<pi> = K[]
    L.<pi> = K.extension(pi^36-3)
    try:
        ssred(G, L, 1/12, 0)
    except SingularitiesNotRational: pass
    else: assert(False)

    observer.log("\n\nExtending base field to make the singularities rational!")
    R.<a> = K[]
    L.<a> = K.extension(a^2+2*a+2)
    R.<pi> = L[]
    M.<pi> = L.extension(pi^36-3)
    ssred(G, M, 1/12, 0)

from observer import Observer
from threading import current_thread

if not "observer" in globals():
    observer = Observer(current_thread().ident)
    observer.start()

class P1NotReducedError(Exception): pass
class NormalizationNotReducedError(Exception): pass
class SingularitiesNotRational(Exception): pass

def ssred(G, L, mu, delta):
    try:
        with observer.report("Now working with radius=%s and center=%s over %s"%(mu, delta, L)):
            Kx,Rt,vx = SmartRationalFunctionFieldValuation(L, L.prime(), mu*L(L.prime()).valuation(), delta)
            observer.log("model of P¹ is given by %s"%vx)

            with observer.ask("Is the special fiber the model of P¹ reduced?") as question:
                if not question.answer(vx.value_group() == vx._base_valuation.constant_valuation().value_group()):
                    raise P1NotReducedError

            G = G(t,x)

            with observer.ask("Is the special fiber of the normalization reduced?") as question:
                with observer.report("Computing valuations of normalization."):
                    W = vx.mac_lane_approximants(G)
                    observer.log("special fiber has %s irreducible components"%len(W))
                if not question.answer(vx.value_group() == prod([v.value_group() for v in W])):
                    raise NormalizationNotReducedError

            with observer.report("Computing the special fiber of the normalization."):
                I,gens = normalization(vx, Kx.extension(G), assume_smooth=True)

            C = AffineSpace(I.ring()).subscheme(I)
            observer.log("special fiber is %s"%C)

            with observer.ask("Is the special fiber smooth?") as is_smooth:
                assert( len(C.irreducible_components()) == len(W) )
                if is_smooth.answer(C.is_smooth()):
                    return

            with observer.report("Computing singularities."):
                J = C.Jacobian()
                D = AffineSpace(I.ring()).subscheme(J)
                singularities = rational_points(D)
                if not singularities:
                    observer.log("The base field is too small to see the singularities.")
                    raise SingularitiesNotRational

            observer.log("singularities are at %s"%singularities)
            observer.log("the variables on the special fiber are reductions of (starting with x,z0,...):\n %s"%gens)

            for CC in C.irreducible_components():
                with observer.report("Invariants of singularities on %s"%C):
                    with observer.ask("Is this component smooth?") as is_smooth:
                        if is_smooth.answer(CC.is_smooth()): continue
                    for singularity in rational_points(AffineSpace(I.ring()).subscheme(CC.Jacobian())):
                        # shift singularity to O
                        equations = [p([g+s for g,s in zip(CC.ambient_space().coordinate_ring().gens(),singularity)]) for p in CC.defining_polynomials()]
                        with observer.ask("Is %s obviously a singularity of a plane curve?"%singularity) as is_plane:
                            nontrivials = [e for e in equations if e.degree()!=1]
                            assert nontrivials
                            if len(nontrivials) >= 2:
                                is_plane.answer(False)
                                continue
                            if len(nontrivials[0].variables()) >= 3:
                                is_plane.answer(False)
                                continue
                            is_plane.answer(True)
                        # for a plane curve this is easy (CurveBook)
                        equation = nontrivials[0]
                        X,Y = equation.variables()
                        m = min([sum(e) for e in equation.exponents()])
                        assert m >= 2
                        Fm = sum([c*mon for (c,mon) in list(equation) if mon.degree()==m])
                        FM = Fm.factor()
                        ordinary = all([e==1 for (_,e) in FM])
                        if m == 2: multiplicity = "double point"
                        elif m == 3: multiplicity = "triple point"
                        else: multiplicity = "point with multiplicity %s"%m
                        observer.log("%s is an %s %s."%(singularity, "ordinary" if ordinary else "non-ordinary", multiplicity))
                     
    finally:
        globals().update(locals())

def rational_points(C, F=None):
    with observer.report("Finding rational points of scheme."):
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
        observer.log("after removal of trivial equations I have to solve %s"%equations)
        observer.log("with groebner basis: %s"%R.ideal(equations).groebner_basis())
        D = AffineSpace(R).subscheme(equations)
        ret = D.rational_points(F)
        ret = [[constants[v] if v in constants else r[R.gens().index(v)] for v in S.gens()] for r in ret]
        while not all([all([s in D.base() for s in r]) for r in ret]):
            ret = [[s(r) if s not in D.base() else s for s in r] for r in ret]
        ret = [[D.base()(s) for s in r] for r in ret]
        return ret

# compute the normalization of the component (minus one point) corresponding to the Gauss valuation in L
# the missing point is x=infinity
def normalization_gauss(L, vK, assume_smooth=False):
    K = vK.domain()
    Kx = L.base()
    G = L.polynomial()
    R = Kx.maximal_order()._ring
    v0 = GaussValuation(R, vK)
    vx = RationalFunctionFieldValuation(Kx,v0)

    S.<x,t> = vK.domain()[]
    if not all([c.denominator().is_one() for c in G.coefficients()]):
        raise ValueError
    F = G.map_coefficients(lambda c:c.numerator(), R)(t)
    with observer.ask("Does F=%s define a smooth curve?"%F, True) as F_smooth:
        if not assume_smooth:
            F_smooth.answer(F_smooth, AffineSpace(S).subscheme(F).is_smooth())
        else:
            observer.log("WARNING: I have not checked.",color="red")
            F_smooth.answer(True)

    with observer.report("Computing generators of the normalization."):
        global B,B_
        B = [L.gen()]
        B_ = [None]
        extra = []
        while True:
            with observer.ask("Does B=%s generate the normalization?"%(B,)) as generates:
                names = ['z%s'%i for i in range(len(B))]
                R_ = PolynomialRing(vK.residue_field(), [Kx.variable_name()] + names)
                for i,b in enumerate(B):
                    if B_[i] is None:
                        with observer.report("Determining equation for %s in reduction."%b):
                            B_[i] = B[i].charpoly(names[i])
                            B_[i].map_coefficients(lambda c:c.element().reduce())
                            assert(all([c.denominator().is_one() for c in B_[i].coefficients()]))
                            B_[i] = B_[i].map_coefficients(lambda c:c.numerator(),R)(S.gen(1))
                            observer.log("the element satisfies %s"%(B_[i],))
                            B_[i] = B_[i].map_coefficients(vK.reduce,vK.residue_field())(R_.gen(0),R_.gen(i+ 1))
                            observer.log("in reduction this is %s"%(B_[i],))
                I = R_.ideal(B_+extra)
                J = I.radical()
                for i,g in enumerate(J.gens()):
                    if g not in I:
                        observer.log("%s is only in the radical."%g)
                        generates.answer(False)
                        z = g.map_coefficients(lambda c:vK.lift(c), K)([x]+B[:len(names)])
                        w = z
                        while vx((w/vK.uniformizer()).norm())>=0:
                            w = w/vK.uniformizer()
                        assert w not in B 
                        if B_[-1] is not None:
                            B.append(w)
                            B_.append(None)
                            extra.append(g)
                if all(B_):
                    generates.answer(True)
                    return J, [L(Kx.gen())]+B

# compute the normalization of the component (minus one point) corresponding to v in L
def normalization(v, L, assume_smooth=False):
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
    pi = v1.element_with_valuation(v1(v1.phi()))
    # y = (x+delta)/pi
    # → x = y*pi-delta
    G = L.polynomial()
    if not all([c.denominator().is_one() for c in G.coefficients()]):
        raise NotImplementedError
    H = G.map_coefficients(lambda c:c.numerator()(c.numerator().parent().gen()*pi - delta))
    LH = Kx.extension(H)
    J,gens = normalization_gauss(LH, vK, assume_smooth)
    # substitute back
    x_ = Kx._ring.gen()
    gens = [g.element().map_coefficients(lambda c:Kx._field(c.numerator()((x_+delta)/pi),c.denominator()((x_+delta)/pi))) for g in gens]
    return J,gens

"""
# KAI 1 (global)
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

def SmartRationalFunctionFieldValuation(L, p, vx_=0, delta=0):
    if L in DiscreteValuationFields():
        vL = pAdicValuation(L)
    else:
        vp = pAdicValuation(QQ, p)
        vL = vp.extension(L)

    R.<x> = L[]
    vx = GaussValuation(R,vL)
    if vx_ != 0:
        print vx,x-delta
        vx = vx.extension(x-delta,vx_)
    K.<x> = FunctionField(L)
    vx = RationalFunctionFieldValuation(K,vx)
    R.<t> = K[]
    K.inject_variables(verbose=False)
    R.inject_variables(verbose=False)
    return K,R,vx
