# coding=utf-8

def afirstexample():
    with observer.report("A FIRST EXAMPLE!"):
        K.<x> = FunctionField(Qp(3,2))
        R.<t> = K[]
        G = t^3- 1 - 3*x^3 - 3*x^5
        L.<y> = K.extension(G)
        observer.log("G = %s!"%G)

        X = NormalModel(L, pAdicValuation(K.constant_base_field()))
        
        with observer.report("BLOWUP with center 0 and radius 0!"):
            B = X.blowup(0,0).normalization()
            with observer.ask("Is the special fiber reduced?", False) as question:
                question.answer(B.is_special_fiber_reduced())
            with observer.report("Eliminating ramification."):
                L = B.make_special_fiber_reduced()
                Y = X.change_ring(L)
                B = Y.blowup(0,0).normalization()
            with observer.ask("Is the special fiber reduced?", True) as question:
                question.answer(B.is_special_fiber_reduced())
            with observer.report("Computing the special fiber."):
                C = B.special_fiber()
                observer.log(C)
                D = C.ambient_space().subscheme(C.defining_ideal() + C.Jacobian())
                observer.log("Singularities at %s"%(D.rational_points(),))
        with observer.report("BLOWUP with center zeta and radius 1/12!"):
            K = X.base()
            R.<zeta> = K[]
            Delta = Delta_f(G[0].element().numerator(), 3)
            L.<zeta> = K.extension(Delta.change_variable_name("zeta").monic())
            Y = X.change_ring(L)
            B = Y.blowup(zeta, 1/12).normalization()
            with observer.ask("Is the special fiber reduced?", False) as question:
                question.answer(B.is_special_fiber_reduced())
            M, to_M = B.make_special_fiber_reduced()
            Mzeta = to_M(zeta)
            Y = X.change_ring(M)
            B = Y.blowup(Mzeta,1/12).normalization()
            with observer.ask("Is the special fiber reduced?", True) as question:
                question.answer(B.is_special_fiber_reduced())
            with observer.report("Computing the special fiber."):
                C = B.special_fiber()
                observer.log(C)
                D = C.ambient_space().subscheme(C.defining_ideal() + C.Jacobian())
                observer.log("Singularities at %s"%(D.rational_points(),))
        with observer.report("BLOWUP with center zeta and radius 1/8!"):
            R.<alpha> = L[]
            M, to_M = L.totally_ramified_extension(2)
            Mzeta = to_M(zeta)
            Y = X.change_ring(M)
            B = Y.blowup(Mzeta,1/8).normalization()
            with observer.ask("Is the special fiber reduced?", False) as question:
                question.answer(B.is_special_fiber_reduced())
            N = B.make_special_fiber_reduced()
            Z = Y.change_ring(N)
            B = Z.blowup(Mzeta,1/8).normalization()
            with observer.ask("Is the special fiber reduced?", True) as question:
                question.answer(B.is_special_fiber_reduced())
            with observer.report("Computing the special fiber."):
                C = B.special_fiber()
                observer.log(C)
                with observer.ask("Is the special fiber smooth?", True) as question:
                    question.answer(C.is_smooth())

class ModelComponent(object):
    def __init__(self, modelP1):
        self._modelP1 = modelP1

    @cached_method
    def valuations(self):
        return self._modelP1.valuation().mac_lane_approximants(self._G())

    @cached_method
    def _normalization(self):
        if not self.is_special_fiber_reduced():
            raise ValueError
        return normalization(self._modelP1.valuation(), self._modelP1._model._rational_function_field().extension(self._G()), assume_smooth=True)

    def special_fiber(self):
        I = self._normalization()[0]
        return Curve(AffineSpace(I.ring()).subscheme(I))

    def gens(self):
        return self._normalization()[1]

    def _G(self):
        return self._modelP1._model._G

    def is_special_fiber_reduced(self):
        return self._modelP1.is_special_fiber_reduced() and all([v.value_group() == 1 for v in self.valuations()])

    def __repr__(self):
        return "Components over %s"%self._modelP1

    def make_special_fiber_reduced(self):
        if not self._modelP1.is_special_fiber_reduced():
            raise ValueError
        return epp(self._G(), self._modelP1.valuation())

class ModelP1Component(object):
    def __init__(self, model, center, radius):
        self._model = model
        self._center = center
        self._radius = radius

    def is_special_fiber_reduced(self):
        return self.valuation().value_group() == 1

    @cached_method
    def normalization(self):
        return ModelComponent(self)

    def __repr__(self):
        return "Component corresponding to %s"%self.valuation()

    @cached_method
    def valuation(self):
        R = PolynomialRing(self._model.base(), names=self._model._variable_P1)
        vx = GaussValuation(R, self._model._vp)
        if self._center:
            assert self._radius > 0
        if self._radius > 0:
            vx = vx.extension(R.gen() - self._center, self._radius*self._model._vp(self._model.p()))

        return RationalFunctionFieldValuation(self._model._rational_function_field(), vx)

class NormalModel(object):
    def __init__(self, L, vp):
        self._G = L.polynomial()
        if vp.domain() != self._G.base_ring().constant_base_field():
            raise ValueError
        self._vp = vp
        self._variable_P1 = self._G.base_ring().variable_name()

    def base(self):
        return self._G.base_ring().constant_base_field()

    def _rational_function_field(self):
        return FunctionField(self.base(), names=self._variable_P1)

    def p(self):
        return self._vp.residue_field().characteristic()

    def change_ring(self, K, vp=None):
        if vp is None:
            vp = self._vp.extension(K)
        if vp.domain() != K:
            raise ValueError
        Kx = FunctionField(K, names= self._variable_P1)
        G = self._G.change_ring(Kx)
        return Model(self._rational_function_field().extension(G), vp)

    def blowup(self, center, radius):
        if center not in self._rational_function_field():
            raise ValueError
        if radius < 0:
            raise ValueError
        return ModelP1Component(self, center, radius)

def afirstexample_():
    with observer.report("A FIRST EXAMPLE!"):
        K.<x> = FunctionField(QQ)
        R.<t> = K[]
        G = t^3- 1 - 3*x^3 - 3*x^5
        observer.log("G = %s!"%G)
        K = Qp(3,3)
        with observer.report("THE MODEL OVER Z₃[x]!"):
            L = K
            try:
                ssred(G, L, 0, 0)
            except NormalizationNotReducedError:pass
            else: assert(False)
        with observer.report("THE MODEL OVER Z₃[pi,x] (with reduced special fiber)!"):
            R.<pi> = K[]
            L.<pi> = K.extension(pi^3 - 3)
            ssred(G, L, 0, 0)
        with observer.report("BLOWUP WITH CENTER zeta AND RADIUS 1/12!"):
            R.<zeta> = K[]
            Delta = Delta_f(G[0].element().numerator(), 3)
            L.<zeta> = K.extension(Delta.change_variable_name("zeta").monic())
            try:
                ssred(G, L, 1/12, zeta)
            except NormalizationNotReducedError:pass
            else: assert(False)
        with observer.report("BLOWUP WITH CENTER zeta AND RADIUS 1/12 (with reduced special fiber)!"):
            R.<alpha> = L[]
            #L.<alpha> = L.extension(alpha^3-(3*zeta^5+3*zeta^3+1))
            LL.<alpha> = L.extension(alpha^3 - zeta)
            with observer.report("Normalizing %s"%LL):
                LL,(alpha,LLzeta) = impl(LL,alpha,zeta)
            assert(Delta(LLzeta)==0)
            ssred(G, LL, 1/12, LLzeta)
        with observer.report("BLOWUP WITH CENTER zeta AND RADIUS 1/8!"):
            M, L_to_M = L.totally_ramified_extension(2)
            zeta = L_to_M(zeta)
            try:
                ssred(G, M, 1/8, zeta)
            except NormalizationNotReducedError:pass
            else: assert(False)
        with observer.report("BLOWUP WITH CENTER zeta AND RADIUS 1/8 (with reduced special fiber)!"):
            R.<Phi> = M[]
            N.<phi> = M.extension(Phi^3 + 2*M.gen()^24*Phi + M.gen()^34)
            with observer.report("Normalizing %s"%N):
                N,(zeta,) = impl(N,zeta)
            ssred(G, N, 1/8, zeta)

def ramification():
    with observer.report("A FIRST EXAMPLE!"):
        K.<x> = FunctionField(QQ)
        R.<t> = K[]
        G = t^3- 1 - 3*x^3 - 3*x^5
        observer.log("G = %s!"%G)
        K = Qp(3,3)
        with observer.report("BLOWUP WITH CENTER zeta AND RADIUS 1/12!"):
            R.<zeta> = K[]
            Delta = Delta_f(G[0].element().numerator(), 3)
            L.<zeta> = K.extension(Delta.change_variable_name("zeta").monic())
            #try:
            #    ssred(G, L, 1/12, zeta)
            #except NormalizationNotReducedError:pass
            #else: assert(False)
        with observer.report("BLOWUP WITH CENTER zeta AND RADIUS 1/8!"):
            M, L_to_M = L.totally_ramified_extension(2)
            zeta = L_to_M(zeta)
            #Kx,Rt,vx = SmartRationalFunctionFieldValuation(L, L.prime(), mu*L(L.prime()).valuation(), delta)
            ssred(G, M, 1/8, zeta)
            try:
                ssred(G, M, 1/8, zeta)
            except NormalizationNotReducedError:pass
            else: assert(False)
        with observer.report("BLOWUP WITH CENTER zeta and RADIUS 1/8 (and reduced special fiber)!"):
            R.<Phi> = M[]
            N.<phi> = M.extension(Phi^3+M.gen()^34)
            zeta = M(zeta)
            ssred(G, N, 1/8, zeta)

def liu10439():
    K.<x> = FunctionField(QQ)
    R.<t> = K[]
    G = t^4 - x^4 - 1
    observer.log("EXAMPLE: G = %s"%G)
    K = Qp(2,20)
    R.<pi> = K[]
    L.<pi> = K.extension(pi^8-2)
    ssred(G, L, 0, 0)

def liu10438():
    K.<x> = FunctionField(QQ)
    R.<t> = K[]
    G = t^2 - x^8 + 5*x^6 - 10*x^4 + 10*x^2 - 5
    observer.log("EXAMPLE: G = %s"%G)
    Delta = Delta_f(G[0].element().numerator(), 3)
    Delta = Delta.factor()[1][0]
    K = Qp(2)
    R.<pi> = K[]
    L.<pi> = K.extension(pi^2-2)
    R.<t> = K[]
    Delta = Delta(t/pi)*pi^20
    R.<psi> = L[]
    L.<psi> = L.extension(Delta)
    return L
    L = Qp(2,10)
    R.<pi> = L[]
    L.<pi> = L.extension(pi^4-2)
    ssred(G, L, 0, 0)

    #ssred(G, L, 1/2, 0)


def kai3():
    K.<x> = FunctionField(QQ)
    R.<t> = K[]
    G = t^9 - 1 - x^2
    observer.log("EXAMPLE: G = %s"%G)
    G = normal_form(G)
    observer.log("in normal form: %s"%G)
    L = Qp(3,20)
    ssred(G, L, 0, 0)

def kai2():
    K.<x> = FunctionField(QQ)
    R.<t> = K[]
    G = t^7 - (x^3 - 2*x^2 - x + 1)/(x^3 - x^2 - 2*x + 1)
    observer.log("EXAMPLE: G = %s"%G)
    G = normal_form(G)
    observer.log("in normal form: %s"%G)
    K = Qp(7,10)
    R.<zeta> = K[]
    Delta = Delta_f(G[0].element().numerator().change_ring(K), 7)
    R.<zeta> = K[]
    L.<zeta> = K.extension(Delta.monic())
    ssred(G, L, 1/3, 3)

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

            with observer.ask("Is the special fiber of the model of P¹ reduced?") as question:
                if not question.answer(vx.value_group() == vx._base_valuation.constant_valuation().value_group()):
                    raise P1NotReducedError

            G = G.map_coefficients(Kx,Kx)

            with observer.ask("Is the special fiber of the normalization reduced?") as question:
                with observer.report("Computing valuations of normalization."):
                    W = vx.mac_lane_approximants(G)
                    observer.log("special fiber has %s irreducible components"%len(W))
                if not question.answer(vx.value_group() == prod([v.value_group() for v in W])):
                    raise NormalizationNotReducedError

            with observer.report("Computing the special fiber of the normalization."):
                observer.log("the components of the special fiber have genus %s"%[w.residue_field().genus() for w in W])
                I,gens = normalization(vx, Kx.extension(G), assume_smooth=True)

            C = AffineSpace(I.ring()).subscheme(I)
            observer.log("special fiber is %s"%C)

            with observer.ask("Is the special fiber smooth?") as is_smooth:
                assert( len(C.irreducible_components()) == len(W) )
                if is_smooth.answer(C.is_smooth()):
                    return

            [c.element().reduce() for g in gens for c in g.coefficients()]
            observer.log("the variables on the special fiber are reductions of (starting with x,z0,...):\n %s"%gens)

            with observer.report("Computing singularities."):
                J = C.Jacobian()
                D = AffineSpace(I.ring()).subscheme(J)
                singularities = rational_points(D)
                if not singularities:
                    observer.log("The base field is too small to see the singularities.")
                    raise SingularitiesNotRational

            observer.log("singularities are at %s"%singularities)

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

def normal_form(G):
    if not G.is_monic():
        raise NotImplementedError
    D = lcm([c.denominator() for c in G.coeffs()])
    H = G*(D**G.degree())
    ret = H(G.parent().gen()/D)
    assert ret.is_monic()
    return ret

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
        if R.ngens() > 1:
            observer.log("with groebner basis: %s"%R.ideal(equations).groebner_basis())
            D = AffineSpace(R).subscheme(equations)
            ret = D.rational_points(F)
        else:
            if len(equations)!= 1:
                raise NotImplementedError
            ret = [[r] for r in equations[0].roots(multiplicities=False)]
        ret = [[constants[v] if v in constants else r[R.gens().index(v)] for v in S.gens()] for r in ret]
        while not all([all([s in R.base() for s in r]) for r in ret]):
            ret = [[s(r) if s not in R.base() else s for s in r] for r in ret]
        ret = [[R.base()(s) for s in r] for r in ret]
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
                        w = w/vK.uniformizer()^(vx(w.norm())//w.parent().degree())
                        observer.log("%s is another generator"%w)
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
    to_ = Kx.hom([Kx.gen()*pi-delta])
    H = G.map_coefficients(to_)
    observer.log("shifted defining polynomial is %s"%H)
    LH = Kx.extension(H)
    J,gens = normalization_gauss(LH, vK, assume_smooth)
    # substitute back
    from_ = Kx.hom([(Kx.gen()+delta)/pi])
    gens = [g.element().map_coefficients(from_) for g in gens]
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
    if delta:
        assert vx_ != 0
    if vx_ != 0:
        vx = vx.extension(x-delta,vx_)
    K.<x> = FunctionField(L)
    vx = RationalFunctionFieldValuation(K,vx)
    R.<t> = K[]
    K.inject_variables(verbose=False)
    R.inject_variables(verbose=False)
    return K,R,vx

def impl(L, *args):
    def impl1(L, *args):
        assert all(a in L for a in args)
        ret = L._implementation_ring()[0]
        rets = []
        for a in args:
            if a.parent() is ret:
                rets.append(a)
            a = L(a)
            rets.append(a._element)
        return ret, rets

    while hasattr(L,'_implementation_ring'):
        L,args = impl1(L,*args)
    return L,args

def ppprint(f, variables=['x'], delimiters = [','], substitutions=[('pi','π'),('zeta_2','ζ₂'),('zeta','ζ')]):
    f = repr(f)
    for var in variables:
        substitutions.append((var,"\x1b[31;1m"+var+"\x1b[0m"))
    for k,v in substitutions:
        f = f.replace(k,v)
    for d in delimiters:
        f = f.replace(d, d+"\n")
    print f
   
# Α, α      Alpha (ἄλφα)    álfa (άλφα) a   [a], [aː]   a, αι = e   [a]
# Β, β    ϐ   Beta (βῆτα) víta (βήτα) b   [b] v   [v]
# Γ, γ        Gamma (γάμμα)   gám(m)a (γάμ(μ)α)   g   [g] g, γγ = ng, γκ = ng,
# γχ = nch, γξ = nx   [ɣ], [j]
# Δ, δ        Delta (δέλτα)   délta (δέλτα)   d   [d] d   [ð]
# Ε, ε    ϵ   Epsilon (ἔ ψιλόν)   épsilon (έψιλον)    e   [e] e, entfällt vor ι   [ɛ]
# Ζ, ζ        Zeta (ζῆτα) zíta (ζήτα) z   [zd], [dz]  z   [z]
# Η, η        Eta (ἦτα)   íta (ήτα)   ē   [ɛː]    i   [i]
# Θ, θ    ϑ   Theta (θῆτα)    thíta (θήτα)    th  [tʰ]    th  [θ]
# Ι, ι        Iota (ἰῶτα) ióta (ιώτα) i   [i], [iː]   i   [i], [j]
# Κ, κ    ϰ   Kappa (κάππα)   káp(p)a (κάπ(π)α)   k   [k] k   [k], [kʲ]
# Λ, λ        Lambda (λάμβδα) lámda (λάμδα)   l   [l] l   [l]
# Μ, μ        My (μῦ) mi (μι) m   [m] m   [m]
# Ν, ν        Ny (νῦ) ni (νι) n   [n] n   [n]
# Ξ, ξ        Xi (ξῖ) xi (ξι) x   [ks]    x   [ks]
# Ο, ο        Omikron (ὄ μικρόν)  ómikron (όμικρον)   o   [o] o, entfällt vor ι   [ɔ]
# Π, π    ϖ   Pi (πῖ) pi (πι) p   [p] p, μπ = (m)b5   [p]
# Ρ, ρ    ϱ   Rho (ῥῶ)    ro (ρω) r(h)    [r], [rʰ]   r   [r]
# Σ, σ    ς6, Ϲ7  Sigma (σῖγμα)   sígma (σίγμα)   s   [s], [z]    s   [s], [z]
# Τ, τ        Tau (ταῦ)   taf (ταυ)   t   [t] t, ντ = (n)d5   [t]
# Υ, υ        Ypsilon (ὔ ψιλόν)   ýpsilon (ύψιλον)    y
# bei αυ, ευ, ου: u   [y], [yː]   y, nach Vokal v oder f  [i], [v], [f]
# Φ, φ    ϕ   Phi (φῖ)    fi (φι) ph  [pʰ]    f   [f]
# Χ, χ        Chi (χῖ)    chi (χι)    ch  [kʰ]    ch  [x], [ç]
# Ψ, ψ        Psi (ψῖ)    psi (ψι)    ps  [ps]    ps  [ps]
# Ω, ω        Omega (ὦ μέγα)  oméga (ωμέγα)   ō   [ɔː]    o   [ɔ]
