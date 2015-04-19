# coding=utf-8

# KAI (local)
"""
sage: %attach ssred.sage
sage: K = Qp(3)
sage: v = pAdicValuation(K)
sage: K.<x> = FunctionField(K)
sage: R.<t> = K[]
sage: G = t^3 - 1 - 3*x^3 - 3*x^5
sage: L.<y> = K.extension(G)

sage: X = NormalModel(L,v)
sage: Y = X.blowup(0,0).normalization()
sage: Y.is_special_fiber_reduced()
False
sage: Y = Y.make_special_fiber_reduced()
"""

use_norm = True

def any_root(F,name):
    M = F.base_ring()
    try:
        return M,F.any_root()
    except IndexError:
        M = M.extension(F, names=name)
        return M, F.change_ring(M).any_root()

def Y2(radius=3/2,prec=40,M=None,n=2,center=None):
    with observer.report("Y2"):
        K.<x> = FunctionField(Qp(2,prec))
        R.<t> = K[]
        G = t^(2^n) - x*(x^2-1)
        L.<y> = K.extension(G)
        observer.log("G = %s!"%G)

        X = NormalModel(L, pAdicValuation(K.constant_base_field()))

        if M is None:
            M = K.constant_base_field()

        if center is None:
            R.<t> = M[]
            M, si = any_root(t^4+1,'si')
            print M
            R.<t> = M[]
            M, zeta = any_root(t^2 - (1/3 + 4/9*si),'zeta')
            print M
            center = zeta

        X = X.change_ring(M)
        return X.blowup(center, radius).normalization()

def obus1(prec=40,radius=1, M=None):
    with observer.report("OBUS 1"):
        K.<x> = FunctionField(Qp(2,prec))
        R.<t> = K[]
        G = t^2 - x*(x^2-1)
        L.<y> = K.extension(G)
        observer.log("G = %s!"%G)

        X = NormalModel(L, pAdicValuation(K.constant_base_field()))
        if M is None:
            K = X.base()
            R.<si> = K[]
            L.<si> = K.extension(si^4+1)
            L,(si,) = impl(L,si)

            if not radius.denominator().divides(L.degree()):
                L, to_L = L.totally_ramified_extension(radius.denominator()//L.degree())
                si = to_L(si)
                L, (si,) = impl(L, si)
        else:
            L = M

        R.<t> = L[]
        si = (t^4+1).any_root()
        zeta = (t^2 - (1/3 + 4*si/9)).roots(multiplicities=False)[0]
        i = si^2
        assert i^2==-1
        assert zeta^2 - (1/3 + 4*si/9) == 0
        assert (zeta**2 -1/3)*9/4 != 1 and ((zeta^2 -1/3)*9/4)**2 != 1 and ((zeta^2 -1/3)*9/4)**4 == -1,  ((zeta**2 -1/3)*9/4, "**********", ((zeta**2 -1/3)*9/4)**2 , "**************", ((zeta**2 -1/3)*9/4)**4)
        with observer.report("BLOWUP with center %s and radius %s!"%(zeta,radius)):
            X_ = X.change_ring(L)
            Y_ = X_.blowup(zeta,radius).normalization()
            return Y_
            if not Y_.is_special_fiber_reduced():
                M, to_M = Y_.make_special_fiber_reduced()
                M, (zeta,) = impl(M, to_M(zeta))
                try:
                    X_ = X_.change_ring(M)
                except:
                    X_ = X.change_ring(M)
                Y_ = X_.blowup(zeta,radius).normalization()
            return Y_

def obus2_0(prec=40):
    with observer.report("OBUS 2/0"):
        K.<x> = FunctionField(Qp(2,prec))
        R.<t> = K[]
        G = t^4 - x*(x^2-1)
        L.<y> = K.extension(G)
        observer.log("G = %s!"%G)

        X = NormalModel(L, pAdicValuation(K.constant_base_field()))
        #L = M
        #R.<t> = M[]
        zeta = 0
        radius = 0
        with observer.report("BLOWUP with center %s and radius %s!"%(zeta,radius)):
            #X_ = X.change_ring(L)
            Y_ = X.blowup(zeta,radius).normalization()
            if not Y_.is_special_fiber_reduced():
                M, to_M = Y_.make_special_fiber_reduced()
                M, (zeta,) = impl(M, to_M(zeta))
                try:
                    X_ = X_.change_ring(M)
                except:
                    X_ = X.change_ring(M)
                Y_ = X_.blowup(zeta,radius).normalization()
            return Y_

def obus2_1(M, prec=40):
    with observer.report("OBUS 2/1"):
        K.<x> = FunctionField(Qp(2,prec))
        R.<t> = K[]
        G = t^4 - x*(x^2-1)
        L.<y> = K.extension(G)
        observer.log("G = %s!"%G)

        X = NormalModel(L, pAdicValuation(K.constant_base_field()))
        L = M
        R.<t> = M[]
        zeta = (t^4-2*t^2-1/3).any_root()
        radius = 1
        with observer.report("BLOWUP with center %s and radius %s!"%(zeta,radius)):
            X_ = X.change_ring(L)
            Y_ = X_.blowup(zeta,radius).normalization()
            if not Y_.is_special_fiber_reduced():
                M, to_M = Y_.make_special_fiber_reduced()
                M, (zeta,) = impl(M, to_M(zeta))
                try:
                    X_ = X_.change_ring(M)
                except:
                    X_ = X.change_ring(M)
                Y_ = X_.blowup(zeta,radius).normalization()
            return Y_

def obus2(prec=40,radius=3/2):
    with observer.report("OBUS 2"):
        K.<x> = FunctionField(Qp(2,prec))
        R.<t> = K[]
        G = t^4 - x*(x^2-1)
        L.<y> = K.extension(G)
        observer.log("G = %s!"%G)

        X = NormalModel(L, pAdicValuation(K.constant_base_field()))
        K = X.base()
        R.<si> = K[]
        L.<si> = K.extension(si^4+1)
        L,(si,) = impl(L,si)
        if not radius.denominator().divides(L.degree()):
            L, to_L = L.totally_ramified_extension(radius.denominator()//L.degree())
            si = to_L(si)
            L, (si,) = impl(L, si)

        R.<t> = L[]
        zeta = (t^2 - (1/3 + 4*si/9)).roots(multiplicities=False)[1]
        assert (zeta**2 -1/3)*9/4 != 1 and ((zeta^2 -1/3)*9/4)**2 != 1 and ((zeta^2 -1/3)*9/4)**4 == -1,  ((zeta**2 -1/3)*9/4, "**********", ((zeta**2 -1/3)*9/4)**2 , "**************", ((zeta**2 -1/3)*9/4)**4)
        with observer.report("BLOWUP with center %s and radius %s!"%(zeta,radius)):
            X_ = X.change_ring(L)
            Y_ = X_.blowup(zeta,radius).normalization()
            if not Y_.is_special_fiber_reduced():
                M, to_M = Y_.make_special_fiber_reduced()
                M, (zeta,) = impl(M, to_M(zeta))
                try:
                    X_ = X_.change_ring(M)
                except:
                    X_ = X.change_ring(M)
                Y_ = X_.blowup(zeta,radius).normalization()
            return Y_

def obus2_(Y):
    X_ = Y._modelP1
    X = X_._model

    if len(Y.valuations()) == 1:
        return Y.base(),Y.base().hom(Y.base())
    assert len(Y.valuations()) == 2
    w=Y.valuations()[1]
    G= X._G
    w=w.mac_lane_step(G)[0]
    w=w.mac_lane_step(G)[0]
    w=w.mac_lane_step(G)[0]
    w=w.mac_lane_step(G)[0]
    w=w.mac_lane_step(G)[0]
    w=w.mac_lane_step(G)[0]

    return epp(w.phi(), w.constant_valuation())

def obus2__(M,prec=40, radius=3/2):
    with observer.report("OBUS 2__"):
        K.<x> = FunctionField(Qp(2,prec))
        R.<t> = K[]
        G = t^4 - x*(x^2-1)
        L.<y> = K.extension(G)
        observer.log("G = %s!"%G)

        X = NormalModel(L, pAdicValuation(K.constant_base_field()))
        X = X.change_ring(M)
        R.<t> = M[]
        si = (t^4+1).any_root()
        zeta = (t^2 - (1/3 + 4*si/9)).roots(multiplicities=False)[1]
        assert (zeta**2 -1/3)*9/4 != 1 and ((zeta^2 -1/3)*9/4)**2 != 1 and ((zeta^2 -1/3)*9/4)**4 == -1,  ((zeta**2 -1/3)*9/4, "**********", ((zeta**2 -1/3)*9/4)**2 , "**************", ((zeta**2 -1/3)*9/4)**4)
        L = M
        with observer.report("BLOWUP with center %s and radius %s!"%(zeta,radius)):
            X_ = X.change_ring(L)
            Y_ = X_.blowup(zeta,radius).normalization()
            assert Y_.is_special_fiber_reduced()
            return Y_

def OBUS2(prec=40,radius=3/2):
    Y = obus2(prec=prec,radius=radius)
    if Y.is_special_fiber_reduced(): return Y
    M,to_M = obus2_(Y)
    M,_ = impl(M)
    return obus2__(M,prec=prec,radius=radius)


#L.<si> = K.extension(t^8+1)
#L,(si,) = impl(L,si)
#assert si^8 == -1

#R.<t> = L[]
#s2nb = (t^2-8).any_root()

#zeta = 1/3 + s2nb*si/9

#R.<t> = L[]
#L.<zeta> = L.extension(t^2 - zeta)
#L,(zeta,) = impl(L, zeta)
        
#        X = NormalModel(L, pAdicValuation(K.constant_base_field()))
#
#        K = X.base()
#        R.<t> = K[]
#        L.<si> = K.extension(t^8+1)
#        L,(si,) = impl(L,si)
#        assert si^8 == -1
#
#        R.<t> = L[]
#        s2nb = t^2 - 2^n*b
#        s2nb = s2nb.any_root()
#
#        s = n - b.valuation(2)
#        if radius is None:
#            radius = n - s/2 + 1/2
#        zeta = a/(a+b) + (s2nb*si)/((a+b)^2)
#        with observer.report("BLOWUP with center %s and radius %s!"%(zeta,radius)):
#            X_ = X.change_ring(L)
#            Y_ = X_.blowup(zeta,radius).normalization()
#            if not Y_.is_special_fiber_reduced():
#                M, to_M = Y_.make_special_fiber_reduced()
#                M, (zeta,) = impl(M, to_M(zeta))
#                try:
#                    X_ = X_.change_ring(M)
#                except:
#                    X_ = X.change_ring(M)
#                Y_ = X_.blowup(zeta,radius).normalization()
#            return Y_


#def obus(a,b,n,prec=40,radius=None):
#    with observer.report("OBUS a=%s b=%s n=%s"%(a,b,n)):
#        K.<x> = FunctionField(Qp(2,prec))
#        R.<t> = K[]
#        G = t^(2^n) - x^a*(x-1)^b
#        L.<y> = K.extension(G)
#        observer.log("G = %s!"%G)
#        
#        X = NormalModel(L, pAdicValuation(K.constant_base_field()))
#
#        K = X.base()
#        R.<t> = K[]
#        L.<si> = K.extension(t^8+1)
#        L,(si,) = impl(L,si)
#        assert si^8 == -1
#
#        R.<t> = L[]
#        s2nb = t^2 - 2^n*b
#        s2nb = s2nb.any_root()
#
#        s = n - b.valuation(2)
#        if radius is None:
#            radius = n - s/2 + 1/2
#        zeta = a/(a+b) + (s2nb*si)/((a+b)^2)
#        with observer.report("BLOWUP with center %s and radius %s!"%(zeta,radius)):
#            X_ = X.change_ring(L)
#            Y_ = X_.blowup(zeta,radius).normalization()
#            if not Y_.is_special_fiber_reduced():
#                M, to_M = Y_.make_special_fiber_reduced()
#                M, (zeta,) = impl(M, to_M(zeta))
#                try:
#                    X_ = X_.change_ring(M)
#                except:
#                    X_ = X.change_ring(M)
#                Y_ = X_.blowup(zeta,radius).normalization()
#            return Y_
#
#def obus1():
#    with observer.report("A SECOND EXAMPLE!"):
#        K.<x> = FunctionField(Qp(2,20))
#        R.<t> = K[]
#        G = t^2 - x*(x^2-1)
#        L.<y> = K.extension(G)
#        observer.log("G = %s!"%G)
#        
#        X = NormalModel(L, pAdicValuation(K.constant_base_field()))
#
#        radius = QQ(1)
#        with observer.report("BLOWUP with center zeta and radius %s!"%radius):
#            K = X.base()
#            R.<zeta> = K[]
#            Delta = Delta_f(G[0].element().numerator(), 2)
#            Delta = Delta.parent()(Delta.monic().list()[:Delta.degree()+1])
#            L.<zeta> = K.extension(Delta)
#            with observer.report("Normalizing %s"%L):
#                L,(zeta,) = impl(L,zeta)
#            X_ = X.change_ring(L)
#            radius_L = radius*L.valuation()(2)
#            if radius_L.denominator() != 1:
#                L, to_L = L.totally_ramified_extension(radius_L.denominator())
#                zeta = to_L(zeta)
#            try:
#                X_ = X.change_ring(L)
#            except:
#                X_ = X_.change_ring(L)
#            Y_ = X_.blowup(zeta,radius).normalization()
#            if not Y_.is_special_fiber_reduced():
#                M, to_M = Y_.make_special_fiber_reduced()
#                try:
#                    X_ = X_.change_ring(M)
#                except:
#                    X_ = X.change_ring(M)
#                zeta = to_M(zeta)
#                Y_ = X_.blowup(zeta,radius).normalization()
#            return Y_

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
                B = B.make_special_fiber_reduced()
            with observer.ask("Is the special fiber reduced?", True) as question:
                question.answer(B.is_special_fiber_reduced())
            with observer.report("Computing the special fiber."):
                C = B.special_fiber()
                observer.log(C)
                D = C.ambient_space().subscheme(C.defining_ideal() + C.ambient_space().subscheme(C.defining_ideal()).Jacobian())
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
            B = B.make_special_fiber_reduced()
            with observer.ask("Is the special fiber reduced?", True) as question:
                question.answer(B.is_special_fiber_reduced())
            with observer.report("Computing the special fiber."):
                C = B.special_fiber()
                observer.log(C)
                D = C.ambient_space().subscheme(C.defining_ideal() + C.ambient_space().subscheme(C.defining_ideal()).Jacobian())
                observer.log("Singularities at %s"%(D.rational_points(),))
        with observer.report("BLOWUP with center zeta and radius 1/8!"):
            R.<alpha> = L[]
            M, to_M = L.totally_ramified_extension(2)
            Mzeta = to_M(zeta)
            Y = X.change_ring(M)
            B = Y.blowup(Mzeta,1/8).normalization()
            with observer.ask("Is the special fiber reduced?", False) as question:
                question.answer(B.is_special_fiber_reduced())
            B = B.make_special_fiber_reduced()
            with observer.ask("Is the special fiber reduced?", True) as question:
                question.answer(B.is_special_fiber_reduced())
            with observer.report("Computing the special fiber."):
                C = B.special_fiber()
                observer.log(C)
                with observer.ask("Is the special fiber smooth?", True) as question:
                    question.answer(C.is_smooth())
                return B

class NormalModelComponent(object):
    def __init__(self, modelP1):
        self._modelP1 = modelP1

    @cached_method
    def valuations(self):
        return self._modelP1.valuation().mac_lane_approximants(self._G())

    def base(self):
        return self._modelP1._model.base()

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

    @cached_method
    def make_special_fiber_reduced(self):
        if not self._modelP1.is_special_fiber_reduced():
            raise ValueError
        if self.is_special_fiber_reduced():
            return self
        M, to_M = epp(self._G(), self._modelP1.valuation())
        center = to_M(self._modelP1._center)
        ouniformizer = M.uniformizer()
        M, (center,uniformizer) = impl(M,center,ouniformizer)
        observer.log("FIELD COLLAPSED: old uniformizer %s \n is now %s!"%(ouniformizer.polynomial(),uniformizer))
        radius = self._modelP1._radius
        X = self._modelP1._model.change_ring(M)
        return X.blowup(center, radius).normalization()

    def genus(self):
        if not self.is_special_fiber_reduced():
            raise ValueError()
        return [w.residue_field().genus() for w in self.valuations()]

    def analyze(self):
        with observer.report("Analyzing special fiber."):
            C = self.special_fiber()
            observer.log("special fiber is %s"%C)
            C = C.ambient_space().subscheme(C.defining_ideal())

            with observer.ask("Is the special fiber smooth?") as is_smooth:
                assert( len(C.irreducible_components()) == len(self.valuations()) )
                if len(C.irreducible_components())>1:
                    is_smooth.answer("it is not irreducible.")
                else:
                    if is_smooth.answer(C.irreducible_components()[0].is_smooth()):
                        return

            observer.log("the variables on the special fiber are reductions of (starting with x,z0,...):\n %s"%self.gens())

            with observer.report("Computing singularities."):
                J = C.Jacobian()
                D = AffineSpace(C.defining_ideal().ring()).subscheme(J)
                singularities = rational_points(D)
                if not singularities:
                    observer.log("The base field is too small to see the singularities.")
                    raise SingularitiesNotRational

            observer.log("singularities are at %s"%singularities)

            for CC in C.irreducible_components():
                with observer.report("Invariants of singularities on %s"%C):
                    with observer.ask("Is this component smooth?") as is_smooth:
                        if is_smooth.answer(CC.is_smooth()): continue
                    for singularity in rational_points(AffineSpace(C.defining_ideal().ring()).subscheme(CC.Jacobian())):
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


class NormalModelP1Component(object):
    def __init__(self, model, center, radius):
        self._model = model
        self._center = center
        self._radius = radius

    def is_special_fiber_reduced(self):
        return self.valuation().value_group() == 1

    @cached_method
    def normalization(self):
        return NormalModelComponent(self)

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
    def __init__(self, L, vp, construction=None):
        self._G = L.polynomial()
        if vp.domain() != self._G.base_ring().constant_base_field():
            raise ValueError
        self._vp = vp
        self._variable_P1 = self._G.base_ring().variable_name()
        self._construction = construction

    def base(self):
        return self._G.base_ring().constant_base_field()

    def _rational_function_field(self):
        return FunctionField(self.base(), names=self._variable_P1)

    def p(self):
        return self._vp.residue_field().characteristic()

    def change_ring(self, K, vp=None):
        if vp is None:
            try:
                vp = self._vp.extension(K)
            except ValueError:
                if self._construction:
                    return self._construction.change_ring(K)
                else:
                    raise
        if vp.domain() != K:
            raise ValueError
        Kx = FunctionField(K, names= self._variable_P1)
        G = self._G.change_ring(Kx)
        return NormalModel(self._rational_function_field().extension(G), vp, self)

    def blowup(self, center, radius):
        if center not in self._rational_function_field():
            raise ValueError
        if radius < 0:
            raise ValueError
        return NormalModelP1Component(self, center, radius)

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

def normalization_pre_gauss(L, vK, assume_smooth=False):
    K = vK.domain()
    Kx = L.base()
    assert Kx.base() is Kx
    G = L.polynomial()
    R = Kx.maximal_order()._ring
    v0 = GaussValuation(R, vK)
    vx = RationalFunctionFieldValuation(Kx,v0)
    W = vx.mac_lane_approximants(G)

    S.<x,t> = vK.domain()[]
    if not all([c.denominator().is_one() for c in G.coefficients()]):
        raise ValueError

    with observer.report("Computing good initial generators of the normalization."):
        global B,B_
        B=[]
        gens = []
        good_gens = []
        for w in W:
            bw = w._base_valuation if w._mu is infinity else w
            k = w.residue_field()
            if not hasattr(k,'simple_model'):
                continue
            other,other_to_self,self_to_other = w.residue_field().simple_model()
            assert other_to_self(other.base().gen()) == k.rational_function_field().gen()
            gen = other_to_self(other.gen()).element()
            Gen = gen.map_coefficients(lambda c:bw.lift(bw.residue_ring()(c))(L.gen()), L)(bw.lift(bw.residue_ring().gen())(L.gen()))
            gens.append(Gen)
            assert w(Gen.element())==0
            if all([ww(Gen.element())>=0 for ww in W]):
                good_gens.append(Gen)
                #observer.log("found one: %s"%Gen)
                #GG = Gen.charpoly('T').map_coefficients(lambda c:c.map_coefficients(lambda d:d.lift_to_precision()))
                #print GG
                #assert GG.is_squarefree()
                #print "ok"
                #ret,gens = normalization_gauss(Kx.extension(GG,names='q'), vK, assume_smooth=assume_smooth)
                #return ret,[gens[0],Gen]
        return normalization_gauss(L, vK, gens=(gens if gens else None), assume_smooth=assume_smooth)

# compute the normalization of the component (minus one point) corresponding to the Gauss valuation in L
# the missing point is x=infinity
def normalization_gauss(L, vK, assume_smooth=False, gens=None):
    K = vK.domain()
    k = vK.residue_field()
    Kx = L.base()
    G = L.polynomial()
    R = Kx.maximal_order()._ring
    v0 = GaussValuation(R, vK)
    vx = RationalFunctionFieldValuation(Kx,GaussValuation(R, vK))
    S = R.change_ring(Kx)
    w0 = GaussValuation(S, vx)

    if not all([c.denominator().is_one() for c in G.coefficients()]):
        raise ValueError

    if gens is None:
        gens = [Kx.gen(), L.gen()]
    else:
        gens = [Kx.gen()] + gens
    rels = [None]*len(gens)
    extra = []

    with observer.report("Computing generators of the normalization."):
        while True:
            with observer.ask("Does gens=%s generate the normalization?"%(gens,)) as generates:
                names = ['z%s'%i for i in range(len(gens))]
                R_ = PolynomialRing(vK.residue_field(), names)
                for i,gen in enumerate(gens):
                    if rels[i] is None:
                        if i==0:
                            rels[i] = R_.zero()
                            continue
                        with observer.report("Determining equation for %s in reduction."%gen):
                            charpoly = gen.charpoly(L.variable_name())
                            charpoly.map_coefficients(lambda c:c.element().reduce())
                            charpoly = charpoly.map_coefficients(lambda c:c.map_coefficients(lambda d:d.lift_to_precision()))
                            assert w0(charpoly) == 0
                            coeffs = charpoly.coeffs()
                            coeffs = [vx.domain().zero() if vx(c)>0 else c for c in coeffs]
                            coeffs = [c.map_coefficients(vK.reduce, k) for c in coeffs]
                            assert all([c.denominator().is_one() for c in coeffs])
                            coeffs = [c.numerator() for c in coeffs]
                            R0.<a> = k[]
                            coeffs = [c(a) for c in coeffs]
                            R1.<b> = R0[]
                            rel = R1(coeffs)
                            R01.<a,b> = k[]
                            rel = R01(rel)
                            rels[i] = rel(R_.gen(0), R_.gen(i))
                I = R_.ideal(rels[1:]+extra)
                print I
                J = I.radical()
                print J
                for i,g in enumerate(J.gens()):
                    if g not in I:
                        observer.log("%s is only in the radical."%g)
                        generates.answer(False)
                        z = g.map_coefficients(lambda c:vK.lift(c), K)(gens[:len(names)])
                        w = z
                        if use_norm:
                            w = w/vK.uniformizer()^(vx(w.norm())//w.parent().degree())
                        else:
                            w = w/vK.uniformizer()
                        w = w.parent()(w.element().map_coefficients(lambda c: c.map_coefficients(lambda d:d.lift_to_precision())))
                        assert w != z
                        assert vx(w.norm()) >= 0
                        observer.log("%s is another generator"%w)
                        if w not in gens:
                            gens.append(w)
                            rels.append(None)
                        extra.append(g)
                if all(rels[1:]):
                    generates.answer(True)
                    return J, gens

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
    pi = vK.domain()(v1.element_with_valuation(v1(v1.phi())))
    # y = (x+delta)/pi
    # → x = y*pi-delta
    G = L.polynomial()
    if not all([c==0 or i in [G.degree(),0] for i,c in enumerate(G.coeffs())]):
        raise NotImplementedError
    to_ = Kx.hom([Kx.gen()*pi-delta])
    H = G.map_coefficients(to_)
    observer.log("shifted defining polynomial is %s"%H)
    assert all([c==0 or i in [G.degree(),0] for i,c in enumerate(G.coeffs())])

    LH = Kx.extension(H)
    J,gens = normalization_gauss(LH, vK, assume_smooth)
    # substitute back
    from_ = Kx.hom([(Kx.gen()+delta)/pi])
    #gens = [g.element().map_coefficients(from_) for g in gens]
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

def ppprint(f, variables=['t','x'], delimiters = [','], substitutions=[('pi','π'),('zeta_2','ζ₂'),('zeta','ζ')]):
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
def epp(G, vx):
    with observer.report("EPP for %s!"%G):
        if not G.parent().base() is vx.domain():
            raise ValueError

        R = G.parent()
        K = R.base().constant_base_field()
        Kx = R.base()
        t = G.parent().gen()
        p = vx.residue_field().characteristic()
        M = G.degree()
        v0 = GaussValuation(R,vx)

        W = vx.mac_lane_approximants(G)
        if len(W) > 1:
            raise NotImplementedError
        E = lcm([w.value_group().denominator().gen(0) for w in W])
        print "E=",E
        if not p.divides(E):
            observer.log("CHEAP CASE!")
            return K.totally_ramified_extension(E)
        if not M.divides(E):
            observer.log("DEGREE DOES NOT DIVIDE THE RAMIFICATION INDEX - THE REDUCTION CASE!")
            if W[0](t) != 0:
                observer.log("the generator of the field extension does not generate the residue field.")
                L.<Pi> = Kx.extension(G)
                w = W[0]
                gen = w.lift(w.residue_ring()(w.residue_field().gen()))(Pi)
                H = gen.minpoly()
                #print "H=%s"%H
                return epp(H, vx)
            w = W[0]
            PSI = w.phi()
            wPSI = v0.extension(PSI,infinity)
            KPSI.<s> = Kx.extension(PSI)
            observer.log("considering intermediate field %s"%KPSI)
            wPSI = FunctionFieldPolymodValuation(KPSI, wPSI)
            S.<T> = KPSI[]
            GPSI = S([c(s) for c in w.coefficients(G)])
            return epp(GPSI,wPSI)
        if W[0].phi().degree() != 1:
            print "replace generator to make minpoly totally ramified"
            w=W[0]
            print "Generating extension"
            L.<z> = Kx.extension(G)
            print "generator"
            gen = w.phi()(z)
            print "char/minpoly"
            poly = gen.charpoly('T')
            return epp(poly, vx)

        f0 = -G[0]

        if vx(f0) != 0:
            print f0
            observer.log("valuation of constant is nonzero - restarting with a differen generator")
            return epp(G(G.parent().gen()+1),vx)

        if not vx.reduce(f0).is_nth_power(p):
            raise ValueError("no ramification here")
        if not vx.reduce(f0).is_nth_power(M):
            raise NotImplementedError

        h = vx.lift(vx.reduce(f0).nth_root(M))
        v1 = v0.extension(t-h, infinity)

        def nred(g=None):
            if g is None: g = g0()
            if g.parent() is R:
                assert g.degree() <= 0
                g = g[0]
            return vx.reduce(vx.shift(g,-vx(g)))

        def is_a():
            for i in range(1,M):
                if vx(g0()) >= M/(M-i)*vx(gi(i)):
                    return True
            return False

        def is_b(g=None):
            if g is None: g = g0()
            if not nred(g).is_nth_power(p):
                return True
            if not nred(g).is_nth_power(M):
                raise NotImplementedError

        def is_633(g=None):
            if g is None: g = g0()
            return is_a() or is_b(g) or (vx(g)/M not in ZZ)

        def gi(i):
            return list(v1.coefficients(G))[i]

        def g0():
            return v1.coefficients(G).next()[0]

        def h():
            return -v1.phi()[0]

        # LEMMA 6.33
        while not is_633():
            alpha = vx.lift(nred().nth_root(M))
            s = vx(g0())
            assert M.divides(s)
            v1 = v1._base_valuation.extension(v1.phi()+vx.shift(alpha,s//M),infinity)
        if is_a():
            raise ValueError("any totally ramified extension works")
        if is_b():
            observer.log("THE REDUCTION IS NOT AN M-TH POWER ANY TR EXTENSION WILL DO!")
            return K.totally_ramified_extension(M)
        assert vx(g0())/M not in ZZ
        if vx(g0())/p in ZZ:
            raise NotImplementedError

        observer.log("checking whether the conditions of the proposition are satisfied.")
        vf = [vx(c) for c in list(G)]
        print vf
        if vx(g0())/M in ZZ:
            print "v(g0)=",vx(g0())
            print "leo failed."
        if vx(g0())/p in ZZ:
            print "extra condition failed."
        if min(vf[1:-1]) < min([v for i,v in enumerate(vf) if not p.divides(i)]):
            print "cancer failed."
        for j in range(1,M):
            vff = [vx(binomial(i,j))+vf[i] for i in range(j,M+1)]
            mins = [v for v in vff if v==min(vff)]
            if len(mins)!=1:
                print "gemini failed for j=%s"%j
                print vff
                break

        if nred().is_constant():
            observer.log("THE HARD CASE - THE REDUCTION IS A CONSTANT!")
            vx_,v0_,v1_,G_ = vx,v0,v1,G

            vK = vx
            while vK.domain() is not K:
                vK = vK._base_valuation.constant_valuation()
            S.<Phi> = K[]
            polymod = False
            if str(nred().parent()) in ["Function field in u1 defined by x^2 + x + x", "Function field in u1 defined by x^2 + x"]:
                polymod = True
                F = Phi^M + vK.shift(vK.lift(nred().element()[0].numerator()[0]), vx(g0()))
            else:
                F = Phi^M + vK.shift(vK.lift(nred().element().numerator()[0]), vx(g0()))

            keep = False
            while True:
                if not keep:
                    L.<phi> = K.extension(F)
                    observer.log("NOW TRYING THE EXTENSION DEFINED BY %s!"%F)
                    if polymod:
                        KPSI = Kx
                        KX = KPSI.base()
                        wpsi = vx._base_valuation
                        vX1 = wpsi._base_valuation._base_valuation._base_valuation
                        Lx_ = PolynomialRing(L,names=KX.variable_names())
                        wx0 = GaussValuation(Lx_)
                        wx1 = wx0.extension(vX1.phi().change_ring(L), vX1._mu*M)
                        Lx = FunctionField(L,names=KX.variable_names())
                        wx = RationalFunctionFieldValuation(Lx, wx1)
                        
                        Lx_ = PolynomialRing(Lx, names=KPSI.variable_names())
                        wx0 = GaussValuation(Lx_,wx)
                        wx1 = wx0.extension(KPSI.polynomial().change_ring(Lx).change_variable_name(Lx_.variable_name()), infinity)
                        Lx = Lx.extension(wx1.phi(), names=KPSI.variable_names())
                        wx = FunctionFieldPolymodValuation(Lx, wx1)
                        
                    else:
                        vx1 = vx._base_valuation
                        Lx_ = PolynomialRing(L,names=Kx.variable_names())
                        wx0 = GaussValuation(Lx_)
                        wx1 = wx0.extension(vx1.phi().change_ring(L), vx1._mu*M)
                        Lx = FunctionField(L,names=Kx.variable_names())
                        wx = RationalFunctionFieldValuation(Lx,wx1)

                    if polymod:
                        if not all([c.denominator().is_one() for c in h().element().coeffs()]):
                            raise NotImplementedError
                    else:
                        if not h().denominator().is_one():
                            raise NotImplementedError
                    delta = Lx.zero()
                keep = False
                if polymod:
                    hh = Lx(h().element().map_coefficients(Lx.base(),Lx.base())) + phi + delta
                else:
                    hh = Lx(h().numerator().map_coefficients(L,L)) + phi + delta

                wR = R.change_ring(Lx)
                w0 = GaussValuation(wR, wx)
                w1 = w0.extension(wR.gen() - hh, infinity)
                wG = G.change_ring(Lx)

                vx,v0,v1,G = wx,w0,w1,wG
                try:
                    vg0 = ZZ(vx(g0()))
                    bi = nred()
                    observer.log("The reduction of b_i is %s, the vaulation of b_i is %s"%(bi,vg0))
                    if is_a():
                        observer.log("THE HARD CASE - THE NEWTON POLYGON NOW TOUCHES!")
                        return L, K.hom(L)
                    if is_b():
                        observer.log("THE HARD CASE - THE REDUCTION IS NOW NOT AN M-TH POWER ANYMORE!")
                        return L, K.hom(L)
                    i = vg0%M
                    if i == 0:
                        delta += L.uniformizer()^(vg0//M)*wx.lift(bi.nth_root(M))
                        observer.log("modifying delta")
                        keep = True
                        continue
                    else:
                        if not bi.is_constant():
                            break
                        else:
                            bi = g0()/(phi**i)
                            r = wx(bi)/M
                            assert r in ZZ
                            r = ZZ(r)
                            beta0 = wx.reduce(bi/K.uniformizer()**r)
                            assert beta0.is_constant()
                            if polymod:
                                beta0 = beta0.element()[0].numerator()[0]
                            else:
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




def solve_b(F,i):

    b=F.parent().gen(i)
    return -F.constant_coefficient()/F.monomial_coefficient(b)


def Delta_univ(n,p):

    r=floor(n/p)
    s=floor(log(n)/log(p))

    R=PolynomialRing(ZZ,'a',n+1)
    K=R.fraction_field()

    S1=PolynomialRing(K,'b',r+1)
    S2.<x>=S1[]

    F=S2([R.gen(i) for i in [0..n]])

    H=S2([1]+[S1.gen(i) for i in [1..r]])

    G=F-F[0]*H^p

    GL=[G[k] for k in [0..n]]

    for k in [1..r]:
        b=solve_b(GL[k],k)
        for i in [k..p^s]:
            GL[i]=GL[i].subs({S1.gen(k):b})
    
    return GL[p^s].constant_coefficient().numerator()


def Delta_f(f,p):

    K=f.parent().base_ring()
    x=f.parent().gen()
    n=f.degree()

    Delta=Delta_univ(n,p)
    a=Delta.parent().gens()
    Delta=Delta.change_ring(f.parent())

    fd=f
    F=[]
    for i in [0..n]:
        F.append(fd)
        fd=fd.derivative(x)/(i+1)
    Delta=Delta(F)
    return Delta




def pol_red(f,p):

     m=min([f[i].valuation(p) for i in [0..f.degree()]])
     f=f/p^m
     return f.change_ring(GF(p))



def h_g_decomposition(f,p):

# f: ein Polynom über einem Körper K vom Grad n
# p: eine Primzahl
# Bedingung: f=a0+a1*x+.., mit a0<>0

# Ausgabe: Polynome h,g, so dass
#    (a)  f=a_0*(h^p+g)
#    (b)  r:=deg(h)<=n/p
#    (c)  x^(r+1)|g

    R=f.parent()
    K=R.base_ring()
    x=R.gen()
    n=f.degree()
    r=floor(n/p)
    a0=f[0]
    assert a0.is_unit()

    h=R(1)
    f=f/a0
    g=f-1
    for k in [1..r]:
        h=h+g[k]/p*x^k
        g=f-h^p
    return h,g


        
        

def liu10438():
    with observer.report("LIU 10.4.38"):
        K.<x> = FunctionField(Qp(2,20))
        R.<t> = K[]
        G = t^2 - x^8 + 5*x^6 - 10*x^4 + 10*x^2 - 5
        L.<y> = K.extension(G)
        observer.log("EXAMPLE: G = %s"%G)

        X = NormalModel(L, pAdicValuation(K.constant_base_field()))

        radius = QQ(0)
        with observer.report("BLOWUP with center zeta and radius %s!"%radius):
            K = X.base()
            R.<zeta> = K[]
            # D = (51200) * (x - 1) * (x + 1) * (x^10 - 5*x^8 + 10*x^6 - 10*x^4 + 5*x^2 - 5) * (x^38 - 225/8*x^36 + 1365/4*x^34 - 19365/8*x^32 + 11215*x^30 - 139745/4*x^28 + 67815*x^26 - 155475/4*x^24 - 244900*x^22 + 8323675/8*x^20 - 9543425/4*x^18 + 30232475/8*x^16 - 4334375*x^14 + 3570750*x^12 - 2004625*x^10 + 660125*x^8 - 52500*x^6 - 45000*x^4 + 15000*x^2 - 1250)
            Delta = zeta^10 - 5*zeta^8 + 10*zeta^6 - 10*zeta^4 + 5*zeta^2 - 5
            L.<zeta> = K.extension(Delta)
            with observer.report("Normalizing %s"%L):
                L,(zeta,) = impl(L,zeta)
            X_ = X.change_ring(L)
            radius_L = radius*L.valuation()(2)
            if radius_L.denominator() != 1:
                L, to_L = L.totally_ramified_extension(radius_L.denominator())
                zeta = to_L(zeta)
            try:
                X_ = X.change_ring(L)
            except:
                X_ = X_.change_ring(L)
            Y_ = X_.blowup(zeta,radius).normalization()
            if not Y_.is_special_fiber_reduced():
                M, to_M = Y_.make_special_fiber_reduced()
                try:
                    X_ = X_.change_ring(M)
                except:
                    X_ = X.change_ring(M)
                zeta = to_M(zeta)
                Y_ = X_.blowup(zeta,radius).normalization()
            return Y_

