from sage.rings.padics.padic_valuation import pAdicValuation
from sage.rings.padics.gauss_valuation import GaussValuation
from sage.rings.padics.function_field_valuation import RationalFunctionFieldValuation

def generate_example():
    d = 1

#R.<t,x> = ZZ[]
#f = R.random_element(degree=d-1)
#D = f.dict()
#D = { e:3*c for (e,c) in D.items() }
#D[(d,0)]=1
#f = R(D)

    R.<x> = QQ[]
    vK = pAdicValuation(QQ, 3)
    vKx = GaussValuation(R, vK)

    K.<x> = FunctionField(QQ)
    vKx = RationalFunctionFieldValuation(K, vKx)

    R.<t> = K[]
#x = R(x)
#if f(t,x) in K:
#    continue
#if not f(t,x).leading_coefficient() == 1:
#    assert False
#if f.degree() != d:
#    assert False
#print "Trying f=%s"%f
    v0 = GaussValuation(R, vKx)
#lambda_1 = vKx(f(t,x)[0])/3
    lambda_1 = 1/3
#if lambda_1 == infinity:
#    print " oo"
#    continue
#if lambda_1.denominator() == 1:
#    print " (not ramified)"
#    continue
    v1 = v0.extension(t, lambda_1)
#if not v1.is_key(f(t,x)):
#    print " (not a key)"
#    continue
# v2 = v1.extension(f(t,x), )
# v3 = v2.extension(t^6 - 6*x*t^3 + 9*x^2 + 162*x, 100)

    def random_key(v, d):
        #print "Looking for random key of degree %s over %s"%(d,v)
        while True:
            R.<t,x> = v.residue_field().constant_base_field()[]
            f = R.random_element(degree=3*d)
            D = { (a,b):c for (a,b),c in f.dict().items() if a < d }
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
            if f.degree() == 1:
                continue
            break

        return f
#    R.<t,x> = ZZ[]
#    ret = eval(str(f).replace('^','**'))
#    return f,ret
#
    f1 = random_key(v1, 1)
    v2 = v1.extension(f1, v1(f1)+1)
    f2 = random_key(v2, 3)
    print "Trying with %s"%vKx.mac_lane_approximants(f2)

    R.<t,x> = ZZ[]
    G = eval(str(f2).replace('^','**'))
    return G

def epp(G, L, uniformizer):
    vL = pAdicValuation(L, uniformizer)
    R.<x> = L[]
    vLx = GaussValuation(R, vL)

    L.<x> = FunctionField(L)
    vLx = RationalFunctionFieldValuation(L, vLx)

    R.<t> = L[]
    x = R(x)
    print vLx
    return vLx.mac_lane_approximants(G(t,x))

# e.g.
# G = load("hard_ramified_polynomial")
# R.<a> = QQ[]
# L.<a> = QQ.extension(a^3-3)
# epp(G, L, a)
