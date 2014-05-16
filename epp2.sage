from sage.rings.padics.padic_valuation import pAdicValuation
from sage.rings.padics.gauss_valuation import GaussValuation
from sage.rings.padics.function_field_valuation import RationalFunctionFieldValuation

G = load("hard_ramified_polynomial.sobj")

R.<a> = QQ[]
L.<a> = QQ.extension(a^3 - 3)
vL = pAdicValuation(L, a)
R.<x> = L[]
vLx = GaussValuation(R, vL)

L.<x> = FunctionField(L)
vLx = RationalFunctionFieldValuation(L, vLx)

R.<t> = L[]
x = R(x)
w=  vLx.mac_lane_approximants(G(t,x))[0]
