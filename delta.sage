


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


        
        

