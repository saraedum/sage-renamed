"""
sage: R.<t> = QQ[]
sage: G = (t^3-3)*(t^3-3-3^10)*(t^6-18)*(t^2+9)*(t^2+3)
sage: p = 3
sage: C=Configuration(G,pAdicValuation(QQ,p))
sage: title="Configuration of Roots, $v(%s)=%s$"%(p,C._denominator())
sage: C.plot().save('/tmp/plot.svg',axes=False,aspect_ratio=1,title=title)
sage: C.plot_tree().save('/tmp/tree.svg',aspect_ratio=1,title=title)

sage: %runfile epp.sage
sage: p = 3
sage: K,R,vx = SmartRationalFunctionFieldValuation(QQ,p)
sage: K.inject_variables()
sage: R.inject_variables()
sage: G=t^3-1-3*x^3-3*x^5
sage: C = Configuration(G,vx)
sage: title="Configuration of Roots, $v(%s)=%s$"%(p,C._denominator())
sage: C.plot().save('/tmp/plot.svg',axes=False,aspect_ratio=1,title=title)
sage: C.plot_tree().save('/tmp/tree.svg',aspect_ratio=1,title=title)
"""

class Configuration(object):
    def __init__(self, G, vp=None):
        self._G = G
        if not isinstance(self._ring(), sage.rings.polynomial.polynomial_ring.PolynomialRing_commutative):
            raise ValueError("G must be a polynomial or a list of polynomials.")
        self._vp = vp
        if not self._valuation().domain() is self._field():
            raise ValueError("vp must be a valuation on %s"%self._field())

    def __repr__(self):
        return "Configuration(%r,%r)"%(self._G,self._valuation())

    @cached_method
    def _approximate_factors(self):
        if hasattr(self._G, 'parent'):
            v = self._valuation()
            V = v.mac_lane_approximants(self._G)
            print "initial approximants for %s are %s"%(self._G,V)
            for i,w in enumerate(V):
                while w.phi().degree() < w.E()*w.F() or (len(V)>1 and not Configuration(w.phi(),self._valuation())._splits(w._mu)):
                    w = w.mac_lane_step(self._G)
                    assert len(w) == 1
                    w = w[0]
                    V[i] = w
            print "final approximants for %s are %s"%(self._G,V)
            return Sequence(v.phi() for v in V)
        else:
            return Sequence(self._G)

    def _splits(self, mu):
        if self._G.degree() == 1:
            return True
        if len(self._approximate_factors()) != 1:
            raise NotImplementedError

        distances = self._distances()[0][0]
        return mu > max([d for d in distances.keys() if d is not Infinity]) + sum([distances[d]*d for d in distances if d is not Infinity])

    @cached_method
    def _ring(self):
        if hasattr(self._G, 'parent'):
            return self._G.parent()
        else:
            return Sequence(self._G).universe()

    @cached_method
    def _field(self):
        return self._ring().base()

    @cached_method
    def _valuation(self, L=None):
        if L is None:
            if self._vp is None:
                return pAdicValuation(self._field())
            else:
                return self._vp
        else:
            return self._valuation().extension(L)

    @cached_method
    def _distances(self):
        return [[self._distance(g,h) for h in self._approximate_factors()] for g in self._approximate_factors()]

    def _distance(self, g, h):
        K.<a> = self._field().extension(g)

        v = self._valuation()
        w = self._valuation(K)
        e = 1/w(v.uniformizer())

        g = g.change_ring(K)
        w0 = GaussValuation(g.parent(),w)
        np = w0.newton_polygon(h(g.parent().gen()+a))
        sides = np.sides()
        slopes = np.slopes()
        d = {}
        for slope,side in zip(slopes,sides):
            d[-slope*e] = side[1][0]-side[0][0]
        return d

    class Disk(object):
        def __init__(self, tree, radius, children):
            self._tree = tree
            self._radius = radius
            self._children = children
        def __repr__(self):
            if self._radius is Infinity:
                #return str(self._children[0])
                return ""
            else:
                return "$"+latex(self._radius*self._tree._denominator())+"$"

    def _tree(self, roots, distances):
        if distances == [Infinity]:
            I = roots.nonzero_positions()
            assert len(I)==1
            return Configuration.Disk(self,Infinity,I)

        d = distances[0]
        distances = distances[1:]

        children = []
        for r in range(len(roots)):
            if not roots[r]:
                continue
            m = roots[r] / self._matrix(d)[r,r]
            assert m
            for i in range(m):
                children.append(self._matrix(d[0]).row(r))
                roots -= children[-1]

        assert all(r==0 for r in roots)
        return Configuration.Disk(self,d,[self._tree(c,distances) for c in children])

    @cached_method
    def _matrix(self, d):
        D = self._distances()
        G = self._approximate_factors()
        M = copy(matrix(len(G)))
        for i in range(len(G)):
            for j in range(len(G)):
                for dij in D[i][j]:
                    if dij > d:
                        M[i,j]+=D[i][j][dij]
        return M

    def _contract(self, tree):
        if not isinstance(tree, Configuration.Disk):
            return tree
        if tree._radius is Infinity:
            return tree
        if len(tree._children)==1:
            return self._contract(tree._children[0])
        return Configuration.Disk(self,tree._radius, [self._contract(c) for c in tree._children])

    def _digraph(self, root, adjacency=None):
        if adjacency is None:
            adjacency = {}
        if not isinstance(root, Configuration.Disk):
            return adjacency
        if root._radius is Infinity:
            return adjacency
        adjacency[root] = tuple(root._children)
        for child in root._children:
            self._digraph(child, adjacency)
        return adjacency

    @cached_method
    def _data(self):
        from itertools import chain
        distances = uniq(chain.from_iterable([d2.keys() for d1 in self._distances() for d2 in d1]))
        tree = self._tree(vector(g.degree() for g in self._approximate_factors()), distances)
        return self._contract(tree)

    def tree(self):
        return DiGraph(self._digraph(self._data()))

    def _vertices(self, d, tree):
        if tree._radius > d:
            return []
        if tree._radius == d:
            return [tree]
        else:
            from itertools import chain
            return chain.from_iterable([self._vertices(d,c) for c in tree._children])

    def _packing_radius(self, radii):
        if len(radii)==2:
            return sum(radii)
        r_max = max(radii)
        if len(radii)==3:
            return r_max*2.154
        u = 2*r_max*len(radii)
        r = u/(2*pi)
        return r+r_max

    def _radius(self, d, tree, radius, delta):
        vertices = self._vertices(d, tree) 
        return max(max(radius.values())*delta,max(self._packing_radius([radius[c._radius] for c in v._children])*delta for v in vertices))

    def _plot(self, graphics, center, tree, radius, denominator):
        r = radius[tree._radius]
        if tree._radius is Infinity:
            graphics += circle(center, r, fill=True, rgbcolor=sage.plot.colors.rainbow(len(self._approximate_factors()))[tree._children[0]], alpha=.8, thickness=0)
        else:
            if len(tree._children) > 2 or all(c._radius == Infinity for c in tree._children):
                text_pos = center
            else:
                text_pos = (center[0], center[1]+r/2)
            fontsize = r*100
            graphics += text("$"+latex(tree._radius*denominator)+"$", text_pos, fontsize=fontsize, rgbcolor=(0,0,0))
            graphics += circle(center, r, rgbcolor=(0,0,0))
            delta = 2*pi/len(tree._children)
            for i,c in enumerate(tree._children):
                graphics = self._plot(graphics, (center[0]+(r-radius[c._radius])*cos(delta*i), center[1]+(r-radius[c._radius])*sin(delta*i)), c, radius, denominator)
        return graphics

    def _denominator(self):
        from itertools import chain
        distances = uniq(chain.from_iterable([d2.keys() for d1 in self._distances() for d2 in d1]))
        return lcm([d.denominator() for d in distances if d is not Infinity])

    def plot(self, infinite_radius = 1, delta=1.05):
        tree = self._data()
        radius = {Infinity : infinite_radius}
        from itertools import chain
        distances = uniq(chain.from_iterable([d2.keys() for d1 in self._distances() for d2 in d1]))
        denominator = self._denominator()
        for d in reversed(distances[:-1]):
            radius[d] = self._radius(d, tree, radius, delta)
        radius = {d:radius[d]/max(radius.values()) for d in distances}
        ret = self._plot(Graphics(), (0,0), tree, radius, denominator)
        return ret

    def colorize(self, tree, colors):
        from sage.plot.colors import rgbcolor, rainbow
        if tree._radius is Infinity:
            colors[rainbow(len(self._approximate_factors()))[tree._children[0]]].append(tree)
        else:
            colors[rgbcolor((.9,.9,.9))].append(tree)
            for c in tree._children:
                self.colorize(c,colors)

    def plot_tree(self, **kwargs):
        tree = self._data()
        from itertools import chain
        from sage.plot.colors import rgbcolor, rainbow
        vertex_colors = { rgbcolor((.9,.9,.9)) : [] }
        for i in range(len(self._approximate_factors())):
            vertex_colors[sage.plot.colors.rainbow(len(self._approximate_factors()))[i]] = []
        self.colorize(tree,vertex_colors)
        return self.tree().plot(vertex_colors=vertex_colors, **kwargs)

#def config(G):
#    raise NotImplementedError("factorization to the required level")
#
#class Disk(object):
#    def __init__(self, radius):
#        self._radius = radius
#        self._children = set()
#
#    def add(self, disk):
#        assert disk.radius() >= self.radius()
#        self._children.add(disk)
#
#    def radius(self):
#        return self._radius
#
#    def count(self, i):
#        return sum([c.count(i) for c in self._children])
#
#    def __repr__(self):
#        return "D(%s:%s)"%(str(list(self._children)),self._radius)
#
#    def is_equivalent(self, other):
#        if not isinstance(other,Disk):
#            return False
#        if self.radius() != other.radius():
#            return False
#        other_children = list(other._children)
#        for c in self._children:
#            for j,cc in enumerate(other_children):
#                if c.is_equivalent(cc):
#                    other_children.pop(j)
#                    break
#        if other_children:
#            return False
#        return True
#
#class Point(object):
#    def __init__(self, i):
#        self._i = i
#    def __repr__(self):
#        return str(self._i)
#    def count(self, i):
#        return 1 if i == self._i else 0
#    def radius(self):
#        return Infinity
#    def is_equivalent(self, other):
#        if not isinstance(other, Point):
#            return False
#        return self._i == other._i
#
#class Tree(object):
#    def __init__(self, G):
#        if len(set(G)) != len(G):
#            raise NotImplementedError("G contains duplicates")
#        self._G = G
#
#    def _distances(self):
#        return [[self._distance(g,h) for h in self._G] for g in self._G]
#
#    def _distance(self, g, h):
#        vp = pAdicValuation(QQ,p)
#        K.<a> = NumberField(g)
#        I = K.ideal(p).factor()
#        assert len(I)==1, "p has coprime factors"
#        pi,e = I[0]
#        vpi = pAdicValuation(K,pi)
#        g = g.change_ring(K)
#        v0 = GaussValuation(g.parent(),vpi)
#        np = v0.newton_polygon(h(g.parent().gen()+a))
#        sides = np.sides()
#        slopes = np.slopes()
#        d = {}
#        for slope,side in zip(slopes,sides):
#            d[-slope/e] = side[1][0]-side[0][0]
#        return d
#
#    def _plan(self):
#        plan = []
#        D = self._distances()
#        G = self._G
#        ds = set()
#        for i in range(len(G)):
#            for j in range(len(G)):
#                for d in D[i][j]:
#                    ds.add(d)
#
#        ds = list(ds)
#        ds.sort()
#        for d in ds:
#            M = copy(matrix(len(G)))
#            for i in range(len(G)):
#                for j in range(len(G)):
#                    for dij in D[i][j]:
#                        if dij >= d:
#                            M[i,j]+=D[i][j][dij]
#            print ""
#            print d
#            print M
#
#    def _config(self):
#        self._nodes = []
#        G = self._G
#        for i in range(len(G)):
#            for j in range(G[i].degree()):
#                p = Point(i)
#                d = Disk(Infinity)
#                d.add(p)
#                self._nodes.append(d)
#
#        return self._plan()

#def config(p, G, H=None):
#    if H is None:
#        H = G
#    vp = pAdicValuation(QQ,p)
#    V = vp.mac_lane_approximants(G)
#    if len(V)!=1:
#        raise NotImplementedError("G is not irreducible over Qp")
#    K.<a> = NumberField(G)
#    I = K.ideal(p).factor()
#    if len(I)!=1:
#        raise NotImplementedError
#    pi,e = I[0]
#    print 1/e
#    vpi = pAdicValuation(K,pi)
#    G = G.change_ring(K)
#    v0 = GaussValuation(G.parent(),vpi)
#    np = v0.newton_polygon(H(G.parent().gen()+a))
#    if G != H:
#        return np
#    #print np
#    sides = np.sides(include_infinite=False)
#    slopes = np.slopes(include_infinite=False)
#    slopes = [-slope/e for slope in slopes]
#    N = [side[1][0]-side[0][0] for side in sides]
#    M = [N[0]+1]
#    for n in N[1:]:
#        for m in M:
#            assert m.divides(n)
#            n = n//m
#        M.append(n+1)
#    return M,slopes
#
def random_irreducible_monic_integral(p, degree):
    R.<t> = QQ[]
    vp = pAdicValuation(QQ,p)
    while True:
        G = R([ZZ.random_element() for i in range(degree)]+[1])
        try:
            V = vp.mac_lane_approximants(G)
            if len(V)>1:
                continue
        except ValueError:
            continue
        return G

#def foo(p,degree):
#    while True:
#       R.<t> = QQ[]
#       G = R([ZZ.random_element() for i in range(degree)]+[1])
#       try:
#        I,V,N = analyze(p, G)
#       except:
#        continue
#       print G
#       print I
#       print V
#       print N
#
#
#def analyze(p, G):
#    vp=pAdicValuation(QQ,p)
#    V = vp.mac_lane_approximants(G)
#    if len(V)>1:
#         raise Exception("not irreducible")
#    K.<a> = QQ.extension(G)
#    I = K.ideal(p).factor()
#    vP = pAdicValuation(K,I[0][0])
#    R.<t> = K[]
#    v0 = GaussValuation(R, vP)
#    NP = v0.newton_polygon(G(t+a))
#    if NP.slopes()[1] == 0:
#         raise Exception("boring")
#    return I,V,N
