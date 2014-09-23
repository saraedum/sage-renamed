"""
Newton polygons

Implements Newton polygons for discrete valuations.

AUTHORS:

- Julian Rueth (15-04-2013): initial version

"""
#*****************************************************************************
#       Copyright (C) 2013 Julian Rueth <julian.rueth@fsfe.org>
#
#  Distributed under the terms of the GNU General Public License (GPL)
#  as published by the Free Software Foundation; either version 2 of
#  the License, or (at your option) any later version.
#                  http://www.gnu.org/licenses/
#*****************************************************************************

from sage.misc.cachefunc import cached_method

from sage.rings.all import infinity

from sage.structure.sage_object import SageObject

class NewtonPolygon(SageObject):
    """
    A Newton polygon given by its set of points.

    INPUT:

    - ``ordinates`` -- a list of rationals (or infinity) representing the
      ordinates at `0,1,\dots`.

    EXAMPLES::

        sage: NewtonPolygon([infinity,infinity,4,0,infinity,-8/3,-4,-4,infinity])
        Newton Polygon with vertices [(0, +Infinity), (2, 4), (3, 0), (6, -4), (7, -4), (8, +Infinity)]


    """
    def __init__(self, ordinates):
        """
        Initialization.

        TESTS::

            sage: type(NewtonPolygon(([0])))
            <class 'sage.rings.padics.newton_polygon.NewtonPolygon'>

        """
        self._points = list(enumerate(ordinates))

        if not len(self._points):
            raise ValueError("ordinates must be non-empty")
        from sage.rings.all import QQ
        if not all([o is infinity or o in QQ for a,o in self._points]):
            raise ValueError("ordinates must be rational or infinty")

    def __repr__(self):
        """
        Return a printable representation of this Newton polygon.

        EXAMPLES::

            sage: NewtonPolygon([1]) # indirect doctest
            Newton Polygon with vertices [(0, 1)]

        """
        return "Newton Polygon with vertices %s"%self.vertices()

    def __len__(self):
        """
        Return the highest abscissa in this Newton polygon

        EXAMPLES::

            sage: NP = NewtonPolygon([infinity,infinity,4,0,infinity,-8/3,-4,-4,infinity])
            sage: len(NP)
            8

        """
        return len(self._points) - 1

    def __getitem__(self, i):
        """
        Return the ordinate of the Newton polygon at ``i``.

        EXAMPLES::

            sage: NP = NewtonPolygon([infinity,infinity,4,0,infinity,-8/3,-4,-4,infinity])
            sage: NP[0]
            +Infinity
            sage: NP[4]
            -4/3
            sage: NP[0:3]
            [+Infinity, +Infinity, 4]
            sage: NP[-2]
            -4

        """
        return self.ordinates()[i]

    @cached_method
    def ordinates(self):
        """
        Return the ordinates of the Newton polygon.

        EXAMPLES::

            sage: NP = NewtonPolygon([infinity,infinity,4,0,infinity,-8/3,-4,-4,infinity])
            sage: NP.ordinates()
            [+Infinity, +Infinity, 4, 0, -4/3, -8/3, -4, -4, +Infinity]

        """
        ret = []
        for side in self.sides():
            l = side[1][0]-side[0][0]
            if side[0][1] is infinity or side[1][1] is infinity:
                ret.append(side[0][1])
                ret.extend([infinity]*(l-1))
            else:
                ret.extend([side[0][1]+i*(side[1][1]-side[0][1])/l for i in range(l)])
        ret.append(self._points[-1][1])
        assert len(ret) == len(self) + 1
        return ret

    @cached_method
    def _finite_lower_convex_hull(self):
        """
        Compute the finite part of the Newton polygon, i.e., the lower convex
        hull of the points which have finite ordinate. Implements Andrew's
        monotone chain algorithm.

        EXAMPLES::

            sage: NP = NewtonPolygon([infinity,infinity,4,0,infinity,-8/3,-4,-4,infinity]); NP
            Newton Polygon with vertices [(0, +Infinity), (2, 4), (3, 0), (6, -4), (7, -4), (8, +Infinity)]
            sage: NP._finite_lower_convex_hull()
            [(2, 4), (3, 0), (6, -4), (7, -4)]

        """
        points = self._points

        points = [p for p in points if p[1] != infinity]

        # the convex hull of two or less points is trivial
        if len(points) <= 2:
            return points

        # Andrew's monotone chain algorithm
        # the leftmost point is certainly in the convex hull
        points.reverse()
        vertices = [points[-1]]
        points.pop()

        vertices.append(points[-1])
        points.pop()

        while points:
            while len(vertices) >= 2 and (points[-1][1]-vertices[-1][1])/(points[-1][0]-vertices[-1][0]) <= (vertices[-1][1]-vertices[-2][1])/(vertices[-1][0]-vertices[-2][0]):
                vertices.pop()
            vertices.append(points[-1])
            points.pop()

        return vertices

    @cached_method
    def vertices(self, include_infinite=True):
        """
        Return the vertices of the Newton polygon.

        INPUT:

        - ``include_infinite`` -- a boolean (default: ``True``), whether to
          include the initial and final infinite part

        EXAMPLES::

            sage: NP = NewtonPolygon([infinity,infinity,4,0,infinity,-8/3,-4,-4,infinity])
            sage: NP.vertices()
            [(0, +Infinity), (2, 4), (3, 0), (6, -4), (7, -4), (8, +Infinity)]
            sage: NP.vertices(include_infinite=False)
            [(2, 4), (3, 0), (6, -4), (7, -4)]

        TESTS::

            sage: NP = NewtonPolygon([infinity])
            sage: NP.vertices()
            [(0, +Infinity)]
            sage: NP.vertices(include_infinite=False)
            []

            sage: NP = NewtonPolygon([infinity,infinity])
            sage: NP.vertices()
            [(0, +Infinity), (1, +Infinity)]
            sage: NP.vertices(include_infinite=False)
            []

        """
        vertices = self._finite_lower_convex_hull()
        if len(vertices):
            finite_part = [vertices[0]]
            for v in vertices:
                if v[0] > finite_part[-1][0]:
                    finite_part.append(v)
        else:
            finite_part = []

        if not include_infinite:
            return finite_part

        infinite_intro = [] if finite_part and finite_part[0][0]==0 else [(0,infinity)]
        infinite_outro = [] if finite_part and finite_part[-1][0]==self._points[-1][0] else [(self._points[-1][0],infinity)]
        if finite_part:
            return infinite_intro + finite_part + infinite_outro
        elif len(self) == 0:
            return infinite_intro
        else:
            return infinite_intro + infinite_outro

    @cached_method
    def principal_part(self):
        """
        Return the principal part of this Newton polygon, i.e., the initial
        part which contains the sides of the negative slopes.

        OUTPUT:

        a Newton polygon, possibly shorter than this one

        EXAMPLES::

            sage: NP = NewtonPolygon([infinity,infinity,4,0,infinity,-8/3,-4,-4,infinity])
            sage: NP.principal_part()
            Newton Polygon with vertices [(0, +Infinity), (2, 4), (3, 0), (6, -4)]
            sage: NP = NewtonPolygon([0,1,2])
            sage: NP.principal_part()
            Newton Polygon with vertices [(0, 0)]

        TESTS::

            sage: NP = NewtonPolygon([infinity])
            sage: NP.principal_part()
            Newton Polygon with vertices [(0, +Infinity)]

            sage: NP = NewtonPolygon([infinity,infinity])
            sage: NP.principal_part()
            Newton Polygon with vertices [(0, +Infinity)]

        """
        vertices = self.vertices()
        principal_vertices = [vertices[0]]
        for v in vertices[1:]:
            if v[1] >= principal_vertices[-1][1]:
                break
            principal_vertices.append(v)
        return NewtonPolygon([o for a,o in self._points[:principal_vertices[-1][0]+1]])

    @cached_method
    def sides(self, include_infinite=True):
        """
        Return the sides of this Newton polygon as pairs of vertices.

        INPUT:

        - ``include_infinte`` -- a boolean (default: ``True``), whether to
          include sides containing an infinite coordinate

        EXAMPLES::

            sage: NP = NewtonPolygon([infinity,infinity,4,0,infinity,-8/3,-4,-4,infinity])
            sage: NP.sides()
            [((0, +Infinity), (2, 4)), ((2, 4), (3, 0)), ((3, 0), (6, -4)), ((6, -4), (7, -4)), ((7, -4), (8, +Infinity))]
            sage: NP = NewtonPolygon([0,1,2])
            sage: NP.sides()
            [((0, 0), (2, 2))]

        TESTS::

            sage: NP = NewtonPolygon([infinity])
            sage: NP.sides()
            []

            sage: NP = NewtonPolygon([infinity,infinity])
            sage: NP.sides()
            [((0, +Infinity), (1, +Infinity))]
            sage: NP.sides(include_infinite=False)
            []

        """
        vertices = self.vertices(include_infinite)
        return [ (vertices[i-1],vertices[i]) for i in range(1,len(vertices)) ]

    @cached_method
    def slopes(self, include_infinite=True):
        """
        Return the slopes of the :meth:`sides` of this Newton polygon.

        INPUT:

        - ``include_infinte`` -- a boolean (default: ``True``), whether to
          include sides containing an infinite coordinate

        EXAMPLES::

            sage: NP = NewtonPolygon([infinity,infinity,4,0,infinity,-8/3,-4,-4,infinity])
            sage: NP.slopes()
            [-Infinity, -4, -4/3, 0, +Infinity]
            sage: NP = NewtonPolygon([0,1,2])
            sage: NP.slopes()
            [1]

        TESTS::

            sage: NP = NewtonPolygon([infinity])
            sage: NP.slopes()
            []

            sage: NP = NewtonPolygon([infinity,infinity])
            sage: NP.slopes()
            Traceback (most recent call last):
            ...
            NotImplementedError: slope not defined between points with ordinate +Infinity
            sage: NP.slopes(include_infinite=False)
            []

        """
        from sage.rings.all import QQ
        ret = []
        for s in self.sides(include_infinite):
            if s[0][1] is infinity and s[1][1] is infinity:
                raise NotImplementedError("slope not defined between points with ordinate +Infinity")
            if s[0][1] is infinity:
                ret.append(-infinity)
            elif s[1][1] is infinity:
                ret.append(infinity)
            else:
                ret.append((s[1][1]-s[0][1])/(s[1][0]-s[0][0]))
        return ret

    def __eq__(self, other):
        if not isinstance(other, NewtonPolygon):
            return False
        return self.sides() == other.sides()
