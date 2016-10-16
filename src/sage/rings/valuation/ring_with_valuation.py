from sage.structure.unique_representation import UniqueRepresentation
from sage.structure.parent import Parent
from sage.rings.all import ZZ

class RingWithValuationFacade(UniqueRepresentation, Parent):
    def __init__(self, domain, valuation, category):
        self._valuation = valuation
        Parent.__init__(self, facade=domain, category=category)

    def valuation(self):
        return self._valuation

    def _element_constructor_(self, x):
        return self.element_class(x)

    element_class = ZZ
