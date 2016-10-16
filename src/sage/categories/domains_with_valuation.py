# Fix doctests so they work in standalone mode (when invoked with sage -t, they run within the mac_lane/ directory)
import sys, os
if hasattr(sys.modules['__main__'], 'DC') and 'standalone' in sys.modules['__main__'].DC.options.optional:
    sys.path.append(os.getcwd())
    sys.path.append(os.path.dirname(os.getcwd()))

from sage.categories.category import Category
from sage.structure.unique_representation import UniqueRepresentation
from sage.structure.parent import Parent
from sage.categories.domains import Domains

class RingsWithDiscretePseudoValuation(Category):
    def super_categories(self):
        return [Domains()]

class RingsWithDiscreteValuation(Category):
    def super_categories(self):
        return [RingsWithDiscretePseudoValuation()]
