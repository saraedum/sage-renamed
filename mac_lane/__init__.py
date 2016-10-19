from .valuation_space import DiscretePseudoValuationSpace, DiscreteValuationSpace
from .trivial_valuation import TrivialValuation, TrivialPseudoValuation
from .padic_valuation import pAdicValuation
from .gauss_valuation import GaussValuation
from .value_group import DiscreteValuationCodomain, DiscreteValueGroup
from .function_field_valuation import FunctionFieldValuation
from .augmented_valuation import AugmentedValuation

# fix unpickling and type checks of classes (otherwise, the instances of the
# local file and the instances that come from the mac_lane import define
# different types)
from .trivial_valuation import TrivialDiscreteValuation, TrivialDiscretePseudoValuation
from .function_field_valuation import FunctionFieldValuation_base, RationalFunctionFieldValuation_base, InducedFunctionFieldValuation_base, ClassicalRationalFunctionFieldValuation_base

# =================
# MONKEY PATCH SAGE
# =================
import sage

# Implement Qp/Zp.valuation
sage.rings.padics.padic_generic.pAdicGeneric.valuation = lambda self: pAdicValuation(self)

# Fix contains check of rational fuction fields
r"""
sage: K.<x> = FunctionField(QQ)
sage: K(1) in QQ
True
sage: K(x) in K._ring
True
"""
def to_polynomial(self, x):
    R = x.parent()._ring
    K = x.parent().constant_base_field()
    if x.denominator() in K:
        return x.numerator()/K(x.denominator())
    raise ValueError("Only polynomials can be converted to the underlying polynomial ring")

sage.rings.function_field.function_field.RationalFunctionField._to_polynomial = to_polynomial
sage.rings.function_field.function_field.RationalFunctionField.__old_init__ = sage.rings.function_field.function_field.RationalFunctionField.__init__
def __init__(self, *args, **kwargs):
    self.__old_init__(*args, **kwargs)
    from sage.categories.morphism import SetMorphism
    self._ring.register_conversion(SetMorphism(self.Hom(self._ring), self._to_polynomial))

sage.rings.function_field.function_field.RationalFunctionField.__init__ = __init__
del(__init__)
del(to_polynomial)

# implement principal_part for newton polygons
import sage.geometry.newton_polygon
sage.geometry.newton_polygon.NewtonPolygon_element.principal_part = lambda self: sage.geometry.newton_polygon.NewtonPolygon(self.vertices(), last_slope=0)
sage.geometry.newton_polygon.NewtonPolygon_element.sides = lambda self: zip(self.vertices(), self.vertices()[1:])

# implement coercion of function fields that comes from coercion of their base fields
def _coerce_map_from_(target, source):
    from sage.categories.function_fields import FunctionFields
    if source in FunctionFields():
        if source.base_field() is source and target.base_field() is target:
            if source.variable_name() == target.variable_name():
                # source and target are rational function fields in the same variable
                base_coercion = target.constant_field().coerce_map_from(source.constant_field())
                if base_coercion is not None:
                    return source.hom([target.gen()], base_morphism=base_coercion)
        if source.base_field() is not source and target.base_field() is not target:
            # source and target are extensions of rational function fields
            base_coercion = target.base_field().coerce_map_from(source.base_field())
            if base_coercion is not None:
                # The base field of source coerces into the base field of target.
                if source.polynomial().map_coefficients(base_coercion)(target.gen()) == 0:
                    # The defining polynomial of source has a root in target,
                    # therefore there is a map. To be sure that it is
                    # canonical, we require a root of the defining polynomial
                    # of target to be a root of the defining polynomial of
                    # source (and that the variables are named equally):
                    if source.variable_name() == target.variable_name():
                        return source.hom([target.gen()], base_morphism=base_coercion)

sage.rings.function_field.function_field.FunctionField._coerce_map_from_ = _coerce_map_from_

del(_coerce_map_from_)


import imp, sys
# register modules at some standard places so imports work as exepcted
r"""
sage: from sage.rings.valuation.gauss_valuation import GaussValuation
"""
sage.rings.valuation = sys.modules['sage.rings.valuation'] = imp.new_module('sage.rings.valuation')
sage.rings.valuation.gauss_valuation = sys.modules['sage.rings.valuation.gauss_valuation'] = gauss_valuation
sage.rings.valuation.valuation = sys.modules['sage.rings.valuation.valuation'] = valuation
sage.rings.valuation.valuation_space = sys.modules['sage.rings.valuation.valuation_space'] = valuation_space
sage.rings.valuation.augmented_valuation = sys.modules['sage.rings.valuation.augmented_valuation'] = augmented_valuation
sage.rings.function_field.function_field_valuation = sys.modules['sage.rings.function_field.function_field_valuation'] = function_field_valuation

# fix unpickling of factories
from sage.structure.factory import register_factory_unpickle
register_factory_unpickle("pAdicValuation", pAdicValuation)
register_factory_unpickle("GaussValuation", GaussValuation)
register_factory_unpickle("TrivialValuation", TrivialValuation)
register_factory_unpickle("TrivialPseudoValuation", TrivialPseudoValuation)
register_factory_unpickle("FunctionFieldValuation", FunctionFieldValuation)
