module

public import M9StacksIntegration.ConormalClassCochain
public import StacksFrontier.Algebra.Homology.DoubleMapFunctor

/-!
# The actual local components of the original conormal-class representative

The original mapping-cone convention contributes its literal minus sign.
These computations will be used with genuine compatible conormal maps.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
set_option maxRecDepth 4096

open CategoryTheory CategoryTheory.Limits HomologicalComplex CochainComplex
open AlgebraicGeometry.RingedSpaceThickening

universe u v

namespace M9Native.ConormalClassComponents

variable {C : Type u} [Category.{v} C] [Abelian C]

/-- The original coefficient object of a shifted original single complex. -/
def coefficientIso (G : C) :
    (((CochainComplex.singleFunctor C 0).obj G)⟦(1 : ℤ)⟧).X (-1) ≅ G :=
  ((CochainComplex.singleFunctor C 0).obj G).shiftFunctorObjXIso 1 (-1) 0 (by decide) ≪≫
    HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 G

variable {A B G : C} (d : A ⟶ B) (δ : A ⟶ G)

/-- The original conormal representative in degree minus one is minus
the actual conormal-to-coefficient morphism. -/
theorem classMap_f_negOne :
    (ConormalClassCochain.classMap d δ).f (-1) ≫ (coefficientIso G).hom =
      -((doubleXIso₀ d ComplexShape.upIntRelNegOneZero).hom ≫ δ) := by
  simp [ConormalClassCochain.classMap, doubleToMappingCone,
    coefficientIso, Category.assoc, CochainComplex.shiftFunctorObjXIso,
    CochainComplex.shiftFunctor_map_f', CochainComplex.singleFunctor,
    HomologicalComplex.single_map_f_self]

/-- Its original degree-zero component has the actual zero target. -/
theorem classMap_f_zero : (ConormalClassCochain.classMap d δ).f 0 = 0 := by
  exact (HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) 0 G 1 (by decide)).eq_of_tgt _ _

end M9Native.ConormalClassComponents
