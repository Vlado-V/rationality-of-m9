module

public import StacksFrontier.Deformation.RingedSpaceThickening.NaiveCotangentTwoTermOfDouble

/-!
# The original conormal extension class is represented by an actual cochain map

The representative retains the pinned mapping-cone projection and its
sign. This separates class naturality from any flatness or injectivity
claim about a general two-term derived pullback.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
set_option maxRecDepth 4096

open CategoryTheory CategoryTheory.Limits HomologicalComplex CochainComplex
open AlgebraicGeometry.RingedSpaceThickening

universe u v w

namespace M9Native.ConormalClassCochain

variable {C : Type u} [Category.{v} C] [Abelian C]
  {A B G : C} (d : A ⟶ B) (δ : A ⟶ G)

/-- The literal original mapping-cone representative of the conormal class. -/
def classMap : double d ComplexShape.upIntRelNegOneZero ⟶
    ((CochainComplex.singleFunctor C 0).obj G)⟦(1 : ℤ)⟧ :=
  doubleToMappingCone d ComplexShape.upIntRelNegOneZero ≫
    (mappingCone.triangle ((CochainComplex.singleFunctor C 0).map d)).mor₃ ≫
    ((CochainComplex.singleFunctor C 0).map δ)⟦(1 : ℤ)⟧'

variable [HasDerivedCategory.{w} C]

/-- The actual original conormal class is Q of this actual chain map,
followed by the original shift comparison, with no class formula input. -/
theorem conormalExtClass_eq :
    (NaiveCotangentTwoTerm.ofDoubleNegOne d).conormalExtClass G δ =
      DerivedCategory.Q.map (classMap d δ) ≫
        (DerivedCategory.Q.commShiftIso (1 : ℤ)).hom.app
          ((CochainComplex.singleFunctor C 0).obj G) := by
  change
    (DerivedCategory.Q.map (doubleToMappingCone d ComplexShape.upIntRelNegOneZero) ≫
      (DerivedCategory.Q.map
        (mappingCone.triangle ((CochainComplex.singleFunctor C 0).map d)).mor₃ ≫
        (DerivedCategory.Q.commShiftIso (1 : ℤ)).hom.app
          ((CochainComplex.singleFunctor C 0).obj A))) ≫
      ((DerivedCategory.Q.map ((CochainComplex.singleFunctor C 0).map δ))⟦(1 : ℤ)⟧') = _
  dsimp only [classMap]
  simp only [Functor.map_comp, Category.assoc]
  exact congrArg
    (fun t => DerivedCategory.Q.map (doubleToMappingCone d ComplexShape.upIntRelNegOneZero) ≫
      DerivedCategory.Q.map
        (mappingCone.triangle ((CochainComplex.singleFunctor C 0).map d)).mor₃ ≫ t)
    (((DerivedCategory.Q.commShiftIso (1 : ℤ)).hom.naturality
      ((CochainComplex.singleFunctor C 0).map δ)).symm)

end M9Native.ConormalClassCochain
