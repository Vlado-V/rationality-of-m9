module

public import Mathlib.CategoryTheory.Monoidal.Cartesian.Grp

/-! Actual right translation isomorphisms of a genuine internal group. -/

@[expose] public noncomputable section

open CategoryTheory MonoidalCategory CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

universe u v

namespace M9Native.GroupObjectRightTranslation

variable {C : Type u} [Category.{v} C] [CartesianMonoidalCategory C]
  {G : C} [GrpObj G]

/-- Multiplication on the right by the specified actual global point. -/
def rightTranslation (c : 𝟙_ C ⟶ G) : G ≅ G where
  hom := (𝟙 G) * (toUnit G ≫ c)
  inv := (𝟙 G) * (toUnit G ≫ c⁻¹)
  hom_inv_id := by
    simp [MonObj.comp_mul, GrpObj.comp_inv, Category.assoc]
  inv_hom_id := by
    simp [MonObj.comp_mul, GrpObj.comp_inv, Category.assoc]

/-- Its action on every actual test-object point is literal right multiplication. -/
theorem comp_rightTranslation {T : C} (p : T ⟶ G) (c : 𝟙_ C ⟶ G) :
    p ≫ (rightTranslation c).hom = p * (toUnit T ≫ c) := by
  simp [rightTranslation,MonObj.comp_mul,Category.assoc]

theorem comp_rightTranslation_inv {T : C} (p : T ⟶ G) (c : 𝟙_ C ⟶ G) :
    p ≫ (rightTranslation c).inv = p * (toUnit T ≫ c⁻¹) := by
  simp [rightTranslation,MonObj.comp_mul,Category.assoc]

end M9Native.GroupObjectRightTranslation

