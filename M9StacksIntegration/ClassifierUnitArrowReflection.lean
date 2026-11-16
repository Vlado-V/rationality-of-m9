module

public import M9StacksIntegration.AlgebraicSpaceValuedClassifierReflection

/-! A single vertical arrow at the actual Yoneda unit determines equality
of the represented presheaf and algebraic-space maps. -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 200000
set_option maxRecDepth 512

open AlgebraicGeometry CategoryTheory Opposite
open CategoryTheory.PresheafOfCategories
attribute [local implicit_reducible] CategoryTheory.BasedCategory.ofFunctor

namespace M9Native.ClassifierUnitArrowReflection

universe v u vD uD

section Presheaf
variable {C : Type u} [Category.{v} C] {P : Cᵒᵖ ⥤ Type v} {U : C}
  {F G : BasedCategory.ofFunctor (Over.forget U) ⥤ᵇ
    PresheafValuedClassifierReflection.elementsBased P}

/-- A vertical arrow at the actual unit alone identifies the Yoneda value. -/
theorem representingMap_eq_of_unit_arrow
    (α : F.obj (Functor.FiberedMor.unit U) ⟶ G.obj (Functor.FiberedMor.unit U))
    (hα : (discreteProjection P).IsHomLift (𝟙 U) α) :
    PresheafValuedClassifierReflection.representingMap F =
      PresheafValuedClassifierReflection.representingMap G := by
  have h := elementOf_eq_map (P := P)
    (Functor.congr_obj F.w (Functor.FiberedMor.unit U))
    (Functor.congr_obj G.w (Functor.FiberedMor.unit U)) (𝟙 U) α hα
  change _ = P.map (𝟙 (op U)) _ at h
  rw [P.map_id_apply] at h
  exact congrArg (fun t => yonedaEquiv.symm t) h

end Presheaf

section AlgebraicSpace
variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {D : Type uD} [Category.{vD} D] {p : D ⥤ BigFppfOver B S hS}
  {M : AlgebraicSpaces B S hS}
  (κ : BasedCategory.ofFunctor p ⥤ᵇ AlgebraicSpaceValuedClassifierReflection.target B S hS M)
  {U : BigFppfOver B S hS}
  {F G : BasedCategory.ofFunctor (Over.forget U) ⥤ᵇ BasedCategory.ofFunctor p}

/-- The actual space-valued functor sends a source unit arrow to equality
in the discrete target; no transformation away from the unit is required. -/
theorem nativeMap_eq_of_unit_arrow
    (α : F.obj (Functor.FiberedMor.unit U) ⟶ G.obj (Functor.FiberedMor.unit U))
    (hα : p.IsHomLift (𝟙 U) α) :
    AlgebraicSpaceValuedClassifierReflection.nativeMap B S hS κ F =
      AlgebraicSpaceValuedClassifierReflection.nativeMap B S hS κ G := by
  have : (BasedCategory.ofFunctor p).p.IsHomLift (𝟙 U) α := hα
  have hκ := Functor.isHomLift_map_of_comp_eq κ.w (𝟙 U) α
  apply ObjectProperty.hom_ext
  exact representingMap_eq_of_unit_arrow (κ.map α) hκ

end AlgebraicSpace

end M9Native.ClassifierUnitArrowReflection
