module

public import M9StacksIntegration.PresheafValuedClassifierReflection

/-! Equality of actual represented maps to a discrete presheaf determines
the entire based classifier functor. This supplies the object-equality
input to genuine geometric-fibre lifting, without assuming an isomorphism
in the original source category. -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxRecDepth 4096

open CategoryTheory Opposite
open CategoryTheory.PresheafOfCategories
attribute [local implicit_reducible] CategoryTheory.BasedCategory.ofFunctor

namespace M9Native.PresheafClassifierInjectivity

open PresheafValuedClassifierReflection
universe v u vD uD

variable {C : Type u} [Category.{v} C] {P : Cᵒᵖ ⥤ Type v} {U : C}
  {F G : BasedCategory.ofFunctor (Over.forget U) ⥤ᵇ elementsBased P}

/-- Actual map equality recovers equality of the whole functors,
including their values on every original slice object and arrow. -/
theorem functor_eq_of_representingMap_eq
    (h : representingMap F = representingMap G) : F.toFunctor = G.toFunctor := by
  apply eq_of_sections_eq F.toFunctor G.toFunctor F.w G.w
  intro t
  change mapAt F t = mapAt G t
  have hunit : mapAt F (Functor.FiberedMor.unit U) =
      mapAt G (Functor.FiberedMor.unit U) := by
    have hh := congrArg yonedaEquiv h
    simpa only [representingMap, Equiv.apply_symm_apply] using hh
  have hF := mapAt_naturality F (Functor.FiberedMor.toUnit t)
  have hG := mapAt_naturality G (Functor.FiberedMor.toUnit t)
  exact hF.symm.trans ((congrArg
    (P.map (Functor.FiberedMor.toUnit t).left.op) hunit).trans hG)

/-- In particular equal represented sections give literal equal objects
in the genuine category of elements, not a supplied source isomorphism. -/
theorem object_eq_of_representingMap_eq
    (h : representingMap F = representingMap G) (t : Over U) :
    F.toFunctor.obj t = G.toFunctor.obj t :=
  Functor.congr_obj (functor_eq_of_representingMap_eq h) t

/-- The discrete-target comparison is exact in both directions. -/
theorem representingMap_eq_iff_functor_eq :
    representingMap F = representingMap G ↔ F.toFunctor = G.toFunctor := by
  refine ⟨functor_eq_of_representingMap_eq, ?_⟩
  intro h
  apply yonedaEquiv.injective
  simp only [representingMap, Equiv.apply_symm_apply]
  exact sectionOfBasedFunctor_congr F.toFunctor G.toFunctor F.w G.w
    (Functor.congr_obj h (Functor.FiberedMor.unit U))

end M9Native.PresheafClassifierInjectivity
