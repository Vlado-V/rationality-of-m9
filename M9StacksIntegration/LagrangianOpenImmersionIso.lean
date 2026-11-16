module

public import StacksFrontier.AlgebraicGeometry.AffineBaseChange.Basic

/-! Actual module-map invertibility on an open-immersion cover, via actual stalks. -/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
set_option maxRecDepth 4096

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace M9Native.LagrangianOpenImmersionIso

/-- Only ordinary sheaf restriction and actual stalk maps are used;
no derived-category comparison or unproved descent statement is a premise. -/
theorem isIso_of_openImmersion_cover {Y : Scheme.{u}} {F G : Y.Modules} (φ : F ⟶ G)
    {I : Type*} {Z : I → Scheme.{u}} (j : ∀ i,Z i ⟶ Y)
    [∀ i,IsOpenImmersion (j i)]
    (hj : ∀ y : Y,∃ i,y ∈ Set.range (j i).base)
    (h : ∀ i,IsIso ((Scheme.Modules.restrictFunctor (j i)).map φ)) : IsIso φ := by
  refine Stacks.AlgebraicGeometry.AffineBaseChange.isIso_of_isIso_stalk φ fun y => ?_
  obtain ⟨i,z,rfl⟩ := hj y
  have : IsIso ((Scheme.Modules.restrictFunctor (j i)).map φ) := h i
  have h₃ : IsIso ((Scheme.Modules.restrictFunctor (j i) ⋙ Scheme.Modules.toPresheaf _ ⋙
      TopCat.Presheaf.stalkFunctor Ab.{u} z).map φ) :=
    Functor.map_isIso (Scheme.Modules.toPresheaf _ ⋙ TopCat.Presheaf.stalkFunctor Ab.{u} z) _
  have h₂ : IsIso ((Scheme.Modules.restrictStalkNatIso (j i) z).hom.app F ≫
      (Scheme.Modules.toPresheaf Y ⋙ TopCat.Presheaf.stalkFunctor Ab.{u} ((j i).base z)).map φ) := by
    rw [← (Scheme.Modules.restrictStalkNatIso (j i) z).hom.naturality φ]
    infer_instance
  exact IsIso.of_isIso_comp_left ((Scheme.Modules.restrictStalkNatIso (j i) z).hom.app F)
    ((Scheme.Modules.toPresheaf Y ⋙ TopCat.Presheaf.stalkFunctor Ab.{u} ((j i).base z)).map φ)

end M9Native.LagrangianOpenImmersionIso
