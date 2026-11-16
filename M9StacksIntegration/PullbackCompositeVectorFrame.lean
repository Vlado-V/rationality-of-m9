module

public import M9StacksIntegration.LineFramePullback

/-! Native pullback-composition and pullback-congruence retain their
actual three morphisms as parameters. This avoids comparing a fixed
projective-chart alias with the caller's original morphism. The section
formula is derived from the original native pullback-section laws. -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
attribute [local implicit_reducible] TopCat.Sheaf CategoryTheory.sheafCompose
  AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme.Modules.Hom
universe u

namespace M9Native.PullbackCompositeVectorFrame
variable {T Y X : Scheme.{u}} (f : T ⟶ Y) (g : Y ⟶ X) (h : T ⟶ X)
  (w : f ≫ g = h) (E : X.Modules)

/-- The literal native composition/congruence comparison, on the actual
maps supplied by the caller. -/
def iso :
    (Scheme.Modules.pullback f).obj ((Scheme.Modules.pullback g).obj E) ≅
      (Scheme.Modules.pullback h).obj E :=
  (Scheme.Modules.pullbackComp f g).app E ≪≫
    (Scheme.Modules.pullbackCongr w).app E

/-- The actual comparison sends the twice-pulled original section to
the section pulled along the actual third map. -/
theorem iso_section (s : Γ(E, ⊤)) :
    (iso f g h w E).hom.app ⊤
      (pullbackGlobalSections f ((Scheme.Modules.pullback g).obj E)
        (pullbackGlobalSections g E s)) =
      pullbackGlobalSections h E s := by
  change (((Scheme.Modules.pullbackCongr w).hom.app E).app ⊤)
    ((((Scheme.Modules.pullbackComp f g).hom.app E).app ⊤)
      (pullbackGlobalSections f ((Scheme.Modules.pullback g).obj E)
        (pullbackGlobalSections g E s))) = _
  rw [AlgebraicGeometry.SectionsEqualizer.pullbackGlobalSections_comp,
    AlgebraicGeometry.SectionsEqualizer.pullbackGlobalSections_congr]

end M9Native.PullbackCompositeVectorFrame
