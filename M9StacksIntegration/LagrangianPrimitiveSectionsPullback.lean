module

public import M9StacksIntegration.LagrangianPluckerQuotient
public import M9StacksIntegration.LagrangianDeterminantPullback

/-!
# Actual base change of the fourteen primitive determinant sections

This thin consequence of determinant-section base change records the
coefficient map explicitly.  It applies to every native quotient
presentation and every test scheme, without a curve or pointwise premise.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
set_option maxRecDepth 4096

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite Module
open scoped BigOperators

universe u

namespace M9Native.LagrangianPrimitiveSectionsPullback

open AlgebraicGeometry.Grassmannian LagrangianPluckerQuotient
open LagrangianDeterminantPullback LagrangianPullback

attribute [local implicit_reducible] TopCat.Sheaf CategoryTheory.sheafCompose
  AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme.Modules.Hom

/-- All fourteen actual primitive sections commute with actual pullback,
including their structural coefficient-ring map. -/
theorem primitiveSection_pullback {X Y : Scheme.{u}} (g : Y ⟶ X)
    (k : Type u) [Field k] (κ : k →+* Γ(X, ⊤)) {r : ℕ}
    (q : QuotientPresentation X r 6) (j : Fin 14) :
    (exteriorPullbackIso g q.target 3).hom.app ⊤
        (pullbackGlobalSections g (Scheme.Modules.exteriorPower q.target 3)
          (primitiveSection X k κ q.map j)) =
      primitiveSection Y k (g.appTop.hom.comp κ) (pullbackPresentation g q).map j := by
  simp only [primitiveSection, map_sum, SectionsEqualizer.pullbackGlobalSections_smul,
    Scheme.Modules.Hom.app_smul, minorSection_pullback, RingHom.comp_apply]

/-- In particular the actual universal LG determinant sections pull back
to the primitive sections of its literal pulled-back quotient. -/
theorem primitiveSections_pullback {X : Scheme.{u}} (k : Type u) [Field k]
    (g : X ⟶ LagrangianGrassmannian.space k) (j : Fin 14) :
    (exteriorPullbackIso g (quotientOnLG k).target 3).hom.app ⊤
        (pullbackGlobalSections g (determinantLine k) (primitiveSections k j)) =
      primitiveSection X k (LagrangianPlucker.coefficientMap k g)
        (pullbackPresentation g (quotientOnLG k)).map j := by
  have hκ : g.appTop.hom.comp (LagrangianPlucker.coefficientMap k (𝟙 _)) =
      LagrangianPlucker.coefficientMap k g := by
    simpa only [Category.comp_id] using (LagrangianPlucker.coefficientMap_comp k (𝟙 _) g).symm
  change (exteriorPullbackIso g (quotientOnLG k).target 3).hom.app ⊤
      (pullbackGlobalSections g (Scheme.Modules.exteriorPower (quotientOnLG k).target 3)
        (primitiveSection _ k _ (quotientOnLG k).map j)) = _
  rw [primitiveSection_pullback, hκ]

end M9Native.LagrangianPrimitiveSectionsPullback
