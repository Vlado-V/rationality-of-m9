module

public import M9StacksIntegration.ChowProjectiveTensorPush

/-! The actual terms of the projective tensor push, with the genuine
pulled Chern coefficient moved outside the original proper pushforward. -/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 1500000

open AlgebraicGeometry CategoryTheory Stacks.Chow Stacks.Chow.GenuineChern

universe u
namespace M9Native.ChowProjectiveTensorPushTerms

open ChowProjectiveTensorPush

theorem properPush_cast (C : ChowSituation.{u}) {X Y : Scheme.{u}}
    (qX : X ⟶ C.S) [LocallyOfFiniteType qX] (qY : Y ⟶ C.S) [LocallyOfFiniteType qY]
    (p : X ⟶ Y) [IsProper p] (hp : p ≫ qY = qX) {k l : ℤ} (h : k=l)
    (α : chowGroup C qX k) :
    ChowLineProperPush.properPush C qX qY p hp l (chowGroupCast C qX h α) =
      chowGroupCast C qY h (ChowLineProperPush.properPush C qX qY p hp k α) := by
  subst l
  rfl

variable {X : Scheme.{u}} (E : X.Modules) (n : ℕ)
  [hE : SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} E (n+1)]
  (F : X.Modules) (r : ℕ)
  [SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} F r]
  (C : ChowSituation.{u}) (q : X ⟶ C.S) [LocallyOfFiniteType q]

def projectedCoefficient (a b : ℕ) (hab : r+a=n+b) (k : ℤ) (j : Fin (r+1))
    (α : chowGroup C q k) : chowGroup C q (k-b) := by
  letI := hE.isFiniteLocallyFree
  letI := Stacks.Chow.flat_bundleProj E n
  letI := Stacks.Chow.locallyOfFiniteType_bundleProj E n
  let qP := bundleProj E ≫ q
  let γ := bundleProjection C q qP (bundleProj E) rfl n
    (Stacks.Chow.relativeDimension_bundleProj E n) (invCap C qP (bundleTwist E))
    (a+(j:ℕ)) k (k+n-a-(j:ℤ)) (by push_cast; ring) α
  exact chowGroupCast C q (by have hj := j.isLt; omega)
    (chernFamily C q F r (k+n-a-(j:ℤ)) (r-(j:ℕ)) γ)

theorem projectionTerm_eq_projectedCoefficient (a b : ℕ) (hab : r+a=n+b) (k : ℤ)
    (j : Fin (r+1)) (α : chowGroup C q k) :
    projectionTerm E n F r C q a b hab k j α =
      projectedCoefficient E n F r C q a b hab k j α := by
  letI := hE.isFiniteLocallyFree
  letI := Stacks.Chow.flat_bundleProj E n
  letI := Stacks.Chow.locallyOfFiniteType_bundleProj E n
  letI := AlgebraicGeometry.isFiniteLocallyFreeOfRank_pullback (bundleProj E) F r
  dsimp only [projectionTerm, tensorTerm, projectedCoefficient]
  rw [capPow_capPow]
  simp only [chowGroupCast_chowGroupCast]
  rw [properPush_cast]
  rw [← chernFamily_apply_of_le C (bundleProj E ≫ q)
    ((Scheme.Modules.pullback (bundleProj E)).obj F) r
    (k+n-a-(j:ℤ)) (show r-(j:ℕ) ≤ r by omega)]
  rw [ChowLineProperPush.properPush_chernFamily_apply C (bundleProj E ≫ q) q
    (bundleProj E) rfl F r ((Scheme.Modules.pullback (bundleProj E)).obj F) (Iso.refl _)]
  rfl

end M9Native.ChowProjectiveTensorPushTerms
