module

public import M9StacksIntegration.ChowProjectiveFreeMoments

/-!
# Actual power pushes for the Lagrangian flag calculation

Every map below is the original projective-bundle projection on Chow
groups. The power can be below, at, or above the fibre dimension.
Only grade transports are recorded by heterogeneous equality.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
set_option maxRecDepth 4096

open AlgebraicGeometry CategoryTheory Stacks.Chow

universe u

namespace M9Native.LagrangianProjectivePowerPush

variable {X : Scheme.{u}} (E : X.Modules) (n : ℕ)
  [hE : SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} E (n+1)]
  (C : ChowSituation.{u}) (q : X ⟶ C.S) [LocallyOfFiniteType q]

/-- Literal flat pullback, tautological cap power and actual proper pushforward. -/
def powerPush (c : ℕ) (k : ℤ) :
    chowGroup C q k →+ chowGroup C q (k+(n:ℤ)-(c:ℤ)) := by
  letI := hE.isFiniteLocallyFree
  letI := flat_bundleProj E n
  letI := locallyOfFiniteType_bundleProj E n
  exact bundleProjection C q (bundleProj E ≫ q) (bundleProj E) rfl n
    (relativeDimension_bundleProj E n)
    (invCap C (bundleProj E ≫ q) (bundleTwist E)) c k (k+(n:ℤ)-(c:ℤ)) (by omega)

/-- Powers below the actual fibre dimension vanish by native projective geometry. -/
theorem powerPush_eq_zero_of_lt (c : ℕ) (hc : c<n) (k : ℤ) (α : chowGroup C q k) :
    powerPush E n C q c k α = 0 := by
  letI := hE.isFiniteLocallyFree
  letI := flat_bundleProj E n
  letI := locallyOfFiniteType_bundleProj E n
  exact projectiveBundle_projection_eq_zero_of_lt E n C q c hc k
    (k+(n:ℤ)-(c:ℤ)) (by omega) α

/-- Above the top fibre power this is the same original geometric moment map. -/
theorem powerPush_eq_moment (c j : ℕ) (hc : c=n+j) (k : ℤ)
    (α : chowGroup C q k) :
    powerPush E n C q c k α ≍ ChowProjectiveMoments.moment E n C q j k α := by
  letI := hE.isFiniteLocallyFree
  letI := flat_bundleProj E n
  letI := locallyOfFiniteType_bundleProj E n
  have hp : ∀ (s t : ℕ) (l l' : ℤ) (hs : s=t)
      (h₁ : k+(n:ℤ)=l+(s:ℤ)) (h₂ : k+(n:ℤ)=l'+(t:ℤ)),
      bundleProjection C q (bundleProj E ≫ q) (bundleProj E) rfl n
          (relativeDimension_bundleProj E n)
          (invCap C (bundleProj E ≫ q) (bundleTwist E)) s k l h₁ α ≍
        bundleProjection C q (bundleProj E ≫ q) (bundleProj E) rfl n
          (relativeDimension_bundleProj E n)
          (invCap C (bundleProj E ≫ q) (bundleTwist E)) t k l' h₂ α := by
    intro s t l l' hs h₁ h₂
    have hl : l=l' := by omega
    cases hs
    cases hl
    rfl
  exact hp c (n+j) (k+(n:ℤ)-(c:ℤ)) (k-(j:ℤ)) hc (by omega) (by push_cast; ring)

/-- The actual top-power push is the identity on every original Chow input. -/
theorem powerPush_top (k : ℤ) (α : chowGroup C q k) :
    powerPush E n C q n k α ≍ α :=
  (powerPush_eq_moment E n C q n 0 (by omega) k α).trans
    (ChowProjectiveMoments.moment_zero E n C q k α)

/-- Every other actual power of a genuinely trivialized bundle pushes to zero. -/
theorem powerPush_eq_zero_of_ne_of_iso_free
    (e : E ≅ SheafOfModules.free (R := X.ringCatSheaf) (ULift.{u} (Fin (n+1))))
    (c : ℕ) (hc : c≠n) (k : ℤ) (α : chowGroup C q k) :
    powerPush E n C q c k α = 0 := by
  by_cases hlt : c<n
  · exact powerPush_eq_zero_of_lt E n C q c hlt k α
  · have hj : 0<c-n := by omega
    have h := powerPush_eq_moment E n C q c (c-n) (by omega) k α
    rw [ChowProjectiveFreeMoments.moment_eq_zero_of_pos_of_iso_free E n C q e
      (c-n) hj k α] at h
    have hzero : ∀ (a b : ℤ), a=b → (0 : chowGroup C q a) ≍ (0 : chowGroup C q b) := by
      intro a b hab
      subst b
      rfl
    exact eq_of_heq (h.trans (hzero _ _ (by omega)))

end M9Native.LagrangianProjectivePowerPush
