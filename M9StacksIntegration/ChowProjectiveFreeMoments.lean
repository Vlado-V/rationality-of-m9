module

public import M9StacksIntegration.ChowProjectiveMomentInverse
public import M9StacksIntegration.ChowFreeBundleChern

/-!
# Genuine projective pushforward moments of an actual free bundle

A literal free trivialization gives the Chern-family identity by genuine
split exact rows. The actual projective moment relation then forces all
positive moments to vanish on every original integral Chow group.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false

open AlgebraicGeometry CategoryTheory Stacks.Chow
open Stacks.Chow.GenuineChern
universe u
namespace M9Native.ChowProjectiveFreeMoments

variable {X : Scheme.{u}} (E : X.Modules) (n : ℕ)
  [SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} E (n+1)]
  (C : ChowSituation.{u}) (q : X ⟶ C.S) [LocallyOfFiniteType q]

/-- An actual sheaf trivialization, rather than a supplied Chern or
pushforward formula, gives the actual geometric moment family one. -/
theorem momentFamily_eq_one_of_iso_free
    (e : E ≅ SheafOfModules.free (R := X.ringCatSheaf) (ULift.{u} (Fin (n+1)))) :
    ChowProjectiveMoments.momentFamily E n C q = 1 := by
  have hc := ChowFreeBundleChern.chernFamily_eq_one_of_iso_free C q E (n+1) e
  simpa only [hc, capFamilySignScale_one, mul_one] using
    ChowProjectiveMomentInverse.momentFamily_mul_signed_chern E n C q

/-- The actual pushforward of a power strictly above the fiber's top
power vanishes for an actual free bundle, on every original Chow input. -/
theorem moment_eq_zero_of_pos_of_iso_free
    (e : E ≅ SheafOfModules.free (R := X.ringCatSheaf) (ULift.{u} (Fin (n+1))))
    (j : ℕ) (hj : 0 < j) (k : ℤ) (α : chowGroup C q k) :
    ChowProjectiveMoments.moment E n C q j k α = 0 := by
  have h := congrArg (fun a : GradedCapFamily (chowGroup C q) => a k j α)
    (momentFamily_eq_one_of_iso_free E n C q e)
  simpa only [ChowProjectiveMoments.momentFamily,
    gradedCap_one_of_ne (by omega : j ≠ 0), AddMonoidHom.zero_apply] using h

end M9Native.ChowProjectiveFreeMoments
