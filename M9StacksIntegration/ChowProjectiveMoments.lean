module

public import M9StacksIntegration.ChowProjectiveCoefficient
public import M9StacksIntegration.ChowProjectiveShiftedRelation
public import StacksFrontier.AlgebraicGeometry.Chow.GenuineChern.ChernFamily

/-!
# Genuine projective pushforward moments on the actual Chow groups

The jth map is the literal actual proper pushforward of the (n+j)th
power of the original tautological first-Chern cap after genuine flat
pullback for an original bundle of rank n+1. No inverse-Chern or Schur
identity is part of the definition or supplied as a premise.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false

open AlgebraicGeometry CategoryTheory Stacks.Chow

universe u

namespace M9Native.ChowProjectiveMoments

variable {X : Scheme.{u}} (E : X.Modules) (n : ℕ)
  [hE : SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} E (n+1)]
  (C : ChowSituation.{u}) (q : X ⟶ C.S) [LocallyOfFiniteType q]

/-- The actual jth projective moment, on every original integer-graded Chow group. -/
def moment (j : ℕ) (k : ℤ) : chowGroup C q k →+ chowGroup C q (k-(j:ℤ)) := by
  letI := hE.isFiniteLocallyFree
  letI := flat_bundleProj E n
  letI := locallyOfFiniteType_bundleProj E n
  exact bundleProjection C q (bundleProj E ≫ q) (bundleProj E) rfl n
    (relativeDimension_bundleProj E n) (invCap C (bundleProj E ≫ q) (bundleTwist E))
    (n+j) k (k-(j:ℤ)) (by push_cast; ring)

/-- The same actual geometric maps as a native graded cap family. -/
def momentFamily : GradedCapFamily (chowGroup C q) := fun k j => moment E n C q j k

/-- The geometric meaning is literal actual proper Chow pushforward,
not a cohomological trace or an assumed inverse-Chern coefficient. -/
theorem moment_apply (j : ℕ) (k : ℤ) (α : chowGroup C q k) :
    letI := hE.isFiniteLocallyFree
    letI := flat_bundleProj E n
    letI := locallyOfFiniteType_bundleProj E n
    moment E n C q j k α =
      properChowPushforward C (bundleProj E ≫ q) q (bundleProj E) rfl (k-(j:ℤ))
        (properPushforwardFactorsThroughRationalEquivalence_of_isProper C
          (bundleProj E ≫ q) q (bundleProj E) rfl (k-(j:ℤ)))
        (capPow C (bundleProj E ≫ q) (invCap C (bundleProj E ≫ q) (bundleTwist E))
          (n+j) (k+n) (k-(j:ℤ)) (by push_cast; ring)
          (bundlePullback C q (bundleProj E ≫ q) (bundleProj E) rfl n
            (relativeDimension_bundleProj E n) k α)) := rfl

/-- Actual top-power normalization of the original projective bundle. -/
theorem moment_zero (k : ℤ) (α : chowGroup C q k) : moment E n C q 0 k α ≍ α := by
  letI := hE.isFiniteLocallyFree
  letI := flat_bundleProj E n
  letI := locallyOfFiniteType_bundleProj E n
  have cast_heq : ∀ {a b : ℤ} (e : a = b) (β : chowGroup C q a),
      chowGroupCast C q e β ≍ β := by
    intro a b e β
    cases e
    rfl
  let e : k = k-((0:ℕ):ℤ) := by omega
  have hc := bundleProjection_congr_target C q (bundleProj E ≫ q) (bundleProj E) rfl n
    (relativeDimension_bundleProj E n) (invCap C (bundleProj E ≫ q) (bundleTwist E))
    n k (by ring) e α
  exact (heq_of_eq hc).trans ((cast_heq e _).trans
    (heq_of_eq (projectiveBundle_projection_self E n C q k α)))

/-- The actual moment family has identity constant coefficient,
derived from genuine projective-bundle normalization. -/
theorem momentFamily_apply_zero (k : ℤ) :
    momentFamily E n C q k 0 = (1 : GradedCapFamily (chowGroup C q)) k 0 := by
  apply AddMonoidHom.ext
  intro α
  apply eq_of_heq
  exact (moment_zero E n C q k α).trans
    ((heq_of_eq (gradedCap_one_apply_zero k α)).trans (gradedDegreeCast_heq _ α)).symm

/-- The actual characteristic relation, multiplied by an actual extra
cap power and genuinely pushed down. This is the geometric recurrence
before any inverse-Chern interpretation or formal coefficient reindexing. -/
theorem projected_characteristic_relation (k : ℤ) (m : ℕ) (hm : 0 < m)
    (α : chowGroup C q k) :
    letI := hE.isFiniteLocallyFree
    letI := flat_bundleProj E n
    letI := locallyOfFiniteType_bundleProj E n
    ∑ i : Fin (n+2), (-1 : ℤ) ^ (i:ℕ) •
      bundleProjection C q (bundleProj E ≫ q) (bundleProj E) rfl n
        (relativeDimension_bundleProj E n) (invCap C (bundleProj E ≫ q) (bundleTwist E))
        ((i:ℕ)+(m-1)) (k-((n+1-(i:ℕ):ℕ):ℤ)) (k-(m:ℤ))
        (by have hi := i.isLt; have hm' : 1 ≤ m := hm
            push_cast [Nat.cast_sub (by omega : (i:ℕ) ≤ n+1), Nat.cast_sub hm']; ring)
        (bundleChernCapFamily E n C q k α ⟨n+1-(i:ℕ), by omega⟩) = 0 := by
  letI := hE.isFiniteLocallyFree
  letI := flat_bundleProj E n
  letI := locallyOfFiniteType_bundleProj E n
  have h := congrArg
    (ChowProjectiveShiftedRelation.shiftedPush C q (bundleProj E ≫ q)
      (bundleProj E) rfl n (invCap C (bundleProj E ≫ q) (bundleTwist E)) k m hm)
    (isChernCapFamily_bundleChernCapFamily E n C q k α).2
  have htwist : bundleTwistCap E C q =
      invCap C (bundleProj E ≫ q) (bundleTwist E) := rfl
  simpa only [map_sum, map_zsmul, map_zero, htwist,
    ChowProjectiveShiftedRelation.shiftedPush_chernTerm] using h

end M9Native.ChowProjectiveMoments
