module

public import M9StacksIntegration.ChowLineFamilyComparison
public import StacksFrontier.AlgebraicGeometry.Chow.GenuineChern.Determinant
public import StacksFrontier.AlgebraicGeometry.Chow.GenuineChern.TopHalfProof
public import StacksFrontier.AlgebraicGeometry.Chow.GenuineChern.BundleBaseChangeHolds
public import StacksFrontier.AlgebraicGeometry.Chow.GenuineChern.SubbundleGeometry

/-!
# The original first Chern component is the actual determinant-line cap

The coefficient of the native total Chern cap family is first compared
with the actual Segre pushforward by the projective bundle relation.
The native determinant theorem, with its genuinely constructed geometric
inputs, then identifies it with the original determinant-line cap.
These are equalities on every original integral Chow group.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false

open AlgebraicGeometry CategoryTheory Stacks.Chow Stacks.Chow.GenuineChern

universe u

namespace M9Native.ChowDeterminantFirstComponent

variable (C : ChowSituation.{u}) {X : Scheme.{u}} (q : X ⟶ C.S)
  [LocallyOfFiniteType q] (E : X.Modules) (n : ℕ)
  [hE : SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} E (n+1)]

/-- The actual degree-one coefficient equals the original first-Chern
Segre construction, by the genuine projective bundle formula. -/
theorem chernCap_first_eq_firstChern (k : ℤ) (α : chowGroup C q k) :
    chernCap C (n+1) q E k ⟨1, by omega⟩ α = firstChern E C q (n+1) k α := by
  let _ := hE.isFiniteLocallyFree
  have := GenuineChern.flat_bundleProj E n
  have := GenuineChern.locallyOfFiniteType_bundleProj E n
  let β := projectiveBundleProjection C q (bundleProj E ≫ q) (bundleProj E) rfl (n+1)
    (GenuineChern.relativeDimension_bundleProj E n)
    (fun d => flatPullbackFactorsThroughRationalEquivalence_general C _ q _ rfl _ _ d)
    (bundleTwistCap E C q) (n+1) k α
  have h := chowGroupCast_one_eq_projectiveBundleProjection_of_isChernCapFamily
    C q (bundleProj E ≫ q) (bundleProj E) rfl (n+1)
    (GenuineChern.relativeDimension_bundleProj E n)
    (fun d => flatPullbackFactorsThroughRationalEquivalence_general C _ q _ rfl _ _ d)
    (bundleTwistCap E C q) (by omega) (topHalf C q E n) k α
    (bundleChernCapFamily E n C q k α) (isChernCapFamily_bundleChernCapFamily E n C q k α)
  have hc : chernCap C (n+1) q E k ⟨1, by omega⟩ α ≍ β :=
    (chowGroupCast_heq C q _ (bundleChernCapFamily E n C q k α ⟨1, by omega⟩)).symm.trans
      (heq_of_eq h)
  exact eq_of_heq (hc.trans
    (chowGroupCast_heq C q
      (show k + ((n+1-1 : ℕ) : ℤ) - ((n+1 : ℕ) : ℤ) = k-1 by omega) β).symm)

/-- The literal determinant line, with actual invertibility derived. -/
def determinantLine : ChowCapWords.InvertibleLine X :=
  ⟨Scheme.Modules.exteriorPower E ((n+1 : ℕ) : ℤ), isInvertible_det E (n+1)⟩

/-- c1(E) is exactly the same original operational cap family as
c1(det E), without a supplied determinant-Chern identity. -/
theorem firstComponent_eq_lineFamily :
    homComponent 1 (chernFamily C q E (n+1)) =
      GradedLineCapSubring.lineFamily C q (determinantLine E n) := by
  funext k j
  by_cases hj : j = 1
  · subst j
    apply AddMonoidHom.ext
    intro α
    rw [homComponent_apply_self,
      chernFamily_apply_of_le C q E (n+1) k (by omega : 1 ≤ n+1)]
    rw [chernCap_first_eq_firstChern C q E n,
      firstChern_eq_firstChernClassCapChow_exteriorPower (topHalf C)
        (flatCompat_of C bundleBaseChangeHolds) (subAdditive C) (n+1)]
    rw [GradedLineCapSubring.lineFamily_apply_one]
    rfl
  · rw [homComponent_apply_of_ne hj,
      GradedLineCapSubring.lineFamily_homogeneous C q (determinantLine E n) k j hj]

end M9Native.ChowDeterminantFirstComponent
