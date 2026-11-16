module

public import StacksFrontier.AlgebraicGeometry.Chow.ProjectiveBundleFormula.Formula

/-!
# The actual Chow projective-bundle top coefficient is actual proper pushforward

The coefficient is the last component of the inverse of the genuine
native Chow projective-bundle formula. The equality with proper
pushforward is derived from genuine lower-power vanishing and top
normalization. No trace or cycle-pushforward identification is assumed.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false

open AlgebraicGeometry CategoryTheory
open Stacks.Chow

universe u

namespace M9Native.ChowProjectiveCoefficient

variable {X : Scheme.{u}} (E : X.Modules) (n : ℕ)
  [hE : SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} E (n+1)]
  (C : ChowSituation.{u}) (sX : X ⟶ C.S) [LocallyOfFiniteType sX]

/-- The original native Chow PBF, as an additive equivalence. -/
def formulaEquiv (k : ℤ) :
    letI := hE.isFiniteLocallyFree
    letI := flat_bundleProj E n
    letI := locallyOfFiniteType_bundleProj E n
    (∀ i : Fin (n+1), chowGroup C sX (k + (i : ℕ))) ≃+
      chowGroup C (bundleProj E ≫ sX) (k+n) := by
  letI := hE.isFiniteLocallyFree
  letI := flat_bundleProj E n
  letI := locallyOfFiniteType_bundleProj E n
  exact AddEquiv.ofBijective
    (bundleMap C sX (bundleProj E ≫ sX) (bundleProj E) rfl n
      (relativeDimension_bundleProj E n)
      (invCap C (bundleProj E ≫ sX) (bundleTwist E)) k)
    (projectiveBundle_formula E n C sX k)

/-- Actual proper pushforward along the original bundle projection. -/
def properPush (k : ℤ) :
    letI := hE.isFiniteLocallyFree
    letI := flat_bundleProj E n
    letI := locallyOfFiniteType_bundleProj E n
    chowGroup C (bundleProj E ≫ sX) (k+n) →+ chowGroup C sX (k+n) := by
  letI := hE.isFiniteLocallyFree
  letI := flat_bundleProj E n
  letI := locallyOfFiniteType_bundleProj E n
  exact properChowPushforward C (bundleProj E ≫ sX) sX (bundleProj E) rfl (k+n)
    (properPushforwardFactorsThroughRationalEquivalence_of_isProper C
      (bundleProj E ≫ sX) sX (bundleProj E) rfl (k+n))

/-- The last coefficient of the actual Chow PBF inverse. -/
def topCoefficient (k : ℤ) :
    letI := hE.isFiniteLocallyFree
    letI := flat_bundleProj E n
    letI := locallyOfFiniteType_bundleProj E n
    chowGroup C (bundleProj E ≫ sX) (k+n) →+ chowGroup C sX (k+n) := by
  letI := hE.isFiniteLocallyFree
  letI := flat_bundleProj E n
  letI := locallyOfFiniteType_bundleProj E n
  exact (Pi.evalAddMonoidHom (fun i : Fin (n+1) => chowGroup C sX (k + (i : ℕ)))
    (Fin.last n)).comp (formulaEquiv E n C sX k).symm.toAddMonoidHom

/-- Proper pushforward of the genuine PBF sum is exactly its last
component. The proof uses actual geometric pushforward theorems. -/
theorem properPush_formulaEquiv (k : ℤ)
    (β : ∀ i : Fin (n+1), chowGroup C sX (k + (i : ℕ))) :
    letI := hE.isFiniteLocallyFree
    letI := flat_bundleProj E n
    letI := locallyOfFiniteType_bundleProj E n
    properPush E n C sX k (formulaEquiv E n C sX k β) = β (Fin.last n) := by
  letI := hE.isFiniteLocallyFree
  letI := flat_bundleProj E n
  letI := locallyOfFiniteType_bundleProj E n
  have hterm (i : Fin (n+1)) :
      properPush E n C sX k
        (bundleTerm C sX (bundleProj E ≫ sX) (bundleProj E) rfl n
          (relativeDimension_bundleProj E n)
          (invCap C (bundleProj E ≫ sX) (bundleTwist E)) k i (β i)) =
      bundleProjection C sX (bundleProj E ≫ sX) (bundleProj E) rfl n
        (relativeDimension_bundleProj E n)
        (invCap C (bundleProj E ≫ sX) (bundleTwist E)) i (k + (i : ℕ))
        (k+n) (by ring) (β i) := rfl
  change properPush E n C sX k
    (bundleMap C sX (bundleProj E ≫ sX) (bundleProj E) rfl n
      (relativeDimension_bundleProj E n)
      (invCap C (bundleProj E ≫ sX) (bundleTwist E)) k β) = _
  rw [bundleMap_apply, map_sum]
  refine (Finset.sum_congr rfl fun i _ => hterm i).trans ?_
  rw [Finset.sum_eq_single (Fin.last n)]
  · exact projectiveBundle_projection_self E n C sX (k+n) (β (Fin.last n))
  · intro i _ hne
    have hi : (i : ℕ) < n := by
      have hlt := i.isLt
      have hn : (i : ℕ) ≠ n := fun h => hne (Fin.ext h)
      omega
    exact projectiveBundle_projection_eq_zero_of_lt E n C sX i hi
      (k + (i : ℕ)) (k+n) (by ring) (β i)
  · simp

/-- The actual inverse-PBF coefficient is actual proper pushforward,
with no cohomological trace compatibility as a hypothesis. -/
theorem topCoefficient_eq_properPush (k : ℤ) :
    letI := hE.isFiniteLocallyFree
    letI := flat_bundleProj E n
    letI := locallyOfFiniteType_bundleProj E n
    topCoefficient E n C sX k = properPush E n C sX k := by
  letI := hE.isFiniteLocallyFree
  letI := flat_bundleProj E n
  letI := locallyOfFiniteType_bundleProj E n
  ext α
  have h := properPush_formulaEquiv E n C sX k ((formulaEquiv E n C sX k).symm α)
  rw [AddEquiv.apply_symm_apply] at h
  exact h.symm

end M9Native.ChowProjectiveCoefficient
