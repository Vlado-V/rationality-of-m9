module

public import M9StacksIntegration.CanonicalLineCohomology
public import M9StacksIntegration.Private.CurveCanonicalInvertibility
public import StacksFrontier.AlgebraicGeometry.Curves.VanishingResults.DualizingSheafSmoothCurve
public import StacksFrontier.AlgebraicGeometry.Variety.Curve.SmoothRelativeDimension
public import StacksFrontier.AlgebraicGeometry.EulerCharIso.Basic
public import StacksFrontier.AlgebraicGeometry.Picard.CurveLineBundles.RiemannRoch

/-!
# The original canonical and cotangent lines of a smooth proper curve

The native diagonal/Koszul duality theorem supplies an actual sheaf
isomorphism from `H⁻¹(fˣO)` to the original relative differentials. Its
cohomology comparison is linear for the original field action. The
canonical-line degree calculation therefore gives the actual cotangent
degree `2g-2`; no comparison isomorphism or degree is supplied as input.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option maxRecDepth 4096

open AlgebraicGeometry CategoryTheory
open Stacks.Duality (dualizingSheafOverField)

universe u

namespace M9Native.SmoothCurveCanonicalDifferentials

variable {k : Type u} [Field k] {X : Scheme.{u}}
variable (f : X ⟶ Spec (.of k)) [IsCurve k f] [IsProper f] [Smooth f]

/-- The native diagonal duality theorem, at the literal original sheaves. -/
def canonicalDifferentialsIso :
    dualizingSheafOverField f ≅ Scheme.Hom.relativeDifferentials f := by
  let := smoothOfRelativeDimension_one_of_isCurve k f
  exact (Stacks.Duality.nonempty_dualizingSheafOverField_iso_relativeDifferentials f).some

/-- The comparison preserves the actual base-field scalars in every cohomological degree. -/
def canonicalDifferentialsCohomologyEquiv (n : ℕ) :
    cohomologyOverField k f (dualizingSheafOverField f) n ≃ₗ[k]
      cohomologyOverField k f (Scheme.Hom.relativeDifferentials f) n :=
  (cohomologyOverFieldIso k f (canonicalDifferentialsIso f) n).toLinearEquiv

theorem canonicalDifferentialsCohomologyEquiv_smul (n : ℕ) (a : k)
    (s : cohomologyOverField k f (dualizingSheafOverField f) n) :
    canonicalDifferentialsCohomologyEquiv f n (a • s) =
      a • canonicalDifferentialsCohomologyEquiv f n s :=
  (canonicalDifferentialsCohomologyEquiv f n).map_smul a s

/-- Actual canonical invertibility and the genuine comparison derive cotangent invertibility. -/
theorem differentials_isInvertible :
    SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.property
      (Scheme.Hom.relativeDifferentials f) := by
  let := CurveCanonicalInvertibility.dualizing_isInvertible f
  exact Stacks.SheafOfModules.isInvertible_of_iso _ _ (canonicalDifferentialsIso f)

theorem differentials_rank_one :
    SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u}
      (Scheme.Hom.relativeDifferentials f) 1 := by
  let := differentials_isInvertible f
  exact SheafOfModules.isFiniteLocallyFreeOfRank_one_of_isInvertible X _

section ConstantFunctions

variable [IsIso ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop)]

/-- The actual relative-differential line has degree `2g-2`. -/
theorem differentials_degree (hdim : topologicalKrullDim X ≤ 1) :
    letI := differentials_isInvertible f
    invertibleCurveDegree k f hdim (Scheme.Hom.relativeDifferentials f) =
      2 * (genus f : ℤ) - 2 := by
  let := differentials_isInvertible f
  let := CurveCanonicalInvertibility.dualizing_isInvertible f
  rw [← invertibleCurveDegree_eq_of_iso k f hdim (canonicalDifferentialsIso f)]
  exact CanonicalLineCohomology.canonical_degree f hdim

/-- The same degree statement in the original native finite-locally-free degree API. -/
theorem differentials_curveDegree (hdim : topologicalKrullDim X ≤ 1) :
    letI := differentials_rank_one f
    curveDegree k f hdim (Scheme.Hom.relativeDifferentials f) 1 =
      2 * (genus f : ℤ) - 2 := by
  let := differentials_isInvertible f
  let := differentials_rank_one f
  rw [← invertibleCurveDegree_eq_curveDegree_one]
  exact differentials_degree f hdim

theorem differentials_degree_genus_zero (hdim : topologicalKrullDim X ≤ 1)
    (hg : genus f = 0) :
    letI := differentials_isInvertible f
    invertibleCurveDegree k f hdim (Scheme.Hom.relativeDifferentials f) = -2 := by
  have h := differentials_degree f hdim
  rw [hg] at h
  norm_num at h
  exact h

theorem differentials_degree_genus_nine (hdim : topologicalKrullDim X ≤ 1)
    (hg : genus f = 9) :
    letI := differentials_isInvertible f
    invertibleCurveDegree k f hdim (Scheme.Hom.relativeDifferentials f) = 16 := by
  have h := differentials_degree f hdim
  rw [hg] at h
  norm_num at h
  exact h

end ConstantFunctions

variable [IsAlgClosed k]

/-- Over an algebraically closed field the original integral curve supplies
the constant-function comparison itself. -/
theorem differentials_degree_of_isAlgClosed (hdim : topologicalKrullDim X ≤ 1) :
    letI := differentials_isInvertible f
    invertibleCurveDegree k f hdim (Scheme.Hom.relativeDifferentials f) =
      2 * (genus f : ℤ) - 2 := by
  let := isIso_globalSections_of_isAlgClosed k f
  exact differentials_degree f hdim

theorem differentials_curveDegree_of_isAlgClosed (hdim : topologicalKrullDim X ≤ 1) :
    letI := differentials_rank_one f
    curveDegree k f hdim (Scheme.Hom.relativeDifferentials f) 1 =
      2 * (genus f : ℤ) - 2 := by
  let := isIso_globalSections_of_isAlgClosed k f
  exact differentials_curveDegree f hdim

theorem differentials_degree_genus_zero_of_isAlgClosed (hdim : topologicalKrullDim X ≤ 1)
    (hg : genus f = 0) :
    letI := differentials_isInvertible f
    invertibleCurveDegree k f hdim (Scheme.Hom.relativeDifferentials f) = -2 := by
  have h := differentials_degree_of_isAlgClosed f hdim
  rw [hg] at h
  norm_num at h
  exact h

theorem differentials_degree_genus_nine_of_isAlgClosed (hdim : topologicalKrullDim X ≤ 1)
    (hg : genus f = 9) :
    letI := differentials_isInvertible f
    invertibleCurveDegree k f hdim (Scheme.Hom.relativeDifferentials f) = 16 := by
  have h := differentials_degree_of_isAlgClosed f hdim
  rw [hg] at h
  norm_num at h
  exact h

end M9Native.SmoothCurveCanonicalDifferentials
