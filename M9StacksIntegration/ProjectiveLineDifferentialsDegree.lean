module

public import M9StacksIntegration.ProjectiveLineDifferentialsCohomology
public import M9StacksIntegration.PencilProjectiveLineGeometry
public import M9StacksIntegration.CurveTangentLineGeometry
public import StacksFrontier.AlgebraicGeometry.Morphisms.Differentials.BaseChange

/-!
# Degree minus two for the actual native projective-line cotangent bundle

The native polynomial comparison transports the actual Euler-sequence
cohomology to `projectiveSpaceOver 1 (Spec k)`. Smoothness derives the
invertibility needed by the native degree definition. Thus the original
relative differentials have degree minus two, with no degree or canonical
comparison supplied as an input.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option maxRecDepth 4096

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open Stacks.AlgebraicGeometry.ProjPolyChart (polyGrading projToSpecCoeff)
open M9Native.PencilProjectiveLineGeometry

universe u

attribute [local instance] MvPolynomial.gradedAlgebra isCurve_projectiveSpaceOver_one

namespace M9Native.ProjectiveLineDifferentialsDegree

variable (k : Type u) [Field k]

/-- The actual base-change comparison for the original relative differentials,
along the original native polynomial-model isomorphism. -/
def polynomialPullbackIso :
    (Scheme.Modules.pullback
      (Stacks.AlgebraicGeometry.ProjBaseChange.polynomialComparison k 1).iso.hom).obj
        (Scheme.Hom.relativeDifferentials (projToSpecCoeff k 1)) ≅
      Scheme.Hom.relativeDifferentials (toBase k) := by
  let c := Stacks.AlgebraicGeometry.ProjBaseChange.polynomialComparison k 1
  have hbase : c.iso.hom ≫ projToSpecCoeff k 1 = toBase k := c.toBase
  have h : IsPullback c.iso.hom (toBase k) (projToSpecCoeff k 1)
      (𝟙 (Spec (.of k))) :=
    IsPullback.of_horiz_isIso ⟨by simpa only [Category.comp_id] using hbase⟩
  have := Scheme.Hom.isIso_relativeDifferentialsMap_of_isPullback
    c.iso.hom (toBase k) (projToSpecCoeff k 1) (𝟙 _) h
  exact asIso (Scheme.Hom.relativeDifferentialsMap c.iso.hom
    (projToSpecCoeff k 1) (toBase k) (𝟙 _) h.w)

theorem line_cotangent_cohomology_finrank (n : ℕ) :
    Module.finrank k (cohomologyOverField k (toBase k)
      (Scheme.Hom.relativeDifferentials (toBase k)) n) = if n = 1 then 1 else 0 := by
  let c := Stacks.AlgebraicGeometry.ProjBaseChange.polynomialComparison k 1
  have hbase : c.iso.hom ≫ projToSpecCoeff k 1 = toBase k := c.toBase
  have hp := finrank_cohomologyOverField_pullback k c.iso.hom (projToSpecCoeff k 1)
    (Scheme.Hom.relativeDifferentials (projToSpecCoeff k 1)) n
  rw [hbase] at hp
  exact (cohomologyOverFieldIso k (toBase k) (polynomialPullbackIso k) n).toLinearEquiv.finrank_eq.symm.trans
    (hp.trans (ProjectiveLineDifferentialsCohomology.cotangent_cohomology_finrank k n))

theorem line_unit_cohomology_finrank (n : ℕ) :
    Module.finrank k (cohomologyOverField k (toBase k)
      (SheafOfModules.unit (Line k).ringCatSheaf) n) = if n = 0 then 1 else 0 := by
  let c := Stacks.AlgebraicGeometry.ProjBaseChange.polynomialComparison k 1
  have hbase : c.iso.hom ≫ projToSpecCoeff k 1 = toBase k := c.toBase
  have hp := finrank_cohomologyOverField_unit_pushforward k c.iso.hom
    (projToSpecCoeff k 1) n
  rw [hbase] at hp
  exact hp.trans (ProjectiveLineDifferentialsCohomology.unit_cohomology_finrank k n)

/-- The invertibility comes from the actual projective line being a smooth curve. -/
theorem line_cotangent_isInvertible :
    SheafOfModules.IsInvertible (Line k).presheaf (Line k).ringCatSheaf.property
      (Scheme.Hom.relativeDifferentials (toBase k)) := by
  let c := Stacks.AlgebraicGeometry.ProjBaseChange.polynomialComparison k 1
  let : Smooth (toBase k) := smooth_of_iso_projectiveLine (toBase k) c.iso c.toBase
  exact CurveTangentLineGeometry.differentials_isInvertible (toBase k)

theorem line_cotangent_rank_one :
    SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u}
      (Scheme.Hom.relativeDifferentials (toBase k)) 1 := by
  let := line_cotangent_isInvertible k
  exact SheafOfModules.isFiniteLocallyFreeOfRank_one_of_isInvertible (Line k) _

/-- The original native cotangent line has degree minus two. -/
theorem line_cotangent_degree :
    letI := line_cotangent_isInvertible k
    invertibleCurveDegree k (toBase k) (lineDimension k)
      (Scheme.Hom.relativeDifferentials (toBase k)) = -2 := by
  let := line_cotangent_isInvertible k
  unfold invertibleCurveDegree
  simp_rw [line_cotangent_cohomology_finrank, line_unit_cohomology_finrank]
  rw [finsum_eq_single _ 1 (fun n hn => by simp [hn]),
    finsum_eq_single _ 0 (fun n hn => by simp [hn])]
  norm_num

theorem line_cotangent_curveDegree :
    letI := line_cotangent_rank_one k
    curveDegree k (toBase k) (lineDimension k)
      (Scheme.Hom.relativeDifferentials (toBase k)) 1 = -2 := by
  let := line_cotangent_isInvertible k
  let := line_cotangent_rank_one k
  rw [← invertibleCurveDegree_eq_curveDegree_one]
  exact line_cotangent_degree k

end M9Native.ProjectiveLineDifferentialsDegree
