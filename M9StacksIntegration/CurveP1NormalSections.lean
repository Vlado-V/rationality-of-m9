module

public import M9StacksIntegration.CurveDerivativeTargetSections
public import M9StacksIntegration.ProjectiveLineTangentCohomology

/-!
# Actual normal sections and target-field quotient for maps to native P1

Every map is the original nonconstant morphism into the original native
relative P1. Target smoothness is derived from the coordinate-pinned
polynomial comparison. Original normal H0 and actual local length are
computed from original cotangent degree and native function-field degree.
The genuine three target vector fields are then removed by the actual
range quotient, when original source cotangent degree is positive.

No numerical cotangent degree, H0 count, quotient identification, or
moduli/Hurwitz dimension is assumed. Specializing the source cotangent
degree to sixteen remains the separate genuine genus-nine provider.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option maxRecDepth 4096

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open M9Native.PencilProjectiveLineGeometry M9Native.CurveTangentLineGeometry
open M9Native.CurveDerivativeNormal M9Native.CurveDerivativeTargetSections

universe u

attribute [local instance] isCurve_projectiveSpaceOver_one

namespace M9Native.CurveP1NormalSections

/-- The original relative projective line is genuinely smooth. -/
theorem line_smooth (k : Type u) [Field k] : Smooth (toBase k) := by
  let c := Stacks.AlgebraicGeometry.ProjBaseChange.polynomialComparison k 1
  exact smooth_of_iso_projectiveLine (toBase k) c.iso c.toBase

attribute [local instance] line_smooth

variable {k : Type u} [Field k] [CharZero k] {X : Scheme.{u}}
variable (f : X ⟶ Spec (.of k)) [IsCurve k f] [IsProper f] [Smooth f]
variable (g : X ⟶ Line k) (hg : g ≫ toBase k = f)
variable (hnc : ¬ ∃ y : Line k, ∀ x : X, g.base x = y)

include hnc

/-- Original normal H0 for the actual map into the actual P1. -/
theorem normal_h0_p1_degree_formula :
    letI := normal_isCoherent f (toBase k) g hg
    letI := differentials_rank_one f
    (Module.finrank k (cohomologyOverField k f (normalSheaf f (toBase k) g hg) 0) : ℤ) =
      curveDegree k f (IsCurve.topologicalKrullDim_eq_one (f := f)).le
        (Scheme.Hom.relativeDifferentials f) 1 +
      2 * (PencilDegreePullback.curveMapDegree f (toBase k) g hg hnc : ℤ) := by
  let := normal_isCoherent f (toBase k) g hg
  let := differentials_rank_one f
  let := differentials_rank_one (toBase k)
  have h := normal_h0_degree_formula f (toBase k) g hg hnc
  rw [ProjectiveLineDifferentialsDegree.line_cotangent_curveDegree k] at h
  linarith

/-- The same formula computes the genuine finite sum of original local lengths. -/
theorem normal_length_p1_degree_formula [IsAlgClosed k] :
    letI := normal_isCoherent f (toBase k) g hg
    letI := differentials_rank_one f
    (ZeroDimensionalCohomologyLength.totalStalkLength f
      (normalSheaf f (toBase k) g hg) (normal_support_le_zero f (toBase k) g hg hnc) : ℤ) =
      curveDegree k f (IsCurve.topologicalKrullDim_eq_one (f := f)).le
        (Scheme.Hom.relativeDifferentials f) 1 +
      2 * (PencilDegreePullback.curveMapDegree f (toBase k) g hg hnc : ℤ) := by
  let := normal_isCoherent f (toBase k) g hg
  let := differentials_rank_one f
  rw [normal_length_eq_h0 f (toBase k) g hg hnc]
  exact normal_h0_p1_degree_formula f g hg hnc

variable [IsAlgClosed k]

/-- Positive actual source differential degree proves that the original
three target fields contribute an actual three-dimensional subspace. -/
theorem target_range_finrank_three
    (hpos : letI := differentials_rank_one f
      0 < curveDegree k f (IsCurve.topologicalKrullDim_eq_one (f := f)).le
        (Scheme.Hom.relativeDifferentials f) 1) :
    Module.finrank k (LinearMap.range (targetNormalSections f (toBase k) g hg)) = 3 := by
  rw [targetNormalSections_range_finrank f (toBase k) g hg hnc
    (tangentH0_subsingleton_of_differential_degree_pos f hpos)]
  exact ProjectiveLineTangentCohomology.line_tangent_h0 k

/-- The original range quotient has the actual degree formula subtracting
three original target vector fields. It is not labelled a moduli tangent. -/
theorem target_quotient_degree_formula
    (hpos : letI := differentials_rank_one f
      0 < curveDegree k f (IsCurve.topologicalKrullDim_eq_one (f := f)).le
        (Scheme.Hom.relativeDifferentials f) 1) :
    letI := differentials_rank_one f
    (Module.finrank k
      ((cohomologyOverField k f (normalSheaf f (toBase k) g hg) 0) ⧸
        LinearMap.range (targetNormalSections f (toBase k) g hg)) : ℤ) =
      curveDegree k f (IsCurve.topologicalKrullDim_eq_one (f := f)).le
        (Scheme.Hom.relativeDifferentials f) 1 +
      2 * (PencilDegreePullback.curveMapDegree f (toBase k) g hg hnc : ℤ) - 3 := by
  let := normal_isCoherent f (toBase k) g hg
  let := differentials_rank_one f
  let hT := tangentH0_subsingleton_of_differential_degree_pos f hpos
  let := finiteDimensional_cohomologyOverField_of_isProper k f
    (normalSheaf f (toBase k) g hg) 0
  have hq := quotient_finrank f (toBase k) g hg hnc hT
  rw [ProjectiveLineTangentCohomology.line_tangent_h0 k] at hq
  have hge : 3 ≤ Module.finrank k
      (cohomologyOverField k f (normalSheaf f (toBase k) g hg) 0) := by
    have h := LinearMap.finrank_le_finrank_of_injective
      (targetNormalSections_injective f (toBase k) g hg hnc hT)
    rw [ProjectiveLineTangentCohomology.line_tangent_h0 k] at h
    exact h
  have hN := normal_h0_p1_degree_formula f g hg hnc
  rw [hq, Int.ofNat_sub hge, hN]
  norm_num

end M9Native.CurveP1NormalSections
