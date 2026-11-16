module

public import M9StacksIntegration.ProjectiveLineDifferentialsDegree
public import StacksFrontier.AlgebraicGeometry.Picard.CurveLineBundles.RiemannRoch

/-!
# The three original target vector fields on native P1

Actual Euler cohomology computes cotangent degree minus two on the
original relative projective line. Genuine dual evaluation therefore
gives tangent degree two; native line Riemann--Roch gives actual H0
three and actual H1 zero. No cohomology count or degree is supplied.
This is the original sheaf of vector fields; its Lie-group comparison
is not asserted here.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option maxRecDepth 4096

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Stacks.AlgebraicGeometry.ReflexiveModules
open M9Native.PencilProjectiveLineGeometry M9Native.CurveTangentLineGeometry

universe u

attribute [local instance] isCurve_projectiveSpaceOver_one

namespace M9Native.ProjectiveLineTangentCohomology

variable (k : Type u) [Field k]

/-- The literal tangent dual of original native projective-line differentials. -/
abbrev lineTangent : (Line k).Modules := tangentLine (toBase k)

/-- Actual Euler cotangent invertibility and genuine duality give invertibility. -/
theorem line_tangent_isInvertible :
    SheafOfModules.IsInvertible (Line k).presheaf (Line k).ringCatSheaf.2
      (lineTangent k) := by
  have hd := isFiniteLocallyFreeOfRank_dualSheaf
    (Scheme.Hom.relativeDifferentials (toBase k)) 1
      (ProjectiveLineDifferentialsDegree.line_cotangent_rank_one k)
  exact (Stacks.InvertibleRankOneScheme.isInvertibleModule_iff_isFiniteLocallyFreeOfRank_one
    (Line k) _).mpr hd

/-- The original target tangent degree is actually two. -/
theorem line_tangent_degree :
    letI := line_tangent_isInvertible k
    invertibleCurveDegree k (toBase k) (lineDimension k) (lineTangent k) = 2 := by
  let := line_tangent_isInvertible k
  let := ProjectiveLineDifferentialsDegree.line_cotangent_rank_one k
  have h := MukaiDualDegree.curveDegree_dual_line k (toBase k) (lineDimension k)
    (Scheme.Hom.relativeDifferentials (toBase k))
      (ProjectiveLineDifferentialsDegree.line_cotangent_rank_one k)
  rw [ProjectiveLineDifferentialsDegree.line_cotangent_curveDegree k] at h
  rw [invertibleCurveDegree_eq_curveDegree_one]
  simpa using h

variable [IsAlgClosed k]

/-- The original target tangent H1 vanishes by actual positive degree. -/
theorem line_tangent_h1_isZero :
    IsZero (cohomologyOverField k (toBase k) (lineTangent k) 1) := by
  let := line_tangent_isInvertible k
  apply isZero_cohomologyOverField_one_of_two_mul_genus_sub_two_lt_invertibleCurveDegree
    k (toBase k) (lineDimension k) (lineTangent k)
  rw [genus_line_eq_zero k, line_tangent_degree k]
  norm_num

/-- The original native projective line has three actual global vector fields. -/
theorem line_tangent_h0 :
    Module.finrank k (cohomologyOverField k (toBase k) (lineTangent k) 0) = 3 := by
  let := line_tangent_isInvertible k
  have hdeg : 2 * (genus (toBase k) : ℤ) - 2 <
      invertibleCurveDegree k (toBase k) (lineDimension k) (lineTangent k) := by
    rw [genus_line_eq_zero k, line_tangent_degree k]
    norm_num
  have h := finrank_cohomologyOverField_zero_eq_of_two_mul_genus_sub_two_lt_invertibleCurveDegree
    k (toBase k) (lineDimension k) (lineTangent k) hdeg
  rw [line_tangent_degree k, genus_line_eq_zero k] at h
  norm_num at h
  exact_mod_cast h

end M9Native.ProjectiveLineTangentCohomology
