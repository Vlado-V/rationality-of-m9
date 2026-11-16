module

public import M9StacksIntegration.LagrangianNoTrigonalAssembly
public import M9StacksIntegration.LagrangianQuadricIdeal

/-! The ORIGINAL smooth integral transverse five-row curve in LG(3,6)
has no native degree-three pencil. The actual canonical closed immersion,
the full mixed linear/quadratic image ideal, and the positive genus are
derived. The divisor argument retains base points and nilpotents. -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096
open AlgebraicGeometry CategoryTheory
open M9Native.ProjectiveQuadraticCohomology M9Native.ProjectiveQuadraticDimension
universe u

namespace M9Native.LagrangianNoTrigonal

open LagrangianTransverseRestriction

variable (K : Type u) [Field K] [IsAlgClosed K] [CharZero K]
    (M : Matrix (Fin 5) (Fin 14) K)
    [IsIntegral (curve K M)] [SmoothOfRelativeDimension 1 (curveProjection K M)]

/-- No genus, pencil, span, reducedness, or ideal-generation premise is
assumed: the actual LG quadratic ideal discharges the geometric gate. -/
theorem no_g1_three (hM : Function.Surjective M.mulVec) :
    ¬ Nonempty (LinearSeries K (curveProjection K M)
      (LagrangianNoTrigonalAssembly.curveDimension_le_one K M) 3 1) := by
  apply LagrangianNoTrigonalAssembly.no_g1_three_of_polynomial_kernel_eq_quadrics
    K M hM (LagrangianTranslatedQuadricFamily.familyForm K)
  simpa only [LagrangianTranslatedQuadricFamily.familyIdeal,
    HomogeneousEquationIdeal.equationIdeal, quadraticIdeal, polynomialSection_eval,
    projective, twist, Nat.cast_ofNat,
    LagrangianPolynomialPluckerEquivariance.polynomialPlucker] using
      LagrangianQuadricIdeal.polynomialPlucker_ker_eq_familyIdeal K

/-- The same original linear-series type with any proof of the curve's
dimension bound; proof irrelevance changes no geometric data. -/
theorem no_g1_three_at_dimension (hM : Function.Surjective M.mulVec)
    (hdim : topologicalKrullDim (curve K M) ≤ 1) :
    ¬ Nonempty (LinearSeries K (curveProjection K M) hdim 3 1) :=
  no_g1_three K M hM

end M9Native.LagrangianNoTrigonal
