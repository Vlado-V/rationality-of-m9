module

public import M9StacksIntegration.LagrangianTransverseProjectiveCanonical
public import M9StacksIntegration.CanonicalDivisorSpan

/-! The original transverse five-row section has positive genus from
its actual nine-dimensional primitive restriction and actual canonical
line comparison. No genus-nine or no-pencil hypothesis is needed. -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096
set_option linter.style.haveILetI false
open AlgebraicGeometry CategoryTheory
universe u

namespace M9Native.LagrangianTransversePositiveGenus
open LagrangianTransverseRestriction LagrangianPluckerQuotient

variable (K : Type u) [Field K] [IsAlgClosed K] [CharZero K]
    (M : Matrix (Fin 5) (Fin 14) K)
    [IsIntegral (curve K M)] [SmoothOfRelativeDimension 1 (curveProjection K M)]

/-- The true original canonical H0 contains the true nine-dimensional
primitive system; native Serre duality identifies its dimension with genus. -/
theorem nine_le_genus (hM : Function.Surjective M.mulVec) :
    9 ≤ genus (curveProjection K M) := by
  let f := curveProjection K M
  let L := LagrangianPrimitiveRestriction.restrictedLine K (inclusion K M)
  letI : Smooth f := SmoothOfRelativeDimension.smooth 1 _
  letI : IsIso ((Scheme.ΓSpecIso (.of K)).inv ≫ f.appTop) :=
    isIso_globalSections_of_isAlgClosed K f
  letI : SheafOfModules.IsInvertible (curve K M).presheaf
      (curve K M).ringCatSheaf.property L := by
    exact LagrangianPluckerGeneration.pulledDeterminantLine_isInvertibleModule K (inclusion K M)
  letI : Module.Finite K (cohomologyOverField K f L 0) :=
    CurveDivisorSections.invertible_cohomology_zero_finite f L
  have hle := Submodule.finrank_le (LinearMap.range
    (LagrangianPrimitiveRestriction.primitiveRestriction K f (inclusion K M)))
  rw [primitiveRestriction_range_finrank K M hM] at hle
  have he := (cohomologyOverFieldIso K f
    (LagrangianTransverseCanonical.restrictedCanonicalIso K M hM) 0).toLinearEquiv.finrank_eq
  have hg := Stacks.Duality.finrank_cohomologyOverField_zero_dualizingSheafOverField f
    (IsCurve.topologicalKrullDim_eq_one (k := K) (f := f)).le
  change Module.finrank K (cohomologyOverField K f L 0) =
    Module.finrank K (cohomologyOverField K f (Stacks.Duality.dualizingSheafOverField f) 0) at he
  change 9 ≤ genus f
  rw [← hg, ← he]
  exact hle

theorem genus_ne_zero (hM : Function.Surjective M.mulVec) :
    genus (curveProjection K M) ≠ 0 := by
  have h := nine_le_genus K M hM
  omega

end M9Native.LagrangianTransversePositiveGenus
