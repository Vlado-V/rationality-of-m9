module

public import M9StacksIntegration.LagrangianChosenCoarseRationality
public import M9StacksIntegration.LagrangianChosenCoarseClassifierGeometryActual
public import M9StacksIntegration.LagrangianChosenCoarsePointCoverage
public import M9StacksIntegration.GenusNineNoFiveDensity

@[expose] public section

/-! Rationality of the independently chosen native genus-nine coarse space.
Actual cover-image avoidance supplies density, the actual LG theorem supplies
orbit-fibre geometry, and the proved invariant-field calculation supplies the
rational open and structural complex function-field equivalence. -/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
attribute [local instance] Space.pointTopology

namespace M9Native.GenusNineRationality
open LagrangianChosenCoarseRationality

variable (B : BigFppfSite) (hC : B.Contains (Spec (.of ℂ)))
  (hZ : B.Contains integerBase)

/-- Actual no-five density and actual Mukai coverage make the true raw
chosen-family map dense, without a supplied density premise. -/
theorem imageDense : ImageDense B hC hZ :=
  LagrangianChosenCoarsePointCoverage.denseRange_of_dense_noFiveLocus ℂ B hC hZ
    (GenusNineNoFiveDensity.locus_dense B hZ ℂ hC)

/-- Invariance and geometric orbit fibres of the actual shifted map. -/
theorem geometry : Geometry B hC hZ :=
  LagrangianChosenCoarseClassifierGeometryActual.classifierGeometry B hC hZ

/-- The literal all-original common rational open of the actual coarse space. -/
theorem rationalOpen :
    M9StandaloneDraft.RationalOpen ℂ 24 (originalSpace B hC hZ).obj :=
  LagrangianChosenCoarseRationality.rationalOpen B hC hZ
    (imageDense B hC hZ) (geometry B hC hZ)

/-- The actual structural complex function field is a pure transcendental
extension in 24 variables; its field comparison is derived. -/
def nativeRationalFieldEquiv :
    letI := Space.functionField B (Spec (.of ℂ)) hC (target B hC hZ).property
      (integral_of_imageDense B hC hZ (imageDense B hC hZ))
    letI := AlgebraicSpaceFunctionFieldScalars.rationalFunctionsBaseAlgebra ℂ B hC
      (target B hC hZ).property (integral_of_imageDense B hC hZ (imageDense B hC hZ))
    Space.rationalFunctions B (Spec (.of ℂ)) hC (target B hC hZ).property ≃ₐ[ℂ]
      M9.RationalField ℂ 24 :=
  LagrangianChosenCoarseRationality.nativeRationalFieldEquiv B hC hZ
    (imageDense B hC hZ) (geometry B hC hZ)

/-- Actual variety, rational open and native function-field rationality,
with no geometric, field-equivalence or rationality premise. -/
theorem rationalityPackage :
    letI := Space.functionField B (Spec (.of ℂ)) hC (target B hC hZ).property
      (integral_of_imageDense B hC hZ (imageDense B hC hZ))
    letI := AlgebraicSpaceFunctionFieldScalars.rationalFunctionsBaseAlgebra ℂ B hC
      (target B hC hZ).property (integral_of_imageDense B hC hZ (imageDense B hC hZ))
    M9StandaloneDraft.VarietySpace ℂ (originalSpace B hC hZ) ∧
      M9StandaloneDraft.RationalOpen ℂ 24 (originalSpace B hC hZ).obj ∧
      Nonempty (Space.rationalFunctions B (Spec (.of ℂ)) hC (target B hC hZ).property ≃ₐ[ℂ]
        M9.RationalField ℂ 24) :=
  LagrangianChosenCoarseRationality.rationalityPackage B hC hZ
    (imageDense B hC hZ) (geometry B hC hZ)

end M9Native.GenusNineRationality
