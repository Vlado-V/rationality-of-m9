module

public import M9StacksIntegration.GenusNineType0PaperEndpoint
public import M9StacksIntegration.LagrangianChosenCoarseRationality

@[expose] public section

/-! Conditional paper-field assembly. The native field equivalence is derived from the actual chosen-target
rationality package; no field equivalence is an input. Actual all-original
coarse classification, raw density and shifted classifier geometry remain
honest upstream inputs until the final actual specialization is available. -/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open AlgebraicGeometry CategoryTheory

namespace M9Native.GenusNineType0PaperFieldEndpoint

open GenusNineType0PaperEndpoint

variable (B : BigFppfSite.{0}) (hZ : B.Contains integerBase)
    (hC : B.Contains (Spec (.of ℂ)))

/-- The function-field producer uses exactly the same independently chosen
actual native target as the standalone coarse-space endpoint. -/
theorem native_target_eq :
    LagrangianChosenCoarseRationality.target B hC hZ = nativeTarget B hZ hC := rfl

/-- The genuine native function-field assertion over its actual structural
complex coefficient algebra, with integrality derived from actual density. -/
abbrev NativeFieldGoal (hd : LagrangianChosenCoarseRationality.ImageDense B hC hZ) : Prop :=
  letI := Space.functionField B (Spec (.of ℂ)) hC
    (LagrangianChosenCoarseRationality.target B hC hZ).property
    (LagrangianChosenCoarseRationality.integral_of_imageDense B hC hZ hd)
  letI := AlgebraicSpaceFunctionFieldScalars.rationalFunctionsBaseAlgebra ℂ B hC
    (LagrangianChosenCoarseRationality.target B hC hZ).property
    (LagrangianChosenCoarseRationality.integral_of_imageDense B hC hZ hd)
  Nonempty (Space.rationalFunctions B (Spec (.of ℂ)) hC
    (LagrangianChosenCoarseRationality.target B hC hZ).property ≃ₐ[ℂ]
      M9.RationalField ℂ 24)

/-- The literal chosen-target complex paper package. Every space, family
and geometric point in coarseness is original. Native integrality, finite
type, the common open and the C-algebra field equivalence are derived by
existing producers. No field comparison or rationality premise is supplied. -/
theorem chosenComplexPaperPackage
    (cC : M9StandaloneDraft.Classifier ℂ 9 (complexSpace B hZ hC).obj)
    (hcC : M9StandaloneDraft.IsCoarse ℂ cC)
    (hd : LagrangianChosenCoarseRationality.ImageDense B hC hZ)
    (h : LagrangianChosenCoarseRationality.Geometry B hC hZ) :
    M9StandaloneDraft.IsCoarse ℂ cC ∧
      M9StandaloneDraft.VarietySpace ℂ (complexSpace B hZ hC) ∧
      M9StandaloneDraft.RationalOpen ℂ 24 (complexSpace B hZ hC).obj ∧
      NativeFieldGoal B hZ hC hd :=
  ⟨hcC, GenusNineCoarseVariety.genusNine_variety B hZ ℂ hC,
    LagrangianChosenCoarseRationality.rationalOpen B hC hZ hd h,
    LagrangianChosenCoarseRationality.nonempty_nativeRationalFieldEquiv B hC hZ hd h⟩

/-- Actual-complex rational coarse moduli, the canonical Type-0 lifted
specialization, and the actual native C-function-field identity. This
conditional assembly makes no assertion of a higher-universe draft goal. -/
theorem standalonePaperPackage
    (cC : M9StandaloneDraft.Classifier ℂ 9 (complexSpace B hZ hC).obj)
    (hcC : M9StandaloneDraft.IsCoarse ℂ cC)
    (hd : LagrangianChosenCoarseRationality.ImageDense B hC hZ)
    (h : LagrangianChosenCoarseRationality.Geometry B hC hZ) :
    M9StandaloneDraft.RationalCoarseSpaceGoal ℂ ∧
      M9StandaloneDraft.ProposedComplexSpaceGoal.{0} ∧ NativeFieldGoal B hZ hC hd :=
  ⟨actualComplex_goal B hZ hC cC hcC
      (LagrangianChosenCoarseRationality.rationalOpen B hC hZ hd h),
    proposedComplex_goal0 B hZ hC cC hcC
      (LagrangianChosenCoarseRationality.rationalOpen B hC hZ hd h),
    LagrangianChosenCoarseRationality.nonempty_nativeRationalFieldEquiv B hC hZ hd h⟩

end M9Native.GenusNineType0PaperFieldEndpoint
