module

public import M9StacksIntegration.GenusNineULiftType0Target

@[expose] public section

/-! Conditional assembly only. The actual original
classifier, its full coarse property, and literal rational-open proof remain
honest intermediate inputs. This does not assert the closed M9 theorem or
the higher-universe standalone goal. All existing providers stay frozen. -/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open AlgebraicGeometry CategoryTheory

namespace M9Native.GenusNineType0PaperEndpoint

variable (B : BigFppfSite.{0}) (hZ : B.Contains integerBase)
    (hC : B.Contains (Spec (.of ℂ)))

/-- The same independently chosen actual smooth-genus-nine native target. -/
abbrev nativeTarget :=
  M9StacksIntegration.GenusNineCoarseOverField.genusNineCoarseSpace B hZ ℂ hC

/-- Its literal original all-test space over the actual complex field. -/
abbrev complexSpace : M9StandaloneDraft.Space ℂ :=
  M9StacksIntegration.AllTestNativeOriginalSpace.originalSpaceOfNative
    ℂ B hC (nativeTarget B hZ hC).obj (nativeTarget B hZ hC).property

/-- Canonical Type-0 coefficient relabeling of this same chosen target. -/
abbrev liftedSpace : M9StandaloneDraft.Space (ULift.{0} ℂ) :=
  GenusNineULiftType0Target.target B hZ hC

/-- The genuine inverse-family transport acts on every original test. -/
abbrev liftedClassifier
    (cC : M9StandaloneDraft.Classifier ℂ 9 (complexSpace B hZ hC).obj) :
    M9StandaloneDraft.Classifier (ULift.{0} ℂ) 9 (liftedSpace B hZ hC).obj :=
  ComplexStandaloneCoefficientTransport.classifier cC

/-- Exact chosen-target complex endpoint, conditional on the separately
produced actual original classifier, full coarseness and literal common open. -/
theorem actualComplex_endpoint
    (cC : M9StandaloneDraft.Classifier ℂ 9 (complexSpace B hZ hC).obj)
    (hcC : M9StandaloneDraft.IsCoarse ℂ cC)
    (hrC : M9StandaloneDraft.RationalOpen ℂ 24 (complexSpace B hZ hC).obj) :
    M9StandaloneDraft.IsCoarse ℂ cC ∧
      M9StandaloneDraft.VarietySpace ℂ (complexSpace B hZ hC) ∧
      M9StandaloneDraft.RationalOpen ℂ 24 (complexSpace B hZ hC).obj :=
  ⟨hcC, GenusNineCoarseVariety.genusNine_variety B hZ ℂ hC, hrC⟩

/-- The actual-complex standalone paper formulation, with the fixed
independently chosen target as witness. This is a conditional assembly. -/
theorem actualComplex_goal
    (cC : M9StandaloneDraft.Classifier ℂ 9 (complexSpace B hZ hC).obj)
    (hcC : M9StandaloneDraft.IsCoarse ℂ cC)
    (hrC : M9StandaloneDraft.RationalOpen ℂ 24 (complexSpace B hZ hC).obj) :
    M9StandaloneDraft.RationalCoarseSpaceGoal ℂ :=
  ⟨complexSpace B hZ hC, cC, actualComplex_endpoint B hZ hC cC hcC hrC⟩

/-- Exact same-target Type-0 lifted endpoint. The field/base comparison,
all-family transport, coarse property and rational-open transport are derived. -/
theorem canonicalULift0_endpoint
    (cC : M9StandaloneDraft.Classifier ℂ 9 (complexSpace B hZ hC).obj)
    (hcC : M9StandaloneDraft.IsCoarse ℂ cC)
    (hrC : M9StandaloneDraft.RationalOpen ℂ 24 (complexSpace B hZ hC).obj) :
    M9StandaloneDraft.IsCoarse (ULift.{0} ℂ) (liftedClassifier B hZ hC cC) ∧
      M9StandaloneDraft.VarietySpace (ULift.{0} ℂ) (liftedSpace B hZ hC) ∧
      M9StandaloneDraft.RationalOpen (ULift.{0} ℂ) 24 (liftedSpace B hZ hC).obj :=
  ⟨ComplexStandaloneCoefficientTransport.isCoarse cC hcC,
    GenusNineULiftType0Target.variety B hZ hC,
    ComplexStandaloneCoefficientTransport.rationalOpen 24 _ hrC⟩

/-- Only the Type-0 specialization of the unchanged proposed draft goal.
No theorem for arbitrary test-scheme universe is asserted. -/
theorem proposedComplex_goal0
    (cC : M9StandaloneDraft.Classifier ℂ 9 (complexSpace B hZ hC).obj)
    (hcC : M9StandaloneDraft.IsCoarse ℂ cC)
    (hrC : M9StandaloneDraft.RationalOpen ℂ 24 (complexSpace B hZ hC).obj) :
    M9StandaloneDraft.ProposedComplexSpaceGoal.{0} :=
  ⟨liftedSpace B hZ hC, liftedClassifier B hZ hC cC,
    canonicalULift0_endpoint B hZ hC cC hcC hrC⟩

end M9Native.GenusNineType0PaperEndpoint
