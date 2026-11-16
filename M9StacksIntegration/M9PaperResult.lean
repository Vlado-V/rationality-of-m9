module

public import M9StacksIntegration.GenusNineRationality
public import M9StacksIntegration.AllOriginalChosenCoarseCoarseness
public import M9StacksIntegration.GenusNineType0PaperFieldEndpoint

@[expose] public section

/-! The paper's actual complex genus-nine rational coarse-moduli assertion.
The site is chosen internally. Neither coarse classification, density,
geometry nor a function-field equivalence is a premise of the result. -/

noncomputable section
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory

namespace M9Native.M9PaperResult
open M9StacksIntegration

/-- Choose a real bounded site; the final classifier still covers all
original complex bases and families, with no cutoff in its statement. -/
theorem exists_site : ∃ B : BigFppfSite.{0},
    B.Contains integerBase ∧ B.Contains (Spec (.of ℂ)) := by
  obtain ⟨B, hB⟩ := BigFppfSite.exists_containing
    ({integerBase, Spec (.of ℂ)} : Set Scheme.{0})
  exact ⟨B, hB _ (by simp), hB _ (by simp)⟩

/-- The full paper result on the literal complex field, using the genuine
all-original unpointed genus-nine moduli problem. -/
theorem paper_goal : M9StandaloneDraft.RationalCoarseSpaceGoal ℂ := by
  obtain ⟨B, hZ, hC⟩ := exists_site
  exact GenusNineType0PaperEndpoint.actualComplex_goal B hZ hC
    (AllOriginalChosenCoarseClassifier.classifier B hZ ℂ hC 9 (by decide))
    (AllOriginalChosenCoarseClassifier.isCoarse B hZ ℂ hC 9 (by decide))
    (GenusNineRationality.rationalOpen B hC hZ)

/-- The same chosen actual moduli space also has the structural complex
function-field identity; the field equivalence is constructed by the proof. -/
theorem exists_actual_package :
    ∃ (B : BigFppfSite.{0}) (hZ : B.Contains integerBase)
      (hC : B.Contains (Spec (.of ℂ))),
      M9StandaloneDraft.IsCoarse ℂ
        (AllOriginalChosenCoarseClassifier.classifier B hZ ℂ hC 9 (by decide)) ∧
      M9StandaloneDraft.VarietySpace ℂ (GenusNineType0PaperEndpoint.complexSpace B hZ hC) ∧
      M9StandaloneDraft.RationalOpen ℂ 24 (GenusNineType0PaperEndpoint.complexSpace B hZ hC).obj ∧
      GenusNineType0PaperFieldEndpoint.NativeFieldGoal B hZ hC
        (GenusNineRationality.imageDense B hC hZ) := by
  obtain ⟨B, hZ, hC⟩ := exists_site
  refine ⟨B, hZ, hC, ?_⟩
  exact GenusNineType0PaperFieldEndpoint.chosenComplexPaperPackage B hZ hC
    (AllOriginalChosenCoarseClassifier.classifier B hZ ℂ hC 9 (by decide))
    (AllOriginalChosenCoarseClassifier.isCoarse B hZ ℂ hC 9 (by decide))
    (GenusNineRationality.imageDense B hC hZ) (GenusNineRationality.geometry B hC hZ)

end M9Native.M9PaperResult
