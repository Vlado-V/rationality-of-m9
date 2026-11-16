module

public import M9StacksIntegration.MukaiFreeFiveResidualSections
public import M9StacksIntegration.LagrangianRankTwoQuotientSections
public import M9StacksIntegration.LineMapCokernelCohomology

/-!
# The original quotient sections are complete in the genuine free-five case

The complete residual section count is derived from the actual free-pencil
inequality, native degrees and no degree-three pencil. The original image
dimension three was independently derived from actual Semi3 geometry.
Together these prove surjectivity of the original six-section quotient,
and hence the actual lifting of every pencil section. This supplies the
containment missing from the paper's abbreviated free-five argument.

No assertion covers a degree-five pencil with a degree-four moving part.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Module
open M9Native.MukaiBundle M9Native.MukaiBundleDeterminant

universe u

namespace M9Native.LagrangianFreeFiveResidualSections

open LagrangianOrderedFibre LagrangianUniversalSections
open LagrangianRankTwoSubsystemBundles LagrangianRankTwoQuotientSections

variable (K : Type u) [Field K] [IsAlgClosed K] [CharZero K]
  (M : Matrix (Fin 5) (Fin 14) K) (hM : Function.Surjective M.mulVec)
  [IsIntegral (model K M hM)]
  [SmoothOfRelativeDimension 1 (modelProjection K M hM)]

abbrev dimension_le_one : topologicalKrullDim (model K M hM) ≤ 1 :=
  (topologicalKrullDim_eq_of_smoothOfRelativeDimension (modelProjection K M hM) 1).le

variable (s : Fin 3 → (Fin 6 → K)) (hs : LinearIndependent K s)
  (hr : MukaiSemiIrreducible.EverywhereRank (originalMap K M hM s) 2)
  (hg : genus (modelProjection K M hM) = 9)
  (hno3 : ¬ Nonempty (LinearSeries K (modelProjection K M hM)
    (dimension_le_one K M hM) 3 1))
  (ξ : (model K M hM).Modules)
  [SheafOfModules.IsInvertible (model K M hM).presheaf
    (model K M hM).ringCatSheaf.2 ξ]
  (hβ : letI := beta_isInvertible K M hM s hr
    invertibleCurveDegree K (modelProjection K M hM) (dimension_le_one K M hM)
      (beta K M hM s) = 8)
  (hξ : invertibleCurveDegree K (modelProjection K M hM)
    (dimension_le_one K M hM) ξ = 5)
  (t : ULift.{u} (Fin 2) → ξ.sections)
  (ht : Epi (MukaiPencilQuotient.pencilEvaluation ξ t))

include hs hr hg hno3 hβ hξ ht

/-- Complete H0(alpha)=3 follows from genuine free-five geometry and original W3. -/
theorem alpha_h0_eq_three :
    finrank K (cohomologyOverField K (modelProjection K M hM) (alpha K M hM s) 0) = 3 := by
  let := model_isCurve K M hM
  let := isIso_globalSections_of_isAlgClosed K (modelProjection K M hM)
  let := alpha_isInvertible K M hM s hr
  let := beta_isInvertible K M hM s hr
  let := SheafOfModules.isFiniteLocallyFreeOfRank_one_of_isInvertible (model K M hM)
    (alpha K M hM s)
  let := MukaiRecognitionHomBound.finite_bundle_H0 K (modelProjection K M hM)
    (alpha K M hM s) 1
  have hh := (MukaiFreeFiveResidualSections.residual_h0_bounds K
    (modelProjection K M hM) (dimension_le_one K M hM) hg hno3
    (alpha K M hM s) (beta K M hM s) ξ
    (MukaiTensorLineCancellation.tensorSwap (alpha K M hM s) (beta K M hM s) ≪≫
      betaTensorAlphaCanonicalIso K M hM s hr) hβ hξ t ht).1
  have hW := (LinearMap.range (alphaSections K M hM s)).finrank_le
  rw [alphaSections_range_finrank K M hM s hs hr] at hW
  omega

/-- The original six quotient sections are genuinely onto complete H0(alpha). -/
theorem alphaSections_surjective : Function.Surjective (alphaSections K M hM s) := by
  let := alpha_isInvertible K M hM s hr
  let := SheafOfModules.isFiniteLocallyFreeOfRank_one_of_isInvertible (model K M hM)
    (alpha K M hM s)
  let := MukaiRecognitionHomBound.finite_bundle_H0 K (modelProjection K M hM)
    (alpha K M hM s) 1
  apply LinearMap.range_eq_top.mp
  apply Submodule.eq_top_of_finrank_eq
  rw [alphaSections_range_finrank K M hM s hs hr,
    alpha_h0_eq_three K M hM s hs hr hg hno3 ξ hβ hξ t ht]

/-- Every actual section of xi maps into the original six-section image. -/
theorem pencil_sections_lift (g : ξ ⟶ alpha K M hM s)
    (a : cohomologyOverField K (modelProjection K M hM) ξ 0) :
    ∃ v : Fin 6 → K, alphaSections K M hM s v =
      (cohomologyOverFieldMap K (modelProjection K M hM) g 0) a :=
  alphaSections_surjective K M hM s hs hr hg hno3 ξ hβ hξ t ht _

end M9Native.LagrangianFreeFiveResidualSections
