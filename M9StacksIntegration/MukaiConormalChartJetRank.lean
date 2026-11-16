module

public import M9StacksIntegration.MukaiConormalChartImage

/-! Native value-and-cotangent surjectivity for the original primitive
determinant sections on actual étale charts. It is derived from the
actual projective differential, with no jet-rank or image premise. -/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 4096

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Module

universe u

namespace M9Native.MukaiConormalChartJetRank

open LagrangianGrassmannian LagrangianPluckerQuotient MukaiConormalChartJets

variable (K : Type u) [Field K] [CharZero K] [IsAlgClosed K]
variable (f : chart K ⟶ space K) [Etale f]
variable (hf : f ≫ projection K = chartProjection K)
variable (z : Spec (.of K) ⟶ chart K)
variable (hz : z ≫ chartProjection K = 𝟙 (Spec (.of K)))
variable (e : (Scheme.Modules.pullback f).obj (determinantLine K) ≅
  SheafOfModules.unit (chart K).ringCatSheaf)

include hf in
/-- The original fourteen determinant sections generate their actual
value and all six native cotangent directions at the field point. -/
theorem firstJetMap_surjective :
    Function.Surjective (firstJetMap K z (fun j =>
      e.hom.app ⊤ (pullbackGlobalSections f (determinantLine K) (primitiveSections K j)))) := by
  obtain ⟨i,hp⟩ := MukaiConormalChartRatioData.pivot_exists K f z
  exact MukaiConormalChartLinear.firstJetMap_surjective_of_ratio_data K z
    (MukaiConormalChartFrame.sectionTuple K f e) i
    (MukaiConormalChartRatioData.pointRatio K f z i hp)
    (MukaiConormalChartRatioData.pointBasis K f z e i hp)
    (MukaiConormalChartRatioData.inputDifferential K f hf z e)
    (MukaiConormalChartRatioData.inputDifferential_surjective K f hf z e)
    (MukaiConormalChartRatioData.pivot_ne_zero K f z e i hp)
    (MukaiConormalChartRatioData.ratio_values K f z e i hp)
    (MukaiConormalChartRatioData.ratio_derivatives K f hf z e i hp)

include hf hz in
/-- This is the actual kernel of the original primitive sections and
universal derivatives, identified through the actual conormal map. -/
theorem finrank_ker_firstJetMap :
    finrank K (LinearMap.ker (firstJetMap K z (fun j =>
      e.hom.app ⊤ (pullbackGlobalSections f (determinantLine K) (primitiveSections K j))))) = 7 := by
  rw [← MukaiConormalChartImage.range_formsMap_eq_ker_firstJetMap K f hf z hz e]
  exact MukaiConormalFieldCoordinates.finrank_range_formsMap K (z ≫ f)

end M9Native.MukaiConormalChartJetRank
