module

public import M9StacksIntegration.LagrangianFreeFiveResidualSections
public import M9StacksIntegration.LagrangianRankOneQuotientBound
public import M9StacksIntegration.LinearSeriesAddEffectiveDivisor

/-!
# The actual xi-to-alpha branch in the genuinely free degree-five case

Actual free-pencil geometry proves complete H0(alpha)=3. The original
line-map exact sequence and H0(xi)=2 imply that the original six-section
image in the actual cokernel has rank at most one. Its genuine quotient
map therefore satisfies the derived hyperplane H0 bound two. Native
line-map cohomology computes the same full cokernel's H0 as three from
the actual degree difference. This excludes every nonzero xi-to-alpha
map without a chosen divisor, hyperplane, section containment, length,
zero-scheme comparison or complete-original-system premise.

The separate minimal free degree-four case is not asserted.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
set_option maxRecDepth 4096

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Module
open M9Native.MukaiBundle M9Native.MukaiBundleDeterminant

universe u

namespace M9Native.LagrangianFreeFiveAlphaHomZero

open LagrangianOrderedFibre LagrangianUniversalSections
open LagrangianRankTwoSubsystemBundles LagrangianRankTwoQuotientSections
open LagrangianFreeFiveResidualSections

variable (K : Type u) [Field K] [IsAlgClosed K] [CharZero K]
  (M : Matrix (Fin 5) (Fin 14) K) (hM : Function.Surjective M.mulVec)
  [IsIntegral (model K M hM)]
  [SmoothOfRelativeDimension 1 (modelProjection K M hM)]
  (s : Fin 3 → (Fin 6 → K)) (hs : LinearIndependent K s)
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
  (h2 : finrank K (cohomologyOverField K (modelProjection K M hM) ξ 0) = 2)
  (t : ULift.{u} (Fin 2) → ξ.sections)
  (ht : Epi (MukaiPencilQuotient.pencilEvaluation ξ t))

/-- The original categorical quotient to the actual line-map cokernel. -/
abbrev quotientToCokernel (g : ξ ⟶ alpha K M hM s) :
    bundle K (modelInclusion K M hM) ⟶ cokernel g :=
  cokernel.π (originalMap K M hM s) ≫ cokernel.π g

include hs hr hg hno3 hβ hξ h2 ht

/-- The true original image in the actual cokernel has rank at most one. -/
theorem cokernel_original_image_rank_le_one (g : ξ ⟶ alpha K M hM s) (hg0 : g ≠ 0) :
    finrank K (LinearMap.range
      (LagrangianRankOneQuotientHyperplane.originalQuotientSections K
        (modelProjection K M hM) (modelInclusion K M hM)
        (quotientToCokernel K M hM s ξ g))) ≤ 1 := by
  let := model_locallyNoetherian K M hM
  let := alpha_isInvertible K M hM s hr
  let := SheafOfModules.isFiniteLocallyFreeOfRank_one_of_isInvertible (model K M hM)
    (alpha K M hM s)
  let := SheafOfModules.isFiniteLocallyFreeOfRank_one_of_isInvertible (model K M hM) ξ
  let := MukaiRecognitionHomBound.finite_bundle_H0 K (modelProjection K M hM)
    (alpha K M hM s) 1
  let := MukaiRecognitionHomBound.finite_bundle_H0 K (modelProjection K M hM) ξ 1
  let := LineMapCokernelCohomology.mono_of_ne_zero g hg0
  let := LineMapCokernelCohomology.cokernel_isCoherent g
  let := finiteDimensional_cohomologyOverField_of_isProper K (modelProjection K M hM)
    (cokernel g) 0
  have hinj := M9StacksIntegration.LinearSeriesAddEffectiveDivisor.injective_cohomology_zero_of_mono
    (modelProjection K M hM) g
  obtain ⟨_, _, he, _, _⟩ := exists_cohomologyOverField_longExactSequence K
    (modelProjection K M hM) (LineMapCokernelCohomology.cokernel_shortExact g hg0)
  have hex : Function.Exact
      (cohomologyOverFieldMap K (modelProjection K M hM) g 0).hom
      (cohomologyOverFieldMap K (modelProjection K M hM) (cokernel.π g) 0).hom := he 0
  have hker : finrank K (LinearMap.ker
      (cohomologyOverFieldMap K (modelProjection K M hM) (cokernel.π g) 0).hom) = 2 := by
    rw [hex.linearMap_ker_eq, LinearMap.finrank_range_of_inj hinj, h2]
  have hn := ((cohomologyOverFieldMap K (modelProjection K M hM)
    (cokernel.π g) 0).hom).finrank_range_add_finrank_ker
  rw [hker, alpha_h0_eq_three K M hM s hs hr hg hno3 ξ hβ hξ t ht] at hn
  have hrange : LinearMap.range
      (LagrangianRankOneQuotientHyperplane.originalQuotientSections K
        (modelProjection K M hM) (modelInclusion K M hM)
        (quotientToCokernel K M hM s ξ g)) ≤
      LinearMap.range (cohomologyOverFieldMap K (modelProjection K M hM) (cokernel.π g) 0).hom := by
    rintro y ⟨v,rfl⟩
    refine ⟨alphaSections K M hM s v,?_⟩
    simp only [LagrangianRankOneQuotientHyperplane.originalQuotientSections,
      quotientToCokernel, cohomologyOverFieldMap_comp, ModuleCat.hom_comp,
      LinearMap.comp_apply, alphaSections]
    rfl
  have hle := Submodule.finrank_mono hrange
  omega

/-- Full original section-zero geometry excludes the free-five xi-to-alpha branch. -/
theorem hom_eq_zero (g : ξ ⟶ alpha K M hM s) : g = 0 := by
  let := model_locallyNoetherian K M hM
  let := model_isCurve K M hM
  let := isIso_globalSections_of_isAlgClosed K (modelProjection K M hM)
  let := alpha_isInvertible K M hM s hr
  let := beta_isInvertible K M hM s hr
  by_contra hg0
  let := LineMapCokernelCohomology.cokernel_isCoherent g
  have hbound := LagrangianRankOneQuotientBound.quotient_H0_le_two K M hM
    (quotientToCokernel K M hM s ξ g)
    (cokernel_original_image_rank_le_one K M hM s hs hr hg hno3 ξ hβ hξ h2 t ht g hg0)
  have hA := MukaiFreeFiveResidualSections.other_degree_eight K (modelProjection K M hM)
    (dimension_le_one K M hM) hg (alpha K M hM s) (beta K M hM s)
    (MukaiTensorLineCancellation.tensorSwap (alpha K M hM s) (beta K M hM s) ≪≫
      betaTensorAlphaCanonicalIso K M hM s hr) hβ
  have hlength := LineMapCokernelCohomology.cokernel_h0_eq_degree_jump K
    (modelProjection K M hM) (dimension_le_one K M hM) g hg0
  rw [hA,hξ] at hlength
  omega

end M9Native.LagrangianFreeFiveAlphaHomZero
