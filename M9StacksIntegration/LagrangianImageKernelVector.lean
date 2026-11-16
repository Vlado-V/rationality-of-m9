module

public import M9StacksIntegration.LagrangianRankTwoSubsystemExistence
public import M9StacksIntegration.MukaiRecognitionHomBound
public import M9StacksIntegration.LagrangianModelRestriction
public import M9StacksIntegration.LagrangianPrimitiveRestrictionInjection

/-! The original three-section subsystem has a genuine nonzero original
vector annihilated by any map of its image into a line with two sections.
The scalar action, image inclusion and original quotient section are retained. -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1200000
set_option maxRecDepth 4096

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Module
open scoped BigOperators
universe u

namespace M9Native.LagrangianImageKernelVector

open LagrangianRankTwoSubsystemBundles LagrangianRankTwoSubsystemExistence
open LagrangianOrderedFibre LagrangianUniversalSections

variable (K : Type u) [Field K] [CharZero K]
  (M : Matrix (Fin 5) (Fin 14) K) (hM : Function.Surjective M.mulVec)

def imageCombination (s : Fin 3 → (Fin 6 → K)) :
    (Fin 3 → K) →ₗ[K] cohomologyOverField K (modelProjection K M hM)
      (imageBundle K M hM s) 0 :=
  Fintype.linearCombination K (imageSections K M hM s)

/-- The actual categorical image inclusion carries the combination to
the original constant vector with the same original coefficients. -/
theorem imageCombination_maps_to_original (s : Fin 3 → (Fin 6 → K)) (a : Fin 3 → K) :
    cohomologyOverFieldMap K (modelProjection K M hM)
      (image.ι (originalMap K M hM s)) 0 (imageCombination K M hM s a) =
        sectionMap K (modelProjection K M hM) (modelInclusion K M hM)
          (Fintype.linearCombination K s a) := by
  simp only [imageCombination, Fintype.linearCombination_apply, map_sum, map_smul,
    imageSections_maps_to_original]

section Curve

variable [IsAlgClosed K] [IsIntegral (model K M hM)]
  [SmoothOfRelativeDimension 1 (modelProjection K M hM)]

/-- Injectivity of the actual original six-section system is derived
from its actual primitive-restriction rank, not from completeness. -/
theorem model_sectionMap_injective : Function.Injective
    (sectionMap K (modelProjection K M hM) (modelInclusion K M hM)) := by
  apply LagrangianPrimitiveRestrictionInjection.universal_sectionMap_injective_of_restriction_rank
    K (modelProjection K M hM) (modelInclusion K M hM) rfl
  rw [LagrangianModelRestriction.primitiveRestriction_range_finrank K M hM]
  norm_num

/-- Dimension three versus two supplies a nonzero original coefficient
vector in the genuine cohomology-map kernel. Its original quotient section
and its image-bundle section are both nonzero, by actual original injectivity. -/
theorem exists_nonzero_original_kernel_vector (s : Fin 3 → (Fin 6 → K))
    (hs : LinearIndependent K s) (ξ : (model K M hM).Modules)
    [SheafOfModules.IsInvertible (model K M hM).presheaf
      (model K M hM).ringCatSheaf.property ξ]
    (g : imageBundle K M hM s ⟶ ξ)
    (hξ : finrank K (cohomologyOverField K (modelProjection K M hM) ξ 0) = 2) :
    ∃ a : Fin 3 → K, a ≠ 0 ∧
      Fintype.linearCombination K s a ≠ 0 ∧ imageCombination K M hM s a ≠ 0 ∧
      cohomologyOverFieldMap K (modelProjection K M hM) g 0
        (imageCombination K M hM s a) = 0 := by
  letI : SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} ξ 1 :=
    SheafOfModules.isFiniteLocallyFreeOfRank_one_of_isInvertible (model K M hM) ξ
  letI := MukaiRecognitionHomBound.finite_bundle_H0 K (modelProjection K M hM) ξ 1
  let φ := (cohomologyOverFieldMap K (modelProjection K M hM) g 0).hom.comp
    (imageCombination K M hM s)
  have hn : ¬ Function.Injective φ := by
    intro h
    have hd := LinearMap.finrank_le_finrank_of_injective (f := φ) h
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_fin, hξ] at hd
    omega
  have hk : LinearMap.ker φ ≠ ⊥ := fun h => hn (LinearMap.ker_eq_bot.mp h)
  obtain ⟨a, ha, hane⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hk
  have horig : Fintype.linearCombination K s a ≠ 0 := by
    have hi := linearIndependent_iff_injective_fintypeLinearCombination.mp hs
    exact fun h => hane (hi (h.trans (map_zero _).symm))
  refine ⟨a, hane, horig, ?_, ha⟩
  intro hz
  have hmap := imageCombination_maps_to_original K M hM s a
  rw [hz, map_zero] at hmap
  exact horig ((model_sectionMap_injective K M hM)
    (hmap.symm.trans (map_zero _).symm))

end Curve
end M9Native.LagrangianImageKernelVector
