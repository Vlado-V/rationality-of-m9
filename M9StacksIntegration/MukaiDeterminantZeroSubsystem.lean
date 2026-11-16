module

public import M9StacksIntegration.GrassmannianExteriorKernelPoint
public import M9StacksIntegration.MukaiDeterminantSubsystemKernel
public import M9StacksIntegration.LagrangianOriginalDeterminantRankTwo

/-!
# Existence of an actual determinant-zero original three-subsystem

The original transverse restriction computes rank nine for the actual
exterior determinant evaluation. Genuine projective intersection then
produces an independent triple in the original six-space whose actual
determinant section vanishes. The original section map is injective by
the same proved restriction rank, so its images are an actual independent
three-subsystem of H0. The checked transverse rank theorem gives rank two
everywhere. Neither subsystem existence nor determinant vanishing nor
rank two is a premise. The residual quotient degree is a separate result.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Module

namespace M9Native.MukaiDeterminantZeroSubsystem
open LagrangianOrderedFibre LagrangianUniversalSections LagrangianUniversalTriples
open LagrangianTripleDeterminantSection
open MukaiDeterminantSubsystemKernel
universe u
variable (K : Type u) [Field K] [IsAlgClosed K] [CharZero K]
variable (M : Matrix (Fin 5) (Fin 14) K) (hM : Function.Surjective M.mulVec)

section Ordered
variable [IsIntegral (LagrangianTransverseRestriction.curve K M)]
  [SmoothOfRelativeDimension 1 (LagrangianTransverseRestriction.curveProjection K M)]
include hM

/-- The actual ordered transverse cut itself has an independent ORIGINAL
H0 three-subsystem with identically zero determinant. -/
theorem exists_determinant_zero_triple_on_cut :
    ∃ s : Fin 3 → (Fin 6 → K), LinearIndependent K s ∧
      LinearIndependent K (fun i => sectionMap K
        (LagrangianTransverseRestriction.curveProjection K M)
        (LagrangianTransverseRestriction.inclusion K M) (s i)) ∧
      determinantValue K (LagrangianTransverseRestriction.curveProjection K M)
        (LagrangianTransverseRestriction.inclusion K M) s = 0 := by
  obtain ⟨s, hs, _, hz⟩ := GrassmannianExteriorKernelPoint.exists_independent_triple K
    (determinantMap K M) (range_finrank K M hM)
  have hdet : determinantValue K (LagrangianTransverseRestriction.curveProjection K M)
      (LagrangianTransverseRestriction.inclusion K M) s = 0 := by
    rwa [map_ιMulti_eq_determinantValue] at hz
  have hinj := LagrangianPrimitiveRestrictionInjection.universal_sectionMap_injective_of_restriction_rank K
    (LagrangianTransverseRestriction.curveProjection K M)
    (LagrangianTransverseRestriction.inclusion K M) rfl
    (by rw [LagrangianTransverseRestriction.primitiveRestriction_range_finrank K M hM]; norm_num)
  exact ⟨s, hs, hs.map' _ (LinearMap.ker_eq_bot.mpr hinj), hdet⟩

end Ordered

section Model
variable [IsIntegral (model K M hM)]
  [SmoothOfRelativeDimension 1 (modelProjection K M hM)]

/-- Genuine projective intersection produces the independent original
triple with identically zero ACTUAL determinant section. -/
theorem exists_determinant_zero_triple :
    ∃ s : Fin 3 → (Fin 6 → K), LinearIndependent K s ∧
      exteriorPower.ιMulti K 3 s ≠ 0 ∧
      determinantValue K (modelProjection K M hM) (modelInclusion K M hM) s = 0 := by
  obtain ⟨s, hs, hw, hz⟩ := GrassmannianExteriorKernelPoint.exists_independent_triple K
    (modelDeterminantMap K M hM) (model_range_finrank K M hM)
  refine ⟨s, hs, hw, ?_⟩
  rwa [model_map_ιMulti_eq_determinantValue] at hz

/-- The actual three-subsystem is independent IN THE ORIGINAL H0 and has
rank two everywhere on the original transverse canonical curve. -/
theorem exists_rank_two_subsystem :
    ∃ s : Fin 3 → (Fin 6 → K), LinearIndependent K s ∧
      LinearIndependent K
        (fun i => sectionMap K (modelProjection K M hM) (modelInclusion K M hM) (s i)) ∧
      determinantValue K (modelProjection K M hM) (modelInclusion K M hM) s = 0 ∧
      MukaiSemiIrreducible.EverywhereRank
        (evaluation K (modelProjection K M hM) (modelInclusion K M hM) s) 2 := by
  obtain ⟨s, hs, _, hdet⟩ := exists_determinant_zero_triple K M hM
  have hinj := LagrangianPrimitiveRestrictionInjection.universal_sectionMap_injective_of_restriction_rank K
    (modelProjection K M hM) (modelInclusion K M hM) rfl
    (by rw [LagrangianModelRestriction.primitiveRestriction_range_finrank K M hM]; norm_num)
  have himages := hs.map'
    (sectionMap K (modelProjection K M hM) (modelInclusion K M hM))
    (LinearMap.ker_eq_bot.mpr hinj)
  exact ⟨s, hs, himages, hdet,
    LagrangianOriginalDeterminantRankTwo.everywhereRank_of_determinantValue_eq_zero
      K M hM s hs hdet⟩

end Model

/-- On the actual canonical good open, the original family itself derives
all curve geometry needed by the genuine subsystem existence theorem. -/
theorem exists_rank_two_subsystem_of_goodOpen
    (hg : LagrangianMatrixPointRows.matrixPoint K M hM (IsLocalRing.closedPoint K) ∈
      LagrangianLinearSectionGenericSmooth.goodOpen K) :
    ∃ s : Fin 3 → (Fin 6 → K), LinearIndependent K s ∧
      LinearIndependent K
        (fun i => sectionMap K (modelProjection K M hM) (modelInclusion K M hM) (s i)) ∧
      determinantValue K (modelProjection K M hM) (modelInclusion K M hM) s = 0 ∧
      MukaiSemiIrreducible.EverywhereRank
        (evaluation K (modelProjection K M hM) (modelInclusion K M hM) s) 2 := by
  let : IsIntegral (model K M hM) :=
    LagrangianGoodOpenRestriction.model_integral K M hM hg
  let : SmoothOfRelativeDimension 1 (modelProjection K M hM) :=
    LagrangianGoodOpenRestriction.model_smooth K M hM hg
  exact exists_rank_two_subsystem K M hM

end M9Native.MukaiDeterminantZeroSubsystem
