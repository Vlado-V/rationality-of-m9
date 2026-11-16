module

public import M9StacksIntegration.MukaiSubsystemSemiExclusions
public import M9StacksIntegration.LagrangianRankTwoQuotientSections
public import M9StacksIntegration.LagrangianImageKernelVector

/-!
# Original-system pair/four exclusions and the actual image Hom vanishing

The original six-space injects by the actual primitive restriction rank.
Its literal native section range consequently has dimension six and
satisfies the proved subsystem Semi3 theorem. Pair and four-section
rank exclusions use only this range. The genuine three-generator image
therefore has no map to the structure sheaf, without a complete-H0,
residual-degree, or pentagonal hypothesis.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Module
open M9Native.MukaiBundle M9Native.MukaiBundleDeterminant

universe u

namespace M9Native.LagrangianOriginalSubsystemExclusions

open LagrangianOrderedFibre LagrangianUniversalSections
open LagrangianRankTwoSubsystemBundles LagrangianRankTwoSubsystemExistence

variable (K : Type u) [Field K] [IsAlgClosed K] [CharZero K]
  (M : Matrix (Fin 5) (Fin 14) K) (hM : Function.Surjective M.mulVec)
  [IsIntegral (model K M hM)]
  [SmoothOfRelativeDimension 1 (modelProjection K M hM)]

/-- Dimension six of the literal original section range follows from
the proved original injection, not from completeness of H0(Q). -/
theorem originalSubsystem_finrank :
    finrank K (LagrangianOriginalSubsystemSemi.originalSubsystem K M hM) = 6 := by
  change finrank K (LinearMap.range
    (sectionMap K (modelProjection K M hM) (modelInclusion K M hM))) = 6
  rw [LinearMap.finrank_range_of_inj (LagrangianImageKernelVector.model_sectionMap_injective K M hM)]
  simp

/-- Every independent pair of ORIGINAL constant vectors has genuine
quotient-evaluation rank at least two at some actual point. -/
theorem original_pair_rank_exclusion (s : Fin 2 → (Fin 6 → K)) (hs : LinearIndependent K s) :
    ∃ x : model K M hM, 2 ≤ MukaiSemiIrreducible.mapRankAt
      (MukaiSemiIrreducible.evaluation K (modelProjection K M hM)
        (bundle K (modelInclusion K M hM))
        (fun i => sectionMap K (modelProjection K M hM) (modelInclusion K M hM) (s i))) x := by
  let : Smooth (modelProjection K M hM) := SmoothOfRelativeDimension.smooth 1 _
  let := bundle_rank K (modelInclusion K M hM)
  have hli : LinearIndependent K
      (fun i => sectionMap K (modelProjection K M hM) (modelInclusion K M hM) (s i)) :=
    hs.map' (sectionMap K (modelProjection K M hM) (modelInclusion K M hM))
      (LinearMap.ker_eq_bot.mpr (LagrangianImageKernelVector.model_sectionMap_injective K M hM))
  exact MukaiSubsystemSemiExclusions.pair_rank_exclusion_of_semi K (modelProjection K M hM)
    (bundle K (modelInclusion K M hM)) (LagrangianOriginalSubsystemSemi.originalSubsystem K M hM)
    (originalSubsystem_finrank K M hM) (LagrangianOriginalSubsystemSemi.originalSubsystem_semi K M hM)
    _ hli (fun i => ⟨s i, rfl⟩)

/-- The generic four-section exclusion is specialized to the same
original six-space, using the independently proved subsystem theorem. -/
theorem original_four_rank_exclusion (s : Fin 4 → (Fin 6 → K)) (hs : LinearIndependent K s) :
    ∃ x : model K M hM, 3 ≤ MukaiSemiIrreducible.mapRankAt
      (MukaiSemiIrreducible.evaluation K (modelProjection K M hM)
        (bundle K (modelInclusion K M hM))
        (fun i => sectionMap K (modelProjection K M hM) (modelInclusion K M hM) (s i))) x := by
  let : IsProper (modelProjection K M hM) := model_proper K M hM
  let := bundle_rank K (modelInclusion K M hM)
  have hli : LinearIndependent K
      (fun i => sectionMap K (modelProjection K M hM) (modelInclusion K M hM) (s i)) :=
    hs.map' (sectionMap K (modelProjection K M hM) (modelInclusion K M hM))
      (LinearMap.ker_eq_bot.mpr (LagrangianImageKernelVector.model_sectionMap_injective K M hM))
  exact LagrangianRankTwoQuotientSections.four_rank_exclusion_of_semi K (modelProjection K M hM)
    (bundle K (modelInclusion K M hM)) (LagrangianOriginalSubsystemSemi.originalSubsystem K M hM)
    (LagrangianOriginalSubsystemSemi.originalSubsystem_semi K M hM) _ hli (fun i => ⟨s i, rfl⟩)

/-- The literal categorical image of an independent original triple,
when its actual rank is two everywhere, has no map to the original
structure sheaf. All original generation and section-range data are
derived, with no full H0 or residual-degree premise. -/
theorem image_hom_unit_eq_zero (s : Fin 3 → (Fin 6 → K)) (hs : LinearIndependent K s)
    (hr : MukaiSemiIrreducible.EverywhereRank (originalMap K M hM s) 2) :
    ∀ p : imageBundle K M hM s ⟶ structureModule (model K M hM), p = 0 := by
  let : IsProper (modelProjection K M hM) := model_proper K M hM
  let : IsCurve K (modelProjection K M hM) := model_isCurve K M hM
  let : Smooth (modelProjection K M hM) := SmoothOfRelativeDimension.smooth 1 _
  let := bundle_rank K (modelInclusion K M hM)
  let : SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} (imageBundle K M hM s) 2 :=
    (ranks K M hM s hr).2.1
  have hli : LinearIndependent K
      (fun i => sectionMap K (modelProjection K M hM) (modelInclusion K M hM) (s i)) :=
    hs.map' (sectionMap K (modelProjection K M hM) (modelInclusion K M hM))
      (LinearMap.ker_eq_bot.mpr (LagrangianImageKernelVector.model_sectionMap_injective K M hM))
  have hu := imageSections_independent K M hM s hli
  have hepi : Epi (MukaiSemiIrreducible.evaluation K (modelProjection K M hM)
      (imageBundle K M hM s) (imageSections K M hM s)) := by
    change Epi (MukaiSemiIrreducible.evaluation K (modelProjection K M hM)
      (RankTwoSubsystemBundles.imageBundle (originalMap K M hM s))
      (RankTwoSubsystemWedge.imageSections K (modelProjection K M hM) (originalMap K M hM s)))
    rw [RankTwoSubsystemWedge.imageSections_evaluation]
    infer_instance
  have huA (i : Fin 3) : cohomologyOverFieldMap K (modelProjection K M hM)
      (image.ι (originalMap K M hM s)) 0 (imageSections K M hM s i) ∈
        LagrangianOriginalSubsystemSemi.originalSubsystem K M hM := by
    rw [imageSections_maps_to_original K M hM s i]
    exact ⟨s i, rfl⟩
  intro p
  exact MukaiSubsystemSemiExclusions.hom_unit_eq_zero_of_generated_three_subsystem
    K (modelProjection K M hM) (bundle K (modelInclusion K M hM))
    (LagrangianOriginalSubsystemSemi.originalSubsystem K M hM) (originalSubsystem_finrank K M hM)
    (LagrangianOriginalSubsystemSemi.originalSubsystem_semi K M hM)
    (imageBundle K M hM s) (image.ι (originalMap K M hM s))
    (imageSections K M hM s) hu hepi huA p

end M9Native.LagrangianOriginalSubsystemExclusions
