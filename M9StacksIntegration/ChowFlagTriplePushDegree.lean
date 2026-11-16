module

public import M9StacksIntegration.ChowFlagThreeNormalizer
public import M9StacksIntegration.LagrangianFlagPowerStages
public import StacksFrontier.AlgebraicGeometry.Variety.NumericalIntersections.ChowDegree

/-!
# Integer degree under the two actual three-stage flag pushforwards

The three original projections are proper projective-bundle maps. The
native proper-pushforward degree theorem applies successively, without
an assumed composite-push or degree identity. No free frame is needed.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1500000
set_option maxRecDepth 4096

open AlgebraicGeometry CategoryTheory Stacks.Chow
universe u
namespace M9Native.ChowFlagTriplePushDegree

section RankThree

attribute [local instance] ChowFlagThreeNormalizer.actualHasKernels
  ChowFlagThreeNormalizer.actualHasKernel ChowFlagThreeNormalizer.sourceFinite
  ChowFlagThreeNormalizer.kernel1Rank ChowFlagThreeNormalizer.kernel1Finite
  ChowFlagThreeNormalizer.kernel2Rank ChowFlagThreeNormalizer.kernel2Finite
  ChowFlagThreeNormalizer.projection1LFT ChowFlagThreeNormalizer.projection2LFT
  ChowFlagThreeNormalizer.projection3LFT

/-- The SAME actual integer degree is preserved by the full rank-three quotient flag. -/
theorem rankThree_triplePush_degree (K : Type u) [Field K] {X : Scheme.{u}}
    (D : X.Modules) [SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} D 3]
    (q : X ⟶ Spec (.of K)) [IsProper q]
    (α : chowGroup (fieldChowSituation K)
      (ChowFlagThreeNormalizer.baseMap3 D (fieldChowSituation K) q) 0) :
    chowDegree (fieldChowSituation K) (fieldChowSituation_dimensionFunction_eq_zero K)
        (ChowFlagThreeNormalizer.baseMap3 D (fieldChowSituation K) q)
        (IsLocalRing.closedPoint K) α =
      chowDegree (fieldChowSituation K) (fieldChowSituation_dimensionFunction_eq_zero K)
        q (IsLocalRing.closedPoint K)
        (ChowFlagThreeNormalizer.triplePush D (fieldChowSituation K) q 0 α) := by
  have h3 := chowDegree_properChowPushforward K
    (ChowFlagThreeNormalizer.baseMap2 D (fieldChowSituation K) q)
    (ChowFlagThreeNormalizer.baseMap3 D (fieldChowSituation K) q)
    (ChowFlagThreeNormalizer.projection3 D) rfl α
  have h2 := chowDegree_properChowPushforward K
    (ChowFlagThreeNormalizer.baseMap1 D (fieldChowSituation K) q)
    (ChowFlagThreeNormalizer.baseMap2 D (fieldChowSituation K) q)
    (ChowFlagThreeNormalizer.projection2 D) rfl
    (ChowFlagThreeNormalizer.push3 D (fieldChowSituation K) q 0 α)
  have h1 := chowDegree_properChowPushforward K q
    (ChowFlagThreeNormalizer.baseMap1 D (fieldChowSituation K) q)
    (ChowFlagThreeNormalizer.projection1 D) rfl
    (ChowFlagThreeNormalizer.push2 D (fieldChowSituation K) q 0
      (ChowFlagThreeNormalizer.push3 D (fieldChowSituation K) q 0 α))
  exact h3.trans (h2.trans h1)

end RankThree

section RankSix

attribute [local instance] LagrangianFlagPowerStages.actualHasKernels
  LagrangianFlagPowerStages.actualHasKernel LagrangianFlagPowerStages.sourceFinite
  LagrangianFlagPowerStages.kernel1Rank LagrangianFlagPowerStages.kernel1Finite
  LagrangianFlagPowerStages.kernel2Rank LagrangianFlagPowerStages.kernel2Finite
  LagrangianFlagPowerStages.projection1LFT LagrangianFlagPowerStages.projection2LFT
  LagrangianFlagPowerStages.projection3LFT

/-- The SAME actual integer degree is preserved by the rank-six three-step flag. -/
theorem rankSix_triplePush_degree (K : Type u) [Field K] {X : Scheme.{u}}
    (E : X.Modules) [SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} E 6]
    (q : X ⟶ Spec (.of K)) [IsProper q]
    (α : chowGroup (fieldChowSituation K)
      (LagrangianFlagPowerStages.baseMap3 E (fieldChowSituation K) q) 0) :
    chowDegree (fieldChowSituation K) (fieldChowSituation_dimensionFunction_eq_zero K)
        (LagrangianFlagPowerStages.baseMap3 E (fieldChowSituation K) q)
        (IsLocalRing.closedPoint K) α =
      chowDegree (fieldChowSituation K) (fieldChowSituation_dimensionFunction_eq_zero K)
        q (IsLocalRing.closedPoint K)
        (LagrangianFlagPowerStages.triplePush E (fieldChowSituation K) q 0 α) := by
  have h3 := chowDegree_properChowPushforward K
    (LagrangianFlagPowerStages.baseMap2 E (fieldChowSituation K) q)
    (LagrangianFlagPowerStages.baseMap3 E (fieldChowSituation K) q)
    (LagrangianFlagPowerStages.projection3 E) rfl α
  have h2 := chowDegree_properChowPushforward K
    (LagrangianFlagPowerStages.baseMap1 E (fieldChowSituation K) q)
    (LagrangianFlagPowerStages.baseMap2 E (fieldChowSituation K) q)
    (LagrangianFlagPowerStages.projection2 E) rfl
    (LagrangianFlagPowerStages.push3 E (fieldChowSituation K) q 0 α)
  have h1 := chowDegree_properChowPushforward K q
    (LagrangianFlagPowerStages.baseMap1 E (fieldChowSituation K) q)
    (LagrangianFlagPowerStages.projection1 E) rfl
    (LagrangianFlagPowerStages.push2 E (fieldChowSituation K) q 0
      (LagrangianFlagPowerStages.push3 E (fieldChowSituation K) q 0 α))
  exact h3.trans (h2.trans h1)

end RankSix
end M9Native.ChowFlagTriplePushDegree
