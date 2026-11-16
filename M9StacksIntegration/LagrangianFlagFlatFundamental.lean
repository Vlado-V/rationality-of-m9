module

public import M9StacksIntegration.LagrangianFlagFundamentalTransport
public import M9StacksIntegration.ChowFlagThreePullback
public import M9StacksIntegration.LagrangianFlagPowerStages

/-!
# Actual fundamental classes under the two original flat flag pulls

These adapters apply the checked three-stage native fundamental-class
formula and remove only the original integer-grade casts. The actual
right-associated structure maps are retained throughout.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1500000
set_option maxRecDepth 4096

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Stacks.Chow
universe u
namespace M9Native.LagrangianFlagFlatFundamental
open LagrangianFlagFundamentalTransport

private theorem fundamentalClass_grade_heq (C : ChowSituation.{u}) {Y : Scheme.{u}}
    (q : Y ⟶ C.S) [LocallyOfFiniteType q] {a b : ℤ} (h : a = b) :
    fundamentalClass C q a ≍ fundamentalClass C q b := by
  cases h
  rfl

section RankThree
variable {X : Scheme.{u}} (D : X.Modules)
    [hD : SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} D 3]
local instance sourceFinite : SheafOfModules.IsFiniteLocallyFree.{u,u,u} D :=
  hD.isFiniteLocallyFree

/-- The original rank-three full flat pullback sends the original
fundamental class to the actual flag fundamental class. -/
theorem rankThree_flatPullClass_fundamental (C : ChowSituation.{u})
    (q : X ⟶ C.S) [LocallyOfFiniteType q] (k : ℤ)
    (hX : schemeDeltaDimension C q ≤ (k : EInt)) :
    ChowFlagThreeNormalizer.flatPullClass D C q k (fundamentalClass C q k) =
      fundamentalClass C (ChowFlagThreeNormalizer.baseMap3 D C q) (k+3) := by
  have hraw := Three.iteratedPull_fundamentalClass 0 D C q k hX
  change ChowFlagThreePullback.rawPull3 D C q ((k+2)+1)
      (ChowFlagThreeNormalizer.pull2 D C q (k+2)
        (ChowFlagThreeNormalizer.pull1 D C q k (fundamentalClass C q k))) =
    fundamentalClass C (ChowFlagThreeNormalizer.baseMap3 D C q) (((k+2)+1)+0) at hraw
  have hpull := ChowFlagThreePullback.fullPull_heq_raw D C q k (fundamentalClass C q k)
  rw [ChowFlagThreePullback.fullPull_apply] at hpull
  apply eq_of_heq
  exact hpull.trans ((heq_of_eq hraw).trans
    (fundamentalClass_grade_heq C (ChowFlagThreeNormalizer.baseMap3 D C q) (by omega)))
end RankThree

section RankSix
variable {X : Scheme.{u}} (E : X.Modules)
    [hE : SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} E 6]
local instance sourceFiniteSix : SheafOfModules.IsFiniteLocallyFree.{u,u,u} E :=
  hE.isFiniteLocallyFree

/-- The original rank-six three-stage flat pullback sends the original
fundamental class to the actual flag fundamental class. -/
theorem rankSix_flatPullClass_fundamental (C : ChowSituation.{u})
    (q : X ⟶ C.S) [LocallyOfFiniteType q] (k : ℤ)
    (hX : schemeDeltaDimension C q ≤ (k : EInt)) :
    LagrangianFlagPowerStages.flatPullClass E C q k (fundamentalClass C q k) =
      fundamentalClass C (LagrangianFlagPowerStages.baseMap3 E C q) (k+12) := by
  have hraw := Three.iteratedPull_fundamentalClass 3 E C q k hX
  change LagrangianFlagPowerStages.pull3 E C q ((k+5)+4)
      (LagrangianFlagPowerStages.pull2 E C q (k+5)
        (LagrangianFlagPowerStages.pull1 E C q k (fundamentalClass C q k))) =
    fundamentalClass C (LagrangianFlagPowerStages.baseMap3 E C q) (((k+5)+4)+3) at hraw
  apply eq_of_heq
  refine (chowGroupCast_heq C (LagrangianFlagPowerStages.baseMap3 E C q) _ _).trans ?_
  exact (heq_of_eq hraw).trans
    (fundamentalClass_grade_heq C (LagrangianFlagPowerStages.baseMap3 E C q) (by omega))
end RankSix

end M9Native.LagrangianFlagFlatFundamental
