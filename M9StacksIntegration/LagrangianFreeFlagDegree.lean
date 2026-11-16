module

public import M9StacksIntegration.LagrangianFlagPolynomialPush
public import M9StacksIntegration.ChowFlagTriplePushDegree
public import M9StacksIntegration.LagrangianBaseDegree
public import M9StacksIntegration.LagrangianChowStructureTransport

/-! The actual free-six flag integrand has integer degree sixteen.
Its original three projective pushes and the original field-base point
supply every normalization; no numerical degree or class premise is used. -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1500000
set_option maxRecDepth 4096
open AlgebraicGeometry CategoryTheory Stacks.Chow
universe u
namespace M9Native.LagrangianFreeFlagDegree
open LagrangianFlagFundamentalTransport LagrangianActualDegree

attribute [local instance] LagrangianFlagPowerStages.sourceFinite
  LagrangianFlagPowerStages.kernel1Rank LagrangianFlagPowerStages.kernel1Finite
  LagrangianFlagPowerStages.kernel2Rank LagrangianFlagPowerStages.kernel2Finite
  LagrangianFlagPowerStages.projection1LFT LagrangianFlagPowerStages.projection2LFT
  LagrangianFlagPowerStages.projection3LFT

section Generic
variable {X : Scheme.{u}} (E : X.Modules)
    [SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} E 6]
    (C : ChowSituation.{u}) (q : X ⟶ C.S) [LocallyOfFiniteType q]

local instance originalFlagLFT : LocallyOfFiniteType
    (show FlagThreeQuotient.space E ⟶ C.S from LagrangianFlagPowerStages.baseMap3 E C q) := by
  infer_instance

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
/-- Only the two native grade-transport spellings change in the already-proved
actual geometric integral on an original degree-zero class. -/
theorem push_integrand_zero
    (e : E ≅ SheafOfModules.free (R:=X.ringCatSheaf) (ULift.{u} (Fin 6)))
    (β : chowGroup C q 0) :
    LagrangianFlagPowerStages.triplePush E C q 0
      (capTo (LagrangianChowPolynomials.evaluate C
        (LagrangianFlagPowerStages.baseMap3 E C q)
        (LagrangianPolynomialLineCongruence.originalLines E)
        LagrangianFlagCoefficientFunctional.integrand)
        (k:=0+12) 12 (by decide : ((0:ℤ)+12)-(12:ℕ)=0)
        (LagrangianFlagPowerStages.flatPullClass E C q 0 β)) = 16 • β := by
  let hCast := LagrangianChowStructureTransport.capTo_eq_chowGroupCast C
    (LagrangianFlagPowerStages.baseMap3 E C q)
    (LagrangianChowPolynomials.evaluate C (LagrangianFlagPowerStages.baseMap3 E C q)
      (LagrangianPolynomialLineCongruence.originalLines E)
      LagrangianFlagCoefficientFunctional.integrand)
    (0+12) 12 0 (by decide)
    (LagrangianFlagPowerStages.flatPullClass E C q 0 β)
  let hCastPush := congrArg (LagrangianFlagPowerStages.triplePush E C q 0) hCast
  let hIntegral := LagrangianFlagPolynomialPush.original_integrand_integral
    (E:=E) (C:=C) (q:=q) (e:=e) 0 β
  run_tac Lean.Elab.Tactic.withMainContext do
    let l ← Lean.Meta.getLocalDeclFromUserName `hCastPush
    let r ← Lean.Meta.getLocalDeclFromUserName `hIntegral
    let proof ← Lean.Meta.mkEqTrans l.toExpr r.toExpr
    Lean.Elab.Tactic.closeMainGoal `exact proof
end Generic

variable (K : Type u) [Field K]
abbrev freeSix : (Spec (.of K)).Modules := Stacks.FlagTower.freeModule 6 (Spec (.of K))
local instance freeRank : SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} (freeSix K) 6 :=
  Stacks.FlagTower.rank_freeModule 6 (Spec (.of K))
local instance freeFinite : SheafOfModules.IsFiniteLocallyFree.{u,u,u} (freeSix K) :=
  Stacks.FlagTower.isFiniteLocallyFree_freeModule 6 (Spec (.of K))
abbrev flagMap := LagrangianFlagPowerStages.baseMap3 (freeSix K)
  (fieldChowSituation K) (𝟙 (Spec (.of K)))

/-- The actual original free sheaf supplies its frame without a hypothesis. -/
def actualFrame : freeSix K ≅ SheafOfModules.free
    (R:=(Spec (.of K)).ringCatSheaf) (ULift.{u} (Fin 6)) := Iso.refl _

/-- The literal original polynomial cap on the actual three flat pulls of the point. -/
def actualClass : chowGroup (fieldChowSituation K) (flagMap K) 0 :=
  capTo (LagrangianChowPolynomials.evaluate (fieldChowSituation K) (flagMap K)
    (LagrangianPolynomialLineCongruence.originalLines (freeSix K))
    LagrangianFlagCoefficientFunctional.integrand)
    (k:=0+12) 12 (by decide : ((0:ℤ)+12)-(12:ℕ)=0)
    (LagrangianFlagPowerStages.flatPullClass (freeSix K) (fieldChowSituation K)
      (𝟙 (Spec (.of K))) 0 (baseFundamental K))

/-- Actual proper integration returns sixteen times the actual base fundamental class. -/
theorem actualClass_triplePush :
    LagrangianFlagPowerStages.triplePush (freeSix K) (fieldChowSituation K)
      (𝟙 (Spec (.of K))) 0 (actualClass K) = 16 • baseFundamental K :=
  push_integrand_zero (freeSix K) (fieldChowSituation K) (𝟙 (Spec (.of K)))
    (actualFrame K) (baseFundamental K)

/-- The actual free-six integral has native integer degree sixteen over every field. -/
theorem degree_actualClass_eq_sixteen :
    chowDegree (fieldChowSituation K) (fieldChowSituation_dimensionFunction_eq_zero K)
      (flagMap K) (IsLocalRing.closedPoint K) (actualClass K) = 16 := by
  have hDegree := ChowFlagTriplePushDegree.rankSix_triplePush_degree K (freeSix K)
    (𝟙 (Spec (.of K))) (actualClass K)
  have hValue := congrArg
    (chowDegree (fieldChowSituation K) (fieldChowSituation_dimensionFunction_eq_zero K)
      (𝟙 (Spec (.of K))) (IsLocalRing.closedPoint K)) (actualClass_triplePush K)
  have hPoint : chowDegree (fieldChowSituation K)
      (fieldChowSituation_dimensionFunction_eq_zero K) (𝟙 (Spec (.of K)))
      (IsLocalRing.closedPoint K) (16 • baseFundamental K) = 16 := by
    simp only [map_nsmul,baseFundamental_degree,nsmul_eq_mul,mul_one,Nat.cast_ofNat]
  exact hDegree.trans (hValue.trans hPoint)

end M9Native.LagrangianFreeFlagDegree
