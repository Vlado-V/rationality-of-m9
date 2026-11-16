module

public import M9StacksIntegration.LagrangianAmbientNumerator
public import M9StacksIntegration.LagrangianFlagPolynomialNumerator
public import M9StacksIntegration.LagrangianFlagFlatFundamental
public import M9StacksIntegration.LagrangianChowStructureTransport
public import M9StacksIntegration.LagrangianFlagPolynomialTransport

/-! The actual normalized quotient flag and actual free flag are compared
to the native models only by equality of their original structure maps.
Both flat-pulled classes are proved to be the original fundamental classes. -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1500000
set_option maxRecDepth 4096
open AlgebraicGeometry CategoryTheory Stacks.Chow
universe u
namespace M9Native.LagrangianFlagModelComparison
open LagrangianGrassmannian LagrangianDegree LagrangianFlagFundamentalTransport
open LagrangianFlagPolynomialTransport LagrangianChowStructureTransport

attribute [local instance] ChowFlagThreeNormalizer.sourceFinite
  ChowFlagThreeNormalizer.kernel1Rank ChowFlagThreeNormalizer.kernel1Finite
  ChowFlagThreeNormalizer.kernel2Rank ChowFlagThreeNormalizer.kernel2Finite
  ChowFlagThreeNormalizer.projection1LFT ChowFlagThreeNormalizer.projection2LFT
  ChowFlagThreeNormalizer.projection3LFT
  LagrangianFlagPowerStages.sourceFinite LagrangianFlagPowerStages.kernel1Rank
  LagrangianFlagPowerStages.kernel1Finite LagrangianFlagPowerStages.kernel2Rank
  LagrangianFlagPowerStages.kernel2Finite LagrangianFlagPowerStages.projection1LFT
  LagrangianFlagPowerStages.projection2LFT LagrangianFlagPowerStages.projection3LFT

/-- Equal integer input grades give the same actual fundamental cap.
The transports are eliminated before specializing to a native flag scheme. -/
theorem fundamentalCap_grade_congr (C : ChowSituation.{u}) {Y : Scheme.{u}}
    (q : Y ⟶ C.S) [LocallyOfFiniteType q] (A : GradedCapFamily (chowGroup C q))
    {k l m : ℤ} (hkl : k=l) (i : ℕ) (hk : k-(i:ℤ)=m) (hl : l-(i:ℤ)=m) :
    capTo A i hk (fundamentalClass C q k) =
      capTo A i hl (fundamentalClass C q l) := by
  cases hkl
  rfl

/-- The value of the transported cap is pinned generically, before any
rich native field model is substituted. The supplied source-class equality
is proved internally by the actual flat-fundamental theorem at each client. -/
private def transportedFundamentalCapData (C : ChowSituation.{u}) {Y : Scheme.{u}}
    (q q' : Y ⟶ C.S) [LocallyOfFiniteType q] [LocallyOfFiniteType q']
    (h : q = q') (L L' : Fin 3 → ChowCapWords.InvertibleLine Y)
    (hL : L = L') (P : MvPolynomial (Fin 3) ℤ) (k l m : ℤ) (hkl : k = l)
    (i : ℕ) (hk : k-(i:ℤ)=m) (hl : l-(i:ℤ)=m) (a : chowGroup C q k)
    (ha : structureMapCast C q q' h k a = fundamentalClass C q' k) :
    {β : chowGroup C q' m //
      β = capTo (LagrangianChowPolynomials.evaluate C q' L' P) i hl
        (fundamentalClass C q' l)} := by
  refine ⟨structureMapCast C q q' h m
    (capTo (LagrangianChowPolynomials.evaluate C q L P) i hk a), ?_⟩
  have hcap := evaluate_capTo_structureMapCast C q q' h L P k i m hk a
  rw [ha] at hcap
  have hgrade := fundamentalCap_grade_congr C q'
    (LagrangianChowPolynomials.evaluate C q' L P) hkl i hk hl
  have hline :
      capTo (LagrangianChowPolynomials.evaluate C q' L P) i hl
        (fundamentalClass C q' l) =
      capTo (LagrangianChowPolynomials.evaluate C q' L' P) i hl
        (fundamentalClass C q' l) := by
    cases hL
    rfl
  exact hcap.trans (hgrade.trans hline)

variable (K : Type u) [Field K] [CharZero K]
local instance quotientFinite : SheafOfModules.IsFiniteLocallyFree.{u,u,u} (quotientBundle K) :=
  (quotientBundle_rank K).isFiniteLocallyFree
abbrev freeSix : (Spec (.of K)).Modules := Stacks.FlagTower.freeModule 6 (Spec (.of K))
local instance freeFinite : SheafOfModules.IsFiniteLocallyFree.{u,u,u} (freeSix K) :=
  Stacks.FlagTower.isFiniteLocallyFree_freeModule 6 (Spec (.of K))
local instance freeRank : SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} (freeSix K) 6 :=
  Stacks.FlagTower.rank_freeModule 6 (Spec (.of K))

abbrev quotientMap := ChowFlagThreeNormalizer.baseMap3 (quotientBundle K)
  (fieldChowSituation K) (grassmannianProjection K)
abbrev freeMap := LagrangianFlagPowerStages.baseMap3 (freeSix K)
  (fieldChowSituation K) (𝟙 (Spec (.of K)))

/-- Only the original parentheses and native identity stage change. -/
theorem quotientMap_eq_native : quotientMap K = qA K :=
  Three.q3_eq_tower (quotientBundle K) (fieldChowSituation K) (grassmannianProjection K)

/-- The original free flag has the native tower's original structural map. -/
theorem freeMap_eq_native : freeMap K = qB K :=
  (Three.q3_eq_tower (freeSix K) (fieldChowSituation K) (𝟙 (Spec (.of K)))).trans
    (Category.comp_id _)

/-- The actual normalized flag's pulled class is the native fundamental class. -/
theorem quotientFlat_cast_fundamental :
    structureMapCast (fieldChowSituation K) (quotientMap K) (qA K)
      (quotientMap_eq_native K) (9+3)
      (ChowFlagThreeNormalizer.flatPullClass (quotientBundle K) (fieldChowSituation K)
        (grassmannianProjection K) 9 (ambientFundamental K)) =
        fundamentalClass (fieldChowSituation K) (qA K) (9+3) := by
  have h := LagrangianFlagFlatFundamental.rankThree_flatPullClass_fundamental
    (quotientBundle K) (fieldChowSituation K) (grassmannianProjection K) 9
    (le_of_eq (ambient_delta_dimension K))
  change ChowFlagThreeNormalizer.flatPullClass (quotientBundle K) (fieldChowSituation K)
      (grassmannianProjection K) 9 (ambientFundamental K) =
    fundamentalClass (fieldChowSituation K) (quotientMap K) (9+3) at h
  have hCast := congrArg (structureMapCast (fieldChowSituation K) (quotientMap K) (qA K)
    (quotientMap_eq_native K) (9+3)) h
  exact hCast.trans (structureMapCast_fundamentalClass (fieldChowSituation K)
    (quotientMap K) (qA K) (quotientMap_eq_native K) (9+3))

/-- The actual free-flag pull of the point is its native fundamental class. -/
theorem freeFlat_cast_fundamental :
    structureMapCast (fieldChowSituation K) (freeMap K) (qB K)
      (freeMap_eq_native K) (0+12)
      (LagrangianFlagPowerStages.flatPullClass (freeSix K) (fieldChowSituation K)
        (𝟙 (Spec (.of K))) 0 (baseFundamental K)) =
        fundamentalClass (fieldChowSituation K) (qB K) (0+12) := by
  have h := LagrangianFlagFlatFundamental.rankSix_flatPullClass_fundamental
    (freeSix K) (fieldChowSituation K) (𝟙 (Spec (.of K))) 0
    (le_of_eq (base_delta_dimension K))
  change LagrangianFlagPowerStages.flatPullClass (freeSix K) (fieldChowSituation K)
      (𝟙 (Spec (.of K))) 0 (baseFundamental K) =
    fundamentalClass (fieldChowSituation K) (freeMap K) (0+12) at h
  have hCast := congrArg (structureMapCast (fieldChowSituation K) (freeMap K) (qB K)
    (freeMap_eq_native K) (0+12)) h
  exact hCast.trans (structureMapCast_fundamentalClass (fieldChowSituation K)
    (freeMap K) (qB K) (freeMap_eq_native K) (0+12))

/-- The literal native normalized polynomial cap in the quotient flag. -/
def nativeClassA : chowGroup (fieldChowSituation K) (qA K) 0 :=
  capTo (LagrangianChowPolynomials.evaluate (fieldChowSituation K) (qA K) (linesA K)
    LagrangianFlagCoefficientFunctional.integrand)
    12 (by decide : (12:ℤ)-(12:ℕ)=0) (fundamentalA K)

/-- The same original polynomial cap on the native free flag. -/
def nativeClassB : chowGroup (fieldChowSituation K) (qB K) 0 :=
  capTo (LagrangianChowPolynomials.evaluate (fieldChowSituation K) (qB K) (linesB K)
    LagrangianFlagCoefficientFunctional.integrand)
    12 (by decide : (12:ℤ)-(12:ℕ)=0) (fundamentalB K)

/-- The original polynomial cap on the actual quotient flag, before the same-map transport. -/
def quotientClass : chowGroup (fieldChowSituation K) (quotientMap K) 0 :=
  capTo (LagrangianChowPolynomials.evaluate (fieldChowSituation K) (quotientMap K)
    (LagrangianFlagPolynomialNumerator.originalLines (quotientBundle K))
    LagrangianFlagCoefficientFunctional.integrand)
    (k:=9+3) 12 (by decide : ((9:ℤ)+3)-(12:ℕ)=0)
    (ChowFlagThreeNormalizer.flatPullClass (quotientBundle K) (fieldChowSituation K)
      (grassmannianProjection K) 9 (ambientFundamental K))

/-- The actual free integrand before the same-map transport. -/
def freeClass : chowGroup (fieldChowSituation K) (freeMap K) 0 :=
  capTo (LagrangianChowPolynomials.evaluate (fieldChowSituation K) (freeMap K)
    (LagrangianPolynomialLineCongruence.originalLines (freeSix K))
    LagrangianFlagCoefficientFunctional.integrand)
    (k:=0+12) 12 (by decide : ((0:ℤ)+12)-(12:ℕ)=0)
    (LagrangianFlagPowerStages.flatPullClass (freeSix K) (fieldChowSituation K)
      (𝟙 (Spec (.of K))) 0 (baseFundamental K))

/-- The original root packages are the same native named sheaves. -/
theorem originalLinesA_eq :
    LagrangianFlagPolynomialNumerator.originalLines (quotientBundle K) = linesA K := rfl

section QuotientClosureCaches

/-- The displayed views below are the same original morphisms. Each LFT
cache is derived before the protected elaboration block. -/
private local instance quotientMapNativeLFT : LocallyOfFiniteType
    (show spaceA K ⟶ (fieldChowSituation K).S from quotientMap K) := by
  infer_instance

private local instance nativeMapNativeLFT : LocallyOfFiniteType
    (show spaceA K ⟶ (fieldChowSituation K).S from qA K) :=
  LagrangianFlagFundamentalTransport.qA_lft K

private local instance nativeMapOriginalLFT : LocallyOfFiniteType
    (show ChowFlagThreeNormalizer.space3 (quotientBundle K) ⟶
      (fieldChowSituation K).S from qA K) := by
  rw [← quotientMap_eq_native K]
  infer_instance

private local instance quotientMapLiteralFlagLFT : LocallyOfFiniteType
    (show FlagThreeQuotient.space (quotientBundle K) ⟶
      (fieldChowSituation K).S from quotientMap K) := by
  infer_instance

private local instance nativeMapLiteralFlagLFT : LocallyOfFiniteType
    (show FlagThreeQuotient.space (quotientBundle K) ⟶
      (fieldChowSituation K).S from qA K) := by
  rw [← quotientMap_eq_native K]
  infer_instance

set_option pp.explicit true in
/-- Same-map transport of the actual quotient-flag integrand. -/
theorem quotientIntegrand_cast_native :
    structureMapCast (fieldChowSituation K) (quotientMap K) (qA K)
      (quotientMap_eq_native K) 0
      (quotientClass K) = nativeClassA K :=
  set_option backward.isDefEq.respectTransparency true in
  set_option backward.isDefEq.respectTransparency.types true in
  by
    have hp := (transportedFundamentalCapData (fieldChowSituation K) (Y := spaceA K)
      (quotientMap K) (qA K) (quotientMap_eq_native K)
      (LagrangianFlagPolynomialNumerator.originalLines (quotientBundle K))
      (linesA K) (originalLinesA_eq K) LagrangianFlagCoefficientFunctional.integrand
      (9+3) 12 0 (by decide) 12 (by decide) (by decide)
      (ChowFlagThreeNormalizer.flatPullClass (quotientBundle K) (fieldChowSituation K)
        (grassmannianProjection K) 9 (ambientFundamental K))
      (quotientFlat_cast_fundamental K)).property
    dsimp only [transportedFundamentalCapData] at hp
    unfold quotientClass nativeClassA fundamentalA
    run_tac Lean.Elab.Tactic.withMainContext do
      let p ← Lean.Meta.getLocalDeclFromUserName `hp
      Lean.Elab.Tactic.closeMainGoal `exact p.toExpr

end QuotientClosureCaches

/-- Same-map transport of the actual free-flag integrand. -/
theorem freeIntegrand_cast_native :
    structureMapCast (fieldChowSituation K) (freeMap K) (qB K)
      (freeMap_eq_native K) 0 (freeClass K) = nativeClassB K := by
  have hp := (transportedFundamentalCapData (fieldChowSituation K) (Y := spaceB K)
    (freeMap K) (qB K) (freeMap_eq_native K)
    (LagrangianPolynomialLineCongruence.originalLines (freeSix K))
    (linesB K) (linesB_eq_original K).symm LagrangianFlagCoefficientFunctional.integrand
    (0+12) 12 0 (by decide) 12 (by decide) (by decide)
    (LagrangianFlagPowerStages.flatPullClass (freeSix K) (fieldChowSituation K)
      (𝟙 (Spec (.of K))) 0 (baseFundamental K))
    (freeFlat_cast_fundamental K)).property
  dsimp only [transportedFundamentalCapData] at hp
  unfold freeClass nativeClassB fundamentalB
  exact hp

end M9Native.LagrangianFlagModelComparison
