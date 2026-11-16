module

public import M9StacksIntegration.ChowFlagThreeInputNormalization

/-! The original-projection form of the genuine flag input identity.
Ranks are derived on the literal original flag, and the target-line
comparison is applied through a generic tensor-cap lemma. -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1500000
set_option maxRecDepth 4096

open AlgebraicGeometry CategoryTheory Stacks.Chow Stacks.Chow.GenuineChern

universe u
namespace M9Native.ChowFlagThreeInputNormalization

open ChowFlagThreeStages

section GenericTensor

variable (C : ChowSituation.{u}) {Y : Scheme.{u}} (s : Y ⟶ C.S)
  [LocallyOfFiniteType s] (Q P₀ P₁ : Y.Modules)
  [hQ : SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} Q 3]
  [hP₀ : SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} P₀ 10]
  [hP₁ : SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} P₁ 10]

/-- Tensor-cap comparison on a fixed native scheme, before any flag
presentation is substituted. -/
theorem tensorCap_targetIso (e : P₀ ≅ P₁) :
    letI : SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u}
        (Scheme.Modules.tensorObj Q P₀) 30 :=
      @FlagThreeTensorChern.tensor_rank Y Q P₀ 3 10 hQ hP₀
    letI : SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u}
        (Scheme.Modules.tensorObj Q P₁) 30 :=
      @FlagThreeTensorChern.tensor_rank Y Q P₁ 3 10 hQ hP₁
    ∀ (k : ℤ) (x : chowGroup C s k),
      chernCap C 30 s (Scheme.Modules.tensorObj Q P₀) k (Fin.last 30) x =
        chernCap C 30 s (Scheme.Modules.tensorObj Q P₁) k (Fin.last 30) x := by
  letI : SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u}
      (Scheme.Modules.tensorObj Q P₀) 30 :=
    @FlagThreeTensorChern.tensor_rank Y Q P₀ 3 10 hQ hP₀
  letI : SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u}
      (Scheme.Modules.tensorObj Q P₁) 30 :=
    @FlagThreeTensorChern.tensor_rank Y Q P₁ 3 10 hQ hP₁
  intro k x
  exact chernCap_congr C s 30 (tensorCongr (Iso.refl Q) e) k (Fin.last 30) x

end GenericTensor

variable {X : Scheme.{u}} (D F : X.Modules)
  [hD : SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} D 10]
  [hF : SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} F 10]

local instance originalSourceFinite : SheafOfModules.IsFiniteLocallyFree.{u,u,u} D :=
  hD.isFiniteLocallyFree

local instance originalProjectionLFT : LocallyOfFiniteType (FlagThreeQuotient.projection D) :=
  ChowFlagThreeStages.originalProjectionLFT D

abbrev originalTarget : (FlagThreeQuotient.space D).Modules :=
  (Scheme.Modules.pullback (FlagThreeQuotient.projection D)).obj F

abbrev originalTensor : (FlagThreeQuotient.space D).Modules :=
  Scheme.Modules.tensorObj (FlagThreeQuotient.quotientBundle D 2) (originalTarget D F)

local instance originalQuotientRank : SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u}
    (FlagThreeQuotient.quotientBundle D 2) 3 :=
  FlagThreeQuotient.quotientBundle_rank D 2

local instance originalTargetRank : SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u}
    (originalTarget D F) 10 :=
  AlgebraicGeometry.isFiniteLocallyFreeOfRank_pullback (FlagThreeQuotient.projection D) F 10

local instance originalTensorRank : SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u}
    (originalTensor D F) 30 :=
  @FlagThreeTensorChern.tensor_rank (FlagThreeQuotient.space D)
    (FlagThreeQuotient.quotientBundle D 2) (originalTarget D F) 3 10
    (originalQuotientRank D) (originalTargetRank D F)

local instance concreteTargetOnOriginalRank : SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u}
    (show (FlagThreeQuotient.space D).Modules from target3 D F) 10 :=
  target3Rank D F

variable (C : ChowSituation.{u}) (q : X ⟶ C.S) [LocallyOfFiniteType q]

local instance concreteBaseOnOriginalLFT : LocallyOfFiniteType (baseMap3 D C q) := by
  rw [baseMap3_eq_original]
  infer_instance

attribute [local irreducible] Stacks.Chow.GenuineChern.chernCap
  ChowFlagThreeStages.normalClass
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

/-- The genuine original flag class has the same rank-thirty cap as
the three constructed inputs. All ranks and comparisons are derived. -/
theorem tensor_on_normalClassOnOriginalFlag_heq (k : ℤ) (x : chowGroup C q k) :
    @chernCap C 30 (FlagThreeQuotient.space D) (FlagThreeQuotient.projection D ≫ q)
      inferInstance (originalTensor D F) (originalTensorRank D F)
      (k+21) (Fin.last 30) (normalClassOnOriginalFlag D C q k x) ≍
    ChowFlagThreeInputs.normalTensorInputOnOriginalFlag D F C q k x := by
  have hcast := @cap_structureMapCast_heq C (FlagThreeQuotient.space D)
    (baseMap3 D C q) (concreteBaseOnOriginalLFT D C q)
    (FlagThreeQuotient.projection D ≫ q) inferInstance (baseMap3_eq_original D C q)
    (originalTensor D F) 30 (originalTensorRank D F)
    (k+21) (Fin.last 30) (normalClass D C q k x)
  have htarget := @tensorCap_targetIso C (FlagThreeQuotient.space D)
    (baseMap3 D C q) (concreteBaseOnOriginalLFT D C q)
    (FlagThreeQuotient.quotientBundle D 2) (originalTarget D F)
    (show (FlagThreeQuotient.space D).Modules from target3 D F)
    (originalQuotientRank D) (originalTargetRank D F) (concreteTargetOnOriginalRank D F)
    (target3IsoOriginal D F).symm (k+21) (normalClass D C q k x)
  have hcore := tensor_on_normalClass_heq D F C q k x
  have hinput := ChowFlagThreeInputs.normalTensorInputOnOriginalFlag_heq D F C q k x
  have hleft := hcast.trans (heq_of_eq htarget)
  have hright := hcore.trans hinput.symm
  -- The standard application builder retains the two fully typed proofs.
  -- The kernel checks their composition without repeating midpoint elaboration.
  run_tac Lean.Elab.Tactic.withMainContext do
    let l ← Lean.Meta.getLocalDeclFromUserName `hleft
    let r ← Lean.Meta.getLocalDeclFromUserName `hright
    let proof ← Lean.Meta.mkHEqTrans l.toExpr r.toExpr
    Lean.Elab.Tactic.closeMainGoal `exact proof

end M9Native.ChowFlagThreeInputNormalization
