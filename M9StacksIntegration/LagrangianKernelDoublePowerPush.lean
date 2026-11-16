module

public import M9StacksIntegration.LagrangianFreeFlagPowerValues

/-!
# The two genuine kernel power pushes in the free-six flag

All operations are original flat projective pullback, powers of the
same original quotient line, and actual proper pushforward. The inner
three possible powers are computed using the genuine finite moment
values of the two original kernels.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
set_option maxRecDepth 4096
open AlgebraicGeometry CategoryTheory Stacks.Chow
universe u v
namespace M9Native.LagrangianKernelDoublePowerPush
open ChowCapWords GradedLineCapSubring GradedCapVirtualSchur LagrangianFlagPowerStages

section Generic
variable {G : ℤ → Type v} [∀ k, AddCommGroup (G k)]

theorem neg_heq {k l : ℤ} (hkl : k=l) {a : G k} {b : G l} (h : a ≍ b) :
    -a ≍ -b := by
  cases hkl
  cases h
  rfl

theorem sub_heq {k l : ℤ} (hkl : k=l) {a b : G k} {a' b' : G l}
    (ha : a ≍ a') (hb : b ≍ b') : a-b ≍ a'-b' := by
  cases hkl
  cases ha
  cases hb
  rfl

end Generic

attribute [local instance] LagrangianFlagPowerStages.sourceFinite
  LagrangianFlagPowerStages.kernel1Rank LagrangianFlagPowerStages.kernel1Finite
  LagrangianFlagPowerStages.kernel2Rank LagrangianFlagPowerStages.kernel2Finite
  LagrangianFlagPowerStages.projection1Flat LagrangianFlagPowerStages.projection2Flat
  LagrangianFlagPowerStages.projection3Flat LagrangianFlagPowerStages.projection1LFT
  LagrangianFlagPowerStages.projection2LFT LagrangianFlagPowerStages.projection3LFT

variable {X : Scheme.{u}} (E : X.Modules)
    [SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} E 6]
    (C : ChowSituation.{u}) (q : X ⟶ C.S) [LocallyOfFiniteType q]

def middleClass (b : ℕ) (k : ℤ) (β : chowGroup C (baseMap1 E C q) k) :
    chowGroup C (baseMap2 E C q) (k+4-(b:ℤ)) :=
  capPow C (baseMap2 E C q) (lineCap C (baseMap2 E C q) (secondLine E))
    b (k+4) (k+4-(b:ℤ)) (by omega) (pull2 E C q k β)

def middlePower (b : ℕ) (k : ℤ) (β : chowGroup C (baseMap1 E C q) k) :
    chowGroup C (baseMap1 E C q) (k+4-(b:ℤ)) :=
  @LagrangianProjectivePowerPush.powerPush (space1 E) (kernel1 E) 4
    (LagrangianFlagPowerStages.kernel1Rank E) C (baseMap1 E C q) inferInstance b k β

def raisedMiddlePower (b : ℕ) (k : ℤ) (β : chowGroup C (baseMap1 E C q) k) :
    chowGroup C (baseMap1 E C q) ((k+4-(b:ℤ))-1) :=
  chowGroupCast C (baseMap1 E C q) (by omega) (middlePower E C q (b+1) k β)

def firstCap (k : ℤ) (β : chowGroup C (baseMap1 E C q) k) :
    chowGroup C (baseMap1 E C q) (k-1) :=
  lineFamily C (baseMap1 E C q) (firstLine E) k 1 β

def firstCapTwice (k : ℤ) (β : chowGroup C (baseMap1 E C q) k) :
    chowGroup C (baseMap1 E C q) ((k-1)-1) :=
  firstCap E C q (k-1) (firstCap E C q k β)

theorem middle_power_four (k : ℤ) (β : chowGroup C (baseMap1 E C q) k) :
    middlePower E C q 4 k β ≍ β :=
  @LagrangianProjectivePowerPush.powerPush_top (space1 E) (kernel1 E) 4
    (LagrangianFlagPowerStages.kernel1Rank E) C (baseMap1 E C q) inferInstance k β

theorem raised_middle_heq (b : ℕ) (k : ℤ) (β : chowGroup C (baseMap1 E C q) k) :
    raisedMiddlePower E C q b k β ≍ middlePower E C q (b+1) k β :=
  chowGroupCast_heq C (baseMap1 E C q) _ _

/-- Both original proper pushes, with the actual inner pull and cap
already present in the literal original powerPush. -/
def doublePowerPush (b c : ℕ) (k : ℤ) (β : chowGroup C (baseMap1 E C q) k) :
    chowGroup C (baseMap1 E C q) (k+7-(b:ℤ)-(c:ℤ)) :=
  push2 E C q (k+7-(b:ℤ)-(c:ℤ))
    (chowGroupCast C (baseMap2 E C q) (by omega)
      (@LagrangianProjectivePowerPush.powerPush (space2 E) (kernel2 E) 3
        (LagrangianFlagPowerStages.kernel2Rank E) C (baseMap2 E C q) inferInstance
        c (k+4-(b:ℤ)) (middleClass E C q b k β)))

theorem push2_middleClass (b : ℕ) (k : ℤ) (β : chowGroup C (baseMap1 E C q) k) :
    push2 E C q (k+4-(b:ℤ)) (middleClass E C q b k β) = middlePower E C q b k β := rfl

theorem line_middleClass_succ (b : ℕ) (k : ℤ) (β : chowGroup C (baseMap1 E C q) k) :
    lineFamily C (baseMap2 E C q) (secondLine E) (k+4-(b:ℤ)) 1
        (middleClass E C q b k β) ≍ middleClass E C q (b+1) k β := by
  let ξ := lineCap C (baseMap2 E C q) (secondLine E)
  have h := LineFamilyCapPower.lineFamily_pow_apply_heq C (baseMap2 E C q) (secondLine E)
    1 (k+4-(b:ℤ)) (k+4-((b+1:ℕ):ℤ)) (by omega) (middleClass E C q b k β)
  rw [pow_one] at h
  have hs : capPow C (baseMap2 E C q) ξ 1 (k+4-(b:ℤ)) (k+4-((b+1:ℕ):ℤ))
      (by omega) (middleClass E C q b k β) = middleClass E C q (b+1) k β := by
    dsimp only [middleClass]
    rw [capPow_capPow]
  exact h.trans (heq_of_eq hs)

theorem push2_y_middleClass (b : ℕ) (k : ℤ) (β : chowGroup C (baseMap1 E C q) k) :
    push2 E C q ((k+4-(b:ℤ))-1)
        (lineFamily C (baseMap2 E C q) (secondLine E) (k+4-(b:ℤ)) 1
          (middleClass E C q b k β)) = raisedMiddlePower E C q b k β := by
  apply eq_of_heq
  refine (ChowFlagThreeNormalizer.properPush_heq C (baseMap2 E C q) (baseMap1 E C q)
    (projection2 E) rfl (show (k+4-(b:ℤ))-1=k+4-((b+1:ℕ):ℤ) by omega)
    (line_middleClass_succ E C q b k β)).trans ?_
  refine (heq_of_eq (push2_middleClass E C q (b+1) k β)).trans ?_
  exact (chowGroupCast_heq C (baseMap1 E C q) _ _).symm

theorem push2_x_middleClass (b : ℕ) (k : ℤ) (β : chowGroup C (baseMap1 E C q) k) :
    push2 E C q ((k+4-(b:ℤ))-1)
        (lineFamily C (baseMap2 E C q) (firstLineAt2 E) (k+4-(b:ℤ)) 1
          (middleClass E C q b k β)) =
      lineFamily C (baseMap1 E C q) (firstLine E) (k+4-(b:ℤ)) 1
        (middlePower E C q b k β) := by
  have h := ChowLineProperPush.properPush_lineFamily_apply C
    (baseMap2 E C q) (baseMap1 E C q) (projection2 E) rfl
    (firstLine E) (firstLineAt2 E) (Iso.refl _) (k+4-(b:ℤ)) 1
    (middleClass E C q b k β)
  change push2 E C q ((k+4-(b:ℤ))-1)
    (lineFamily C (baseMap2 E C q) (firstLineAt2 E) (k+4-(b:ℤ)) 1
      (middleClass E C q b k β)) =
    lineFamily C (baseMap1 E C q) (firstLine E) (k+4-(b:ℤ)) 1
      (push2 E C q (k+4-(b:ℤ)) (middleClass E C q b k β)) at h
  rw [push2_middleClass] at h
  exact h

theorem push2_yx_middleClass (b : ℕ) (k : ℤ) (β : chowGroup C (baseMap1 E C q) k) :
    push2 E C q ((k+4-(b:ℤ))-2)
        ((lineFamily C (baseMap2 E C q) (secondLine E) *
          lineFamily C (baseMap2 E C q) (firstLineAt2 E)) (k+4-(b:ℤ)) 2
          (middleClass E C q b k β)) ≍
      lineFamily C (baseMap1 E C q) (firstLine E) ((k+4-(b:ℤ))-1) 1
        (raisedMiddlePower E C q b k β) := by
  let y := lineFamily C (baseMap2 E C q) (secondLine E)
  let x := lineFamily C (baseMap2 E C q) (firstLineAt2 E)
  let m := k+4-(b:ℤ)
  let J := middleClass E C q b k β
  have hcomm := lineFamily_commute C (baseMap2 E C q) (secondLine E) (firstLineAt2 E)
  have hprod : (y*x) m 2 J ≍ x (m-1) 1 (y m 1 J) := by
    rw [hcomm.eq, mul_apply_of_homogeneous_right x
      (lineFamily_homogeneous C (baseMap2 E C q) (secondLine E)) 1 m J, capTo_def]
    exact gradedDegreeCast_heq _ _
  refine (ChowFlagThreeNormalizer.properPush_heq C (baseMap2 E C q) (baseMap1 E C q)
    (projection2 E) rfl (show m-2=(m-1)-1 by omega) hprod).trans ?_
  have hp := ChowLineProperPush.properPush_lineFamily_apply C
    (baseMap2 E C q) (baseMap1 E C q) (projection2 E) rfl
    (firstLine E) (firstLineAt2 E) (Iso.refl _) (m-1) 1 (y m 1 J)
  change push2 E C q ((m-1)-1) (x (m-1) 1 (y m 1 J)) =
    lineFamily C (baseMap1 E C q) (firstLine E) (m-1) 1
      (push2 E C q (m-1) (y m 1 J)) at hp
  rw [push2_y_middleClass] at hp
  exact heq_of_eq hp

theorem double_power_three (b : ℕ) (k : ℤ) (β : chowGroup C (baseMap1 E C q) k) :
    doublePowerPush E C q b 3 k β ≍ middlePower E C q b k β := by
  have h := @LagrangianProjectivePowerPush.powerPush_top
    (space2 E) (kernel2 E) 3 (LagrangianFlagPowerStages.kernel2Rank E)
    C (baseMap2 E C q) inferInstance (k+4-(b:ℤ)) (middleClass E C q b k β)
  refine (ChowFlagThreeNormalizer.properPush_heq C (baseMap2 E C q) (baseMap1 E C q)
    (projection2 E) rfl (show k+7-(b:ℤ)-3=k+4-(b:ℤ) by omega)
    ((chowGroupCast_heq C (baseMap2 E C q) _ _).trans h)).trans ?_
  exact heq_of_eq (push2_middleClass E C q b k β)

theorem double_power_lt_three (b c : ℕ) (hc : c<3) (k : ℤ)
    (β : chowGroup C (baseMap1 E C q) k) : doublePowerPush E C q b c k β = 0 := by
  rw [doublePowerPush,
    @LagrangianProjectivePowerPush.powerPush_eq_zero_of_lt
      (space2 E) (kernel2 E) 3 (LagrangianFlagPowerStages.kernel2Rank E)
      C (baseMap2 E C q) inferInstance c hc,
    map_zero, map_zero]

variable (e : E ≅ SheafOfModules.free (R := X.ringCatSheaf) (ULift.{u} (Fin 6)))
include e

theorem middle_power_five (k : ℤ) (β : chowGroup C (baseMap1 E C q) k) :
    middlePower E C q 5 k β ≍ -firstCap E C q k β :=
  LagrangianFreeFlagPowerValues.middle_power_five E e C q k β

theorem middle_power_zero (b : ℕ) (h4 : b≠4) (h5 : b≠5) (k : ℤ)
    (β : chowGroup C (baseMap1 E C q) k) : middlePower E C q b k β = 0 :=
  LagrangianFreeFlagPowerValues.middle_power_zero E e C q b h4 h5 k β

theorem raised_middle_zero (b : ℕ) (h4 : b+1≠4) (h5 : b+1≠5) (k : ℤ)
    (β : chowGroup C (baseMap1 E C q) k) : raisedMiddlePower E C q b k β = 0 := by
  rw [raisedMiddlePower, middle_power_zero E C q e (b+1) h4 h5, map_zero]

theorem double_power_four (b : ℕ) (k : ℤ) (β : chowGroup C (baseMap1 E C q) k) :
    doublePowerPush E C q b 4 k β ≍
      -raisedMiddlePower E C q b k β -
        lineFamily C (baseMap1 E C q) (firstLine E) (k+4-(b:ℤ)) 1
          (middlePower E C q b k β) := by
  have h := LagrangianFreeFlagPowerValues.inner_power_four E e C q
    (k+4-(b:ℤ)) (middleClass E C q b k β)
  refine (ChowFlagThreeNormalizer.properPush_heq C (baseMap2 E C q) (baseMap1 E C q)
    (projection2 E) rfl (show k+7-(b:ℤ)-4=(k+4-(b:ℤ))-1 by omega)
    ((chowGroupCast_heq C (baseMap2 E C q) _ _).trans h)).trans ?_
  apply heq_of_eq
  rw [map_sub, map_neg, push2_y_middleClass, push2_x_middleClass]

theorem double_power_five (b : ℕ) (k : ℤ) (β : chowGroup C (baseMap1 E C q) k) :
    doublePowerPush E C q b 5 k β ≍
      lineFamily C (baseMap1 E C q) (firstLine E) ((k+4-(b:ℤ))-1) 1
        (raisedMiddlePower E C q b k β) := by
  have h := LagrangianFreeFlagPowerValues.inner_power_five E e C q
    (k+4-(b:ℤ)) (middleClass E C q b k β)
  refine (ChowFlagThreeNormalizer.properPush_heq C (baseMap2 E C q) (baseMap1 E C q)
    (projection2 E) rfl (show k+7-(b:ℤ)-5=(k+4-(b:ℤ))-2 by omega)
    ((chowGroupCast_heq C (baseMap2 E C q) _ _).trans h)).trans ?_
  exact push2_yx_middleClass E C q b k β

theorem double_power_gt_five (b c : ℕ) (hc : 5<c) (k : ℤ)
    (β : chowGroup C (baseMap1 E C q) k) : doublePowerPush E C q b c k β = 0 := by
  rw [doublePowerPush,
    LagrangianFreeFlagPowerValues.inner_power_gt_five E e C q c hc,
    map_zero, map_zero]

end M9Native.LagrangianKernelDoublePowerPush
