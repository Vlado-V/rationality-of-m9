module

public import M9StacksIntegration.LagrangianKernelDoublePowerPush

/-!
# The six surviving genuine kernel-power pushes

The support and signs are proved for the actual two projective
pushforwards on every original Chow input. The remaining operations
are the same original first-line cap, or that cap applied twice.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1500000
set_option maxRecDepth 4096
open AlgebraicGeometry CategoryTheory Stacks.Chow
universe u
namespace M9Native.LagrangianKernelPowerSupport
open ChowCapWords GradedLineCapSubring LagrangianFlagPowerStages
open LagrangianKernelDoublePowerPush LagrangianFreeFlagPowerValues

attribute [local instance] LagrangianFlagPowerStages.sourceFinite
  LagrangianFlagPowerStages.kernel1Rank LagrangianFlagPowerStages.kernel1Finite
  LagrangianFlagPowerStages.kernel2Rank LagrangianFlagPowerStages.kernel2Finite
  LagrangianFlagPowerStages.projection1Flat LagrangianFlagPowerStages.projection2Flat
  LagrangianFlagPowerStages.projection3Flat LagrangianFlagPowerStages.projection1LFT
  LagrangianFlagPowerStages.projection2LFT LagrangianFlagPowerStages.projection3LFT

variable {X : Scheme.{u}} (E : X.Modules)
    [SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} E 6]
    (e : E ≅ SheafOfModules.free (R := X.ringCatSheaf) (ULift.{u} (Fin 6)))
    (C : ChowSituation.{u}) (q : X ⟶ C.S) [LocallyOfFiniteType q]

include e

theorem pair43 (k : ℤ) (β : chowGroup C (baseMap1 E C q) k) :
    doublePowerPush E C q 4 3 k β ≍ β :=
  (double_power_three E C q 4 k β).trans (middle_power_four E C q k β)

theorem pair53 (k : ℤ) (β : chowGroup C (baseMap1 E C q) k) :
    doublePowerPush E C q 5 3 k β ≍ -firstCap E C q k β :=
  (double_power_three E C q 5 k β).trans
    (LagrangianKernelDoublePowerPush.middle_power_five (E:=E) (C:=C) (q:=q) (e:=e) k β)

private theorem raised_three (k : ℤ) (β : chowGroup C (baseMap1 E C q) k) :
    raisedMiddlePower E C q 3 k β ≍ β :=
  (raised_middle_heq E C q 3 k β).trans (middle_power_four E C q k β)

private theorem raised_four (k : ℤ) (β : chowGroup C (baseMap1 E C q) k) :
    raisedMiddlePower E C q 4 k β ≍ -firstCap E C q k β :=
  (raised_middle_heq E C q 4 k β).trans
    (LagrangianKernelDoublePowerPush.middle_power_five (E:=E) (C:=C) (q:=q) (e:=e) k β)

theorem pair34 (k : ℤ) (β : chowGroup C (baseMap1 E C q) k) :
    doublePowerPush E C q 3 4 k β ≍ -β := by
  have hM := LagrangianKernelDoublePowerPush.middle_power_zero
    (E:=E) (C:=C) (q:=q) (e:=e) 3 (by decide) (by decide) k β
  have hX : lineFamily C (baseMap1 E C q) (firstLine E) (k+4-(3:ℤ)) 1
      (middlePower E C q 3 k β) ≍ (0 : chowGroup C (baseMap1 E C q) k) := by
    rw [hM, map_zero]
    exact zero_heq_of_degree (by omega)
  have hN := LagrangianKernelDoublePowerPush.neg_heq
    (show (k+4-(3:ℤ))-1=k by omega) (raised_three E e C q k β)
  have hs := LagrangianKernelDoublePowerPush.sub_heq
    (show (k+4-(3:ℤ))-1=k by omega) hN hX
  simp only [sub_zero] at hs
  exact (double_power_four (E:=E) (C:=C) (q:=q) (e:=e) 3 k β).trans hs

theorem pair54 (k : ℤ) (β : chowGroup C (baseMap1 E C q) k) :
    doublePowerPush E C q 5 4 k β ≍ firstCapTwice E C q k β := by
  have hR := raised_middle_zero (E:=E) (C:=C) (q:=q) (e:=e)
    5 (by decide) (by decide) k β
  have hN : -raisedMiddlePower E C q 5 k β ≍
      (0 : chowGroup C (baseMap1 E C q) ((k-1)-1)) := by
    rw [hR, neg_zero]
    exact zero_heq_of_degree (by omega)
  have hM := LagrangianKernelDoublePowerPush.middle_power_five
    (E:=E) (C:=C) (q:=q) (e:=e) k β
  have hX := (lineFamily C (baseMap1 E C q) (firstLine E)).apply_heq
    (show k+4-(5:ℤ)=k-1 by omega) 1 hM
  have hX' : lineFamily C (baseMap1 E C q) (firstLine E) (k+4-(5:ℤ)) 1
      (middlePower E C q 5 k β) ≍ -firstCapTwice E C q k β := by
    simpa only [firstCapTwice, firstCap, map_neg] using hX
  have hs := LagrangianKernelDoublePowerPush.sub_heq
    (show (k+4-(5:ℤ))-1=(k-1)-1 by omega) hN hX'
  simp only [zero_sub, neg_neg] at hs
  exact (double_power_four (E:=E) (C:=C) (q:=q) (e:=e) 5 k β).trans hs

theorem pair35 (k : ℤ) (β : chowGroup C (baseMap1 E C q) k) :
    doublePowerPush E C q 3 5 k β ≍ firstCap E C q k β := by
  have hX := (lineFamily C (baseMap1 E C q) (firstLine E)).apply_heq
    (show (k+4-(3:ℤ))-1=k by omega) 1 (raised_three E e C q k β)
  exact (double_power_five (E:=E) (C:=C) (q:=q) (e:=e) 3 k β).trans hX

theorem pair45 (k : ℤ) (β : chowGroup C (baseMap1 E C q) k) :
    doublePowerPush E C q 4 5 k β ≍ -firstCapTwice E C q k β := by
  have hX := (lineFamily C (baseMap1 E C q) (firstLine E)).apply_heq
    (show (k+4-(4:ℤ))-1=k-1 by omega) 1 (raised_four E e C q k β)
  have hX' : lineFamily C (baseMap1 E C q) (firstLine E) ((k+4-(4:ℤ))-1) 1
      (raisedMiddlePower E C q 4 k β) ≍ -firstCapTwice E C q k β := by
    simpa only [firstCapTwice, firstCap, map_neg] using hX
  exact (double_power_five (E:=E) (C:=C) (q:=q) (e:=e) 4 k β).trans hX'

theorem pair33_zero (k : ℤ) (β : chowGroup C (baseMap1 E C q) k) :
    doublePowerPush E C q 3 3 k β = 0 := by
  have hM := LagrangianKernelDoublePowerPush.middle_power_zero
    (E:=E) (C:=C) (q:=q) (e:=e) 3 (by decide) (by decide) k β
  exact eq_of_heq ((double_power_three E C q 3 k β).trans
    ((heq_of_eq hM).trans (zero_heq_of_degree (by omega))))

theorem pair44_zero (k : ℤ) (β : chowGroup C (baseMap1 E C q) k) :
    doublePowerPush E C q 4 4 k β = 0 := by
  have hN := LagrangianKernelDoublePowerPush.neg_heq
    (show (k+4-(4:ℤ))-1=k-1 by omega) (raised_four E e C q k β)
  simp only [neg_neg] at hN
  have hX := (lineFamily C (baseMap1 E C q) (firstLine E)).apply_heq
    (show k+4-(4:ℤ)=k by omega) 1 (middle_power_four E C q k β)
  have hs := LagrangianKernelDoublePowerPush.sub_heq
    (show (k+4-(4:ℤ))-1=k-1 by omega) hN hX
  simp only [firstCap, sub_self] at hs
  exact eq_of_heq ((double_power_four (E:=E) (C:=C) (q:=q) (e:=e) 4 k β).trans
    (hs.trans (zero_heq_of_degree (by omega))))

theorem pair55_zero (k : ℤ) (β : chowGroup C (baseMap1 E C q) k) :
    doublePowerPush E C q 5 5 k β = 0 := by
  have hR := raised_middle_zero (E:=E) (C:=C) (q:=q) (e:=e)
    5 (by decide) (by decide) k β
  have h := double_power_five (E:=E) (C:=C) (q:=q) (e:=e) 5 k β
  rw [hR, map_zero] at h
  exact eq_of_heq (h.trans (zero_heq_of_degree (by omega)))

theorem double_zero_b_outside (b c : ℕ) (hb : b<3 ∨ 5<b)
    (k : ℤ) (β : chowGroup C (baseMap1 E C q) k) : doublePowerPush E C q b c k β = 0 := by
  by_cases hc0 : c<3
  · exact double_power_lt_three E C q b c hc0 k β
  by_cases hc1 : 5<c
  · exact double_power_gt_five (E:=E) (C:=C) (q:=q) (e:=e) b c hc1 k β
  have hM := LagrangianKernelDoublePowerPush.middle_power_zero
    (E:=E) (C:=C) (q:=q) (e:=e) b (by omega) (by omega) k β
  have hR := raised_middle_zero (E:=E) (C:=C) (q:=q) (e:=e)
    b (by omega) (by omega) k β
  interval_cases c
  · exact eq_of_heq ((double_power_three E C q b k β).trans
      ((heq_of_eq hM).trans (zero_heq_of_degree (by omega))))
  · have h := double_power_four (E:=E) (C:=C) (q:=q) (e:=e) b k β
    rw [hR, hM, map_zero, neg_zero, sub_zero] at h
    exact eq_of_heq (h.trans (zero_heq_of_degree (by omega)))
  · have h := double_power_five (E:=E) (C:=C) (q:=q) (e:=e) b k β
    rw [hR, map_zero] at h
    exact eq_of_heq (h.trans (zero_heq_of_degree (by omega)))

/-- Outside the six displayed pairs the actual double push is zero. -/
theorem double_zero_of_not_six (b c : ℕ)
    (h : ¬(b=4 ∧ c=3 ∨ b=5 ∧ c=3 ∨ b=3 ∧ c=4 ∨ b=5 ∧ c=4 ∨
      b=3 ∧ c=5 ∨ b=4 ∧ c=5))
    (k : ℤ) (β : chowGroup C (baseMap1 E C q) k) : doublePowerPush E C q b c k β = 0 := by
  by_cases hc0 : c<3
  · exact double_power_lt_three E C q b c hc0 k β
  by_cases hc1 : 5<c
  · exact double_power_gt_five (E:=E) (C:=C) (q:=q) (e:=e) b c hc1 k β
  by_cases hb0 : b<3
  · exact double_zero_b_outside E e C q b c (Or.inl hb0) k β
  by_cases hb1 : 5<b
  · exact double_zero_b_outside E e C q b c (Or.inr hb1) k β
  interval_cases b
  · interval_cases c
    · exact pair33_zero E e C q k β
    · exact (h (by simp)).elim
    · exact (h (by simp)).elim
  · interval_cases c
    · exact (h (by simp)).elim
    · exact pair44_zero E e C q k β
    · exact (h (by simp)).elim
  · interval_cases c
    · exact (h (by simp)).elim
    · exact (h (by simp)).elim
    · exact pair55_zero E e C q k β

end M9Native.LagrangianKernelPowerSupport
