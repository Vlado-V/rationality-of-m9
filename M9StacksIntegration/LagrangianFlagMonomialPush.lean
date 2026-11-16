module

public import M9StacksIntegration.LagrangianKernelPowerSupport

/-!
# Genuine free-six flag push of degree-twelve monomials

The six surviving monomials are pushed to the SAME original input
class, with their proved signs. The actual first projective top-power
normalization closes the two original kernel-push computation.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1500000
set_option maxRecDepth 4096
open AlgebraicGeometry CategoryTheory Stacks.Chow
universe u
namespace M9Native.LagrangianFlagMonomialPush
open ChowCapWords GradedLineCapSubring LagrangianFlagPowerStages
open LagrangianKernelDoublePowerPush LagrangianKernelPowerSupport

attribute [local instance] LagrangianFlagPowerStages.sourceFinite
  LagrangianFlagPowerStages.kernel1Rank LagrangianFlagPowerStages.kernel1Finite
  LagrangianFlagPowerStages.kernel2Rank LagrangianFlagPowerStages.kernel2Finite
  LagrangianFlagPowerStages.projection1Flat LagrangianFlagPowerStages.projection2Flat
  LagrangianFlagPowerStages.projection3Flat LagrangianFlagPowerStages.projection1LFT
  LagrangianFlagPowerStages.projection2LFT LagrangianFlagPowerStages.projection3LFT

variable {X : Scheme.{u}} (E : X.Modules)
    [hE : SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} E 6]
    (C : ChowSituation.{u}) (q : X ⟶ C.S) [LocallyOfFiniteType q]

/-- Literal three proper pushes of the three actual interleaved powers,
with only the degree-twelve output transport. -/
def monomialPush (a b c : ℕ) (hdeg : a+b+c=12) (k : ℤ) (α : chowGroup C q k) :
    chowGroup C q k :=
  chowGroupCast C q (by omega)
    (triplePush E C q (((k+5-(a:ℤ))+4-(b:ℤ))+3-(c:ℤ))
      (powerClass3 E C q a b c k α))

theorem rawTriplePush_eq_double (a b c : ℕ) (k : ℤ) (α : chowGroup C q k) :
    triplePush E C q (((k+5-(a:ℤ))+4-(b:ℤ))+3-(c:ℤ))
        (powerClass3 E C q a b c k α) ≍
      push1 E C q ((k+5-(a:ℤ))+7-(b:ℤ)-(c:ℤ))
        (doublePowerPush E C q b c (k+5-(a:ℤ)) (powerClass1 E C q a k α)) := by
  have h3 := push3_powerClass E C q a b c k α
  have h2 : doublePowerPush E C q b c (k+5-(a:ℤ)) (powerClass1 E C q a k α) ≍
      push2 E C q (((k+5-(a:ℤ))+4-(b:ℤ))+3-(c:ℤ))
        (push3 E C q (((k+5-(a:ℤ))+4-(b:ℤ))+3-(c:ℤ))
          (powerClass3 E C q a b c k α)) := by
    refine ChowFlagThreeNormalizer.properPush_heq C (baseMap2 E C q) (baseMap1 E C q)
      (projection2 E) rfl (by omega) ?_
    exact (chowGroupCast_heq C (baseMap2 E C q) _ _).trans (heq_of_eq h3).symm
  exact ChowFlagThreeNormalizer.properPush_heq C (baseMap1 E C q) q
    (projection1 E) rfl (by omega) h2.symm

theorem monomialPush_eq_double (a b c : ℕ) (hdeg : a+b+c=12)
    (k : ℤ) (α : chowGroup C q k) :
    monomialPush E C q a b c hdeg k α ≍
      push1 E C q ((k+5-(a:ℤ))+7-(b:ℤ)-(c:ℤ))
        (doublePowerPush E C q b c (k+5-(a:ℤ)) (powerClass1 E C q a k α)) :=
  (chowGroupCast_heq C q _ _).trans (rawTriplePush_eq_double E C q a b c k α)

theorem firstCap_powerClass1_succ (a : ℕ) (k : ℤ) (α : chowGroup C q k) :
    firstCap E C q (k+5-(a:ℤ)) (powerClass1 E C q a k α) ≍
      powerClass1 E C q (a+1) k α := by
  have h := LineFamilyCapPower.lineFamily_pow_apply_heq C (baseMap1 E C q) (firstLine E)
    1 (k+5-(a:ℤ)) (k+5-((a+1:ℕ):ℤ)) (by omega) (powerClass1 E C q a k α)
  rw [pow_one] at h
  have hs : capPow C (baseMap1 E C q) (lineCap C (baseMap1 E C q) (firstLine E))
      1 (k+5-(a:ℤ)) (k+5-((a+1:ℕ):ℤ)) (by omega) (powerClass1 E C q a k α) =
      powerClass1 E C q (a+1) k α := by
    dsimp only [powerClass1]
    rw [capPow_capPow]
  exact h.trans (heq_of_eq hs)

theorem firstCapTwice_powerClass1 (a : ℕ) (k : ℤ) (α : chowGroup C q k) :
    firstCapTwice E C q (k+5-(a:ℤ)) (powerClass1 E C q a k α) ≍
      powerClass1 E C q (a+2) k α := by
  have h := (lineFamily C (baseMap1 E C q) (firstLine E)).apply_heq
    (show (k+5-(a:ℤ))-1=k+5-((a+1:ℕ):ℤ) by omega) 1
    (firstCap_powerClass1_succ E C q a k α)
  refine h.trans ?_
  exact firstCap_powerClass1_succ E C q (a+1) k α

theorem outer_top (k : ℤ) (α : chowGroup C q k) :
    push1 E C q (k+5-(5:ℤ)) (powerClass1 E C q 5 k α) ≍ α :=
  LagrangianProjectivePowerPush.powerPush_top E 5 C q k α

theorem outer_cap_top (k : ℤ) (α : chowGroup C q k) :
    push1 E C q ((k+5-(4:ℤ))-1)
        (firstCap E C q (k+5-(4:ℤ)) (powerClass1 E C q 4 k α)) ≍ α :=
  (ChowFlagThreeNormalizer.properPush_heq C (baseMap1 E C q) q (projection1 E) rfl
    (by omega) (firstCap_powerClass1_succ E C q 4 k α)).trans (outer_top E C q k α)

theorem outer_twice_top (k : ℤ) (α : chowGroup C q k) :
    push1 E C q (((k+5-(3:ℤ))-1)-1)
        (firstCapTwice E C q (k+5-(3:ℤ)) (powerClass1 E C q 3 k α)) ≍ α :=
  (ChowFlagThreeNormalizer.properPush_heq C (baseMap1 E C q) q (projection1 E) rfl
    (by omega) (firstCapTwice_powerClass1 E C q 3 k α)).trans (outer_top E C q k α)

variable (e : E ≅ SheafOfModules.free (R := X.ringCatSheaf) (ULift.{u} (Fin 6)))
include e

theorem push543 (k : ℤ) (α : chowGroup C q k) :
    monomialPush E C q 5 4 3 (by decide) k α = α := by
  apply eq_of_heq
  refine (monomialPush_eq_double E C q 5 4 3 (by decide) k α).trans ?_
  refine (ChowFlagThreeNormalizer.properPush_heq C (baseMap1 E C q) q (projection1 E) rfl
    (by omega) (pair43 (E:=E) (e:=e) (C:=C) (q:=q)
      (k+5-(5:ℤ)) (powerClass1 E C q 5 k α))).trans ?_
  exact outer_top E C q k α

theorem push453 (k : ℤ) (α : chowGroup C q k) :
    monomialPush E C q 4 5 3 (by decide) k α = -α := by
  apply eq_of_heq
  refine (monomialPush_eq_double E C q 4 5 3 (by decide) k α).trans ?_
  refine (ChowFlagThreeNormalizer.properPush_heq C (baseMap1 E C q) q (projection1 E) rfl
    (by omega) (pair53 (E:=E) (e:=e) (C:=C) (q:=q)
      (k+5-(4:ℤ)) (powerClass1 E C q 4 k α))).trans ?_
  rw [map_neg]
  exact LagrangianKernelDoublePowerPush.neg_heq (by omega) (outer_cap_top E C q k α)

theorem push534 (k : ℤ) (α : chowGroup C q k) :
    monomialPush E C q 5 3 4 (by decide) k α = -α := by
  apply eq_of_heq
  refine (monomialPush_eq_double E C q 5 3 4 (by decide) k α).trans ?_
  refine (ChowFlagThreeNormalizer.properPush_heq C (baseMap1 E C q) q (projection1 E) rfl
    (by omega) (pair34 (E:=E) (e:=e) (C:=C) (q:=q)
      (k+5-(5:ℤ)) (powerClass1 E C q 5 k α))).trans ?_
  rw [map_neg]
  exact LagrangianKernelDoublePowerPush.neg_heq (by omega) (outer_top E C q k α)

theorem push354 (k : ℤ) (α : chowGroup C q k) :
    monomialPush E C q 3 5 4 (by decide) k α = α := by
  apply eq_of_heq
  refine (monomialPush_eq_double E C q 3 5 4 (by decide) k α).trans ?_
  refine (ChowFlagThreeNormalizer.properPush_heq C (baseMap1 E C q) q (projection1 E) rfl
    (by omega) (pair54 (E:=E) (e:=e) (C:=C) (q:=q)
      (k+5-(3:ℤ)) (powerClass1 E C q 3 k α))).trans ?_
  exact outer_twice_top E C q k α

theorem push435 (k : ℤ) (α : chowGroup C q k) :
    monomialPush E C q 4 3 5 (by decide) k α = α := by
  apply eq_of_heq
  refine (monomialPush_eq_double E C q 4 3 5 (by decide) k α).trans ?_
  refine (ChowFlagThreeNormalizer.properPush_heq C (baseMap1 E C q) q (projection1 E) rfl
    (by omega) (pair35 (E:=E) (e:=e) (C:=C) (q:=q)
      (k+5-(4:ℤ)) (powerClass1 E C q 4 k α))).trans ?_
  exact outer_cap_top E C q k α

theorem push345 (k : ℤ) (α : chowGroup C q k) :
    monomialPush E C q 3 4 5 (by decide) k α = -α := by
  apply eq_of_heq
  refine (monomialPush_eq_double E C q 3 4 5 (by decide) k α).trans ?_
  refine (ChowFlagThreeNormalizer.properPush_heq C (baseMap1 E C q) q (projection1 E) rfl
    (by omega) (pair45 (E:=E) (e:=e) (C:=C) (q:=q)
      (k+5-(3:ℤ)) (powerClass1 E C q 3 k α))).trans ?_
  rw [map_neg]
  exact LagrangianKernelDoublePowerPush.neg_heq (by omega) (outer_twice_top E C q k α)

/-- Every other degree-twelve monomial has actual geometric push zero. -/
theorem monomialPush_zero (a b c : ℕ) (hdeg : a+b+c=12)
    (h : ¬(a=5 ∧ b=4 ∧ c=3 ∨ a=4 ∧ b=5 ∧ c=3 ∨ a=5 ∧ b=3 ∧ c=4 ∨
      a=3 ∧ b=5 ∧ c=4 ∨ a=4 ∧ b=3 ∧ c=5 ∨ a=3 ∧ b=4 ∧ c=5))
    (k : ℤ) (α : chowGroup C q k) : monomialPush E C q a b c hdeg k α = 0 := by
  have hbc : ¬(b=4 ∧ c=3 ∨ b=5 ∧ c=3 ∨ b=3 ∧ c=4 ∨ b=5 ∧ c=4 ∨
      b=3 ∧ c=5 ∨ b=4 ∧ c=5) := by omega
  have hz := double_zero_of_not_six (E:=E) (e:=e) (C:=C) (q:=q) b c hbc
    (k+5-(a:ℤ)) (powerClass1 E C q a k α)
  have hp := monomialPush_eq_double E C q a b c hdeg k α
  rw [hz, map_zero] at hp
  exact eq_of_heq (hp.trans (LagrangianFreeFlagPowerValues.zero_heq_of_degree (by omega)))

end M9Native.LagrangianFlagMonomialPush
