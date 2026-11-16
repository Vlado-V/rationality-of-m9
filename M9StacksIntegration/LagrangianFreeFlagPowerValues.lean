module

public import M9StacksIntegration.LagrangianFlagPowerStages
public import M9StacksIntegration.LagrangianFreeTautologicalInverse
public import M9StacksIntegration.ChowFlagMomentCoefficients

/-!
# Actual finite power values on the two original free-six kernels

The genuine inverse identities of the actual free-trivialized source
and its actual kernel rows are combined with the proved geometric
moment theorem. The finite values below are conclusions on every actual
Chow input. No numerical push or inverse identity is an assumption.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1500000
set_option maxRecDepth 4096
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Stacks.Chow
open Stacks.Chow.GenuineChern
universe u v
namespace M9Native.LagrangianFreeFlagPowerValues
open GradedCapVirtualSchur ChowCapWords GradedLineCapSubring
open LagrangianFlagPowerStages

section Generic
variable {G : ℤ → Type v} [∀ k, AddCommGroup (G k)]

theorem zero_heq_of_degree {k l : ℤ} (h : k=l) : (0 : G k) ≍ (0 : G l) := by
  cases h
  rfl

theorem one_sub_coeff_one (x : GradedCapFamily G) (k : ℤ) (β : G k) :
    (1-x) k 1 β = -(x k 1 β) := by
  simp only [Pi.sub_apply, AddMonoidHom.sub_apply,
    gradedCap_one_of_ne (by decide : (1:ℕ)≠0), AddMonoidHom.zero_apply, zero_sub,
    AddMonoidHom.neg_apply]

theorem one_sub_coeff_gt (x : GradedCapFamily G) (hx : x.IsHomogeneous 1)
    (j : ℕ) (hj : 1<j) (k : ℤ) (β : G k) : (1-x) k j β = 0 := by
  simp only [Pi.sub_apply, AddMonoidHom.sub_apply,
    gradedCap_one_of_ne (by omega : j≠0), hx k j (by omega),
    AddMonoidHom.zero_apply, sub_zero]

theorem two_factor_eq (y x : GradedCapFamily G) :
    (1-y)*(1-x) = 1-y-x+y*x := by noncomm_ring

theorem two_factor_coeff_one (y x : GradedCapFamily G)
    (hy : y.IsHomogeneous 1) (hx : x.IsHomogeneous 1) (k : ℤ) (β : G k) :
    ((1-y)*(1-x)) k 1 β = -(y k 1 β) - x k 1 β := by
  rw [two_factor_eq]
  simp only [Pi.add_apply, Pi.sub_apply, AddMonoidHom.add_apply, AddMonoidHom.sub_apply,
    gradedCap_one_of_ne (by decide : (1:ℕ)≠0),
    (hy.mul hx) k 1 (by decide : (1:ℕ)≠2), AddMonoidHom.zero_apply, zero_sub, add_zero,
    AddMonoidHom.neg_apply]

theorem two_factor_coeff_two (y x : GradedCapFamily G)
    (hy : y.IsHomogeneous 1) (hx : x.IsHomogeneous 1) (k : ℤ) (β : G k) :
    ((1-y)*(1-x)) k 2 β = (y*x) k 2 β := by
  rw [two_factor_eq]
  simp only [Pi.add_apply, Pi.sub_apply, AddMonoidHom.add_apply, AddMonoidHom.sub_apply,
    gradedCap_one_of_ne (by decide : (2:ℕ)≠0),
    hy k 2 (by decide : (2:ℕ)≠1), hx k 2 (by decide : (2:ℕ)≠1),
    AddMonoidHom.zero_apply, sub_zero, zero_add]

theorem two_factor_coeff_gt (y x : GradedCapFamily G)
    (hy : y.IsHomogeneous 1) (hx : x.IsHomogeneous 1)
    (j : ℕ) (hj : 2<j) (k : ℤ) (β : G k) : ((1-y)*(1-x)) k j β = 0 := by
  rw [two_factor_eq]
  simp only [Pi.add_apply, Pi.sub_apply, AddMonoidHom.add_apply, AddMonoidHom.sub_apply,
    gradedCap_one_of_ne (by omega : j≠0), hy k j (by omega), hx k j (by omega),
    (hy.mul hx) k j (by omega : j≠1+1), AddMonoidHom.zero_apply, sub_zero, zero_add]

end Generic

attribute [local instance] LagrangianFlagPowerStages.sourceFinite
  LagrangianFlagPowerStages.kernel1Rank LagrangianFlagPowerStages.kernel1Finite
  LagrangianFlagPowerStages.kernel2Rank LagrangianFlagPowerStages.kernel2Finite
  LagrangianFlagPowerStages.projection1Flat LagrangianFlagPowerStages.projection2Flat
  LagrangianFlagPowerStages.projection3Flat LagrangianFlagPowerStages.projection1LFT
  LagrangianFlagPowerStages.projection2LFT LagrangianFlagPowerStages.projection3LFT

variable {X : Scheme.{u}} (E : X.Modules)
    [hE : SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} E 6]
    (e : E ≅ SheafOfModules.free (R := X.ringCatSheaf) (ULift.{u} (Fin 6)))
    (C : ChowSituation.{u}) (q : X ⟶ C.S) [LocallyOfFiniteType q]

include e

private theorem middle_moment_eq :
    @ChowProjectiveMoments.momentFamily (space1 E) (kernel1 E) 4
      (LagrangianFlagPowerStages.kernel1Rank E) C (baseMap1 E C q) inferInstance =
        1-lineFamily C (baseMap1 E C q) (firstLine E) := by
  letI := Stacks.Chow.isFiniteLocallyFreeOfRank_bundleTwist E
  let hM := @ChowProjectiveMomentInverse.momentFamily_eq_signed_inverse
    (space1 E) (kernel1 E) 4 (LagrangianFlagPowerStages.kernel1Rank E)
    C (baseMap1 E C q) inferInstance
  let hI := LagrangianFreeTautologicalInverse.inverseFamily_kernel_of_iso_free
    E 5 C e (baseMap1 E C q)
  let hS := congrArg capFamilySignScale hI
  let hL := ChowFlagMomentCoefficients.signed_chernFamily_line
    C (baseMap1 E C q) (firstLine E)
  exact hM.trans (hS.trans hL)

private theorem inner_moment_eq :
    @ChowProjectiveMoments.momentFamily (space2 E) (kernel2 E) 3
      (LagrangianFlagPowerStages.kernel2Rank E) C (baseMap2 E C q) inferInstance =
        (1-lineFamily C (baseMap2 E C q) (secondLine E)) *
          (1-lineFamily C (baseMap2 E C q) (firstLineAt2 E)) := by
  letI := Stacks.Chow.isFiniteLocallyFreeOfRank_bundleTwist E
  letI := Stacks.Chow.isFiniteLocallyFreeOfRank_bundleTwist (kernel1 E)
  letI := AlgebraicGeometry.isFiniteLocallyFreeOfRank_pullback
    (projection2 E) (bundleTwist E) 1
  letI := AlgebraicGeometry.isFiniteLocallyFreeOfRank_pullback
    (projection2 E) (kernel1 E) 5
  let hM := @ChowProjectiveMomentInverse.momentFamily_eq_signed_inverse
    (space2 E) (kernel2 E) 3 (LagrangianFlagPowerStages.kernel2Rank E)
    C (baseMap2 E C q) inferInstance
  let hK := @ChowTautologicalKernelInverse.inverseFamily_kernel
    (space1 E) (kernel1 E) 4 (LagrangianFlagPowerStages.kernel1Rank E) C (baseMap2 E C q)
  let hP := LagrangianFreeTautologicalInverse.inverseFamily_pullback_kernel_of_iso_free
    E 5 C e (projection2 E) (baseMap2 E C q)
  let hI := hK.trans (congrArg (fun a : GradedCapFamily (chowGroup C (baseMap2 E C q)) =>
    chernFamily C (baseMap2 E C q) (bundleTwist (kernel1 E)) 1 * a) hP)
  have hS := congrArg capFamilySignScale hI
  rw [capFamilySignScale_mul] at hS
  let hY := ChowFlagMomentCoefficients.signed_chernFamily_line
    C (baseMap2 E C q) (secondLine E)
  let hX := ChowFlagMomentCoefficients.signed_chernFamily_line
    C (baseMap2 E C q) (firstLineAt2 E)
  let hProduct := congrArg₂ (fun a b : GradedCapFamily (chowGroup C (baseMap2 E C q)) => a*b)
    hY hX
  exact hM.trans (hS.trans hProduct)

/-- The actual fifth power on the first kernel is minus the original
first quotient-line cap, on every genuine Chow class. -/
theorem middle_power_five (k : ℤ) (β : chowGroup C (baseMap1 E C q) k) :
    @LagrangianProjectivePowerPush.powerPush (space1 E) (kernel1 E) 4
      (LagrangianFlagPowerStages.kernel1Rank E) C (baseMap1 E C q) inferInstance 5 k β ≍
        -(lineFamily C (baseMap1 E C q) (firstLine E) k 1 β) := by
  have h := @LagrangianProjectivePowerPush.powerPush_eq_moment
    (space1 E) (kernel1 E) 4 (LagrangianFlagPowerStages.kernel1Rank E)
    C (baseMap1 E C q) inferInstance 5 1 (by decide) k β
  change HEq _ (@ChowProjectiveMoments.momentFamily (space1 E) (kernel1 E) 4
    (LagrangianFlagPowerStages.kernel1Rank E) C (baseMap1 E C q) inferInstance k 1 β) at h
  rw [middle_moment_eq E e C q, one_sub_coeff_one] at h
  exact h

/-- Every middle-stage power other than four and five vanishes. -/
theorem middle_power_zero (b : ℕ) (h4 : b≠4) (h5 : b≠5)
    (k : ℤ) (β : chowGroup C (baseMap1 E C q) k) :
    @LagrangianProjectivePowerPush.powerPush (space1 E) (kernel1 E) 4
      (LagrangianFlagPowerStages.kernel1Rank E) C (baseMap1 E C q) inferInstance b k β = 0 := by
  by_cases hb : b<4
  · exact @LagrangianProjectivePowerPush.powerPush_eq_zero_of_lt
      (space1 E) (kernel1 E) 4 (LagrangianFlagPowerStages.kernel1Rank E)
      C (baseMap1 E C q) inferInstance b hb k β
  · have hj : 1<b-4 := by omega
    have h := @LagrangianProjectivePowerPush.powerPush_eq_moment
      (space1 E) (kernel1 E) 4 (LagrangianFlagPowerStages.kernel1Rank E)
      C (baseMap1 E C q) inferInstance b (b-4) (by omega) k β
    change HEq _ (@ChowProjectiveMoments.momentFamily (space1 E) (kernel1 E) 4
      (LagrangianFlagPowerStages.kernel1Rank E) C (baseMap1 E C q) inferInstance k (b-4) β) at h
    rw [middle_moment_eq E e C q,
      one_sub_coeff_gt _ (lineFamily_homogeneous C (baseMap1 E C q) (firstLine E)) _ hj] at h
    exact eq_of_heq (h.trans (zero_heq_of_degree (G:=chowGroup C (baseMap1 E C q))
      (k:=k-((b-4:ℕ):ℤ)) (l:=k+4-(b:ℤ)) (by omega)))

/-- The inner fourth power is minus the two actual original line caps. -/
theorem inner_power_four (k : ℤ) (β : chowGroup C (baseMap2 E C q) k) :
    @LagrangianProjectivePowerPush.powerPush (space2 E) (kernel2 E) 3
      (LagrangianFlagPowerStages.kernel2Rank E) C (baseMap2 E C q) inferInstance 4 k β ≍
        -(lineFamily C (baseMap2 E C q) (secondLine E) k 1 β) -
          lineFamily C (baseMap2 E C q) (firstLineAt2 E) k 1 β := by
  have h := @LagrangianProjectivePowerPush.powerPush_eq_moment
    (space2 E) (kernel2 E) 3 (LagrangianFlagPowerStages.kernel2Rank E)
    C (baseMap2 E C q) inferInstance 4 1 (by decide) k β
  change HEq _ (@ChowProjectiveMoments.momentFamily (space2 E) (kernel2 E) 3
    (LagrangianFlagPowerStages.kernel2Rank E) C (baseMap2 E C q) inferInstance k 1 β) at h
  rw [inner_moment_eq E e C q,
    two_factor_coeff_one _ _ (lineFamily_homogeneous C (baseMap2 E C q) (secondLine E))
      (lineFamily_homogeneous C (baseMap2 E C q) (firstLineAt2 E))] at h
  exact h

/-- The inner fifth power is the literal ordered product of the two
actual line caps. The order is retained, without a commutation premise. -/
theorem inner_power_five (k : ℤ) (β : chowGroup C (baseMap2 E C q) k) :
    @LagrangianProjectivePowerPush.powerPush (space2 E) (kernel2 E) 3
      (LagrangianFlagPowerStages.kernel2Rank E) C (baseMap2 E C q) inferInstance 5 k β ≍
        (lineFamily C (baseMap2 E C q) (secondLine E) *
          lineFamily C (baseMap2 E C q) (firstLineAt2 E)) k 2 β := by
  have h := @LagrangianProjectivePowerPush.powerPush_eq_moment
    (space2 E) (kernel2 E) 3 (LagrangianFlagPowerStages.kernel2Rank E)
    C (baseMap2 E C q) inferInstance 5 2 (by decide) k β
  change HEq _ (@ChowProjectiveMoments.momentFamily (space2 E) (kernel2 E) 3
    (LagrangianFlagPowerStages.kernel2Rank E) C (baseMap2 E C q) inferInstance k 2 β) at h
  rw [inner_moment_eq E e C q,
    two_factor_coeff_two _ _ (lineFamily_homogeneous C (baseMap2 E C q) (secondLine E))
      (lineFamily_homogeneous C (baseMap2 E C q) (firstLineAt2 E))] at h
  exact h

/-- Every inner-stage power above five vanishes on every original class. -/
theorem inner_power_gt_five (c : ℕ) (hc : 5<c)
    (k : ℤ) (β : chowGroup C (baseMap2 E C q) k) :
    @LagrangianProjectivePowerPush.powerPush (space2 E) (kernel2 E) 3
      (LagrangianFlagPowerStages.kernel2Rank E) C (baseMap2 E C q) inferInstance c k β = 0 := by
  have hj : 2<c-3 := by omega
  have h := @LagrangianProjectivePowerPush.powerPush_eq_moment
    (space2 E) (kernel2 E) 3 (LagrangianFlagPowerStages.kernel2Rank E)
    C (baseMap2 E C q) inferInstance c (c-3) (by omega) k β
  change HEq _ (@ChowProjectiveMoments.momentFamily (space2 E) (kernel2 E) 3
    (LagrangianFlagPowerStages.kernel2Rank E) C (baseMap2 E C q) inferInstance k (c-3) β) at h
  rw [inner_moment_eq E e C q,
    two_factor_coeff_gt _ _ (lineFamily_homogeneous C (baseMap2 E C q) (secondLine E))
      (lineFamily_homogeneous C (baseMap2 E C q) (firstLineAt2 E)) _ hj] at h
  exact eq_of_heq (h.trans (zero_heq_of_degree (G:=chowGroup C (baseMap2 E C q))
    (k:=k-((c-3:ℕ):ℤ)) (l:=k+3-(c:ℤ)) (by omega)))

end M9Native.LagrangianFreeFlagPowerValues
