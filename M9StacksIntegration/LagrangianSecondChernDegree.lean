module

public import M9StacksIntegration.LagrangianQuotientChernRelation
public import M9StacksIntegration.ChowLinePowerCap
public import M9StacksIntegration.LagrangianPluckerCapDegree

/-!
# The original second-Chern mixed cap degree and actual Plucker degree

This derives twice deg(c2(Q) H^4) = deg(H^6) on the literal original LG.
The right side is the original native Plucker cap degree, rather than
an assigned intersection functional.  No numerical value is assumed.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false

open AlgebraicGeometry CategoryTheory Stacks.Chow

universe u

namespace M9Native.LagrangianSecondChernDegree

open LagrangianGrassmannian LagrangianPluckerQuotient LagrangianDegree
open LagrangianQuotientChernRelation LagrangianActualDegree

variable (K : Type u) [Field K] [CharZero K]

/-- The literal mixed cap on the original six-dimensional fundamental class. -/
def mixedCap : chowGroup (fieldChowSituation K) (projection K) 0 :=
  (secondChern K (fieldChowSituation K) (projection K) *
    H K (fieldChowSituation K) (projection K) ^ 4) 6 6 (lagrangianOwnFundamental K)

/-- Its original integral degree, using the actual structural proper map. -/
def mixedDegree : ℤ :=
  chowDegree (fieldChowSituation K) (fieldChowSituation_dimensionFunction_eq_zero K)
    (projection K) (IsLocalRing.closedPoint K) (mixedCap K)

set_option maxHeartbeats 800000 in
/-- The sixth operational power is exactly the original native sixfold cap. -/
theorem H_sixth_cap_eq_iterated :
    (H K (fieldChowSituation K) (projection K) ^ 6) 6 6 (lagrangianOwnFundamental K) =
      iteratedFirstChernCap K (projection K) (fun _ : Fin 6 => determinantLine K)
        (lagrangianOwnFundamental K) := by
  dsimp only [H]
  have h := ChowLinePowerCap.lineFamily_pow_heq_iteratedFirstChernCap K (projection K)
    ⟨determinantLine K, determinantLine_invertible K⟩ 6 (lagrangianOwnFundamental K)
  exact eq_of_heq h

/-- The actual integral degree relation, without division in any Chow group. -/
theorem two_mul_mixedDegree_eq_pluckerCapDegree :
    2 * mixedDegree K = pluckerCapDegree K := by
  have h := congrArg (fun A : GradedCapFamily (chowGroup (fieldChowSituation K) (projection K)) =>
    A 6 6 (lagrangianOwnFundamental K))
    (H_sixth_eq_two_secondChern_H_fourth K (fieldChowSituation K) (projection K))
  rw [H_sixth_cap_eq_iterated K] at h
  have hd := congrArg
    (chowDegree (fieldChowSituation K) (fieldChowSituation_dimensionFunction_eq_zero K)
      (projection K) (IsLocalRing.closedPoint K)) h
  change pluckerCapDegree K =
    chowDegree (fieldChowSituation K) (fieldChowSituation_dimensionFunction_eq_zero K)
      (projection K) (IsLocalRing.closedPoint K) ((2 : ℤ) • mixedCap K) at hd
  rw [map_zsmul, zsmul_eq_mul] at hd
  exact hd.symm

end M9Native.LagrangianSecondChernDegree
