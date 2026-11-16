module

public import M9StacksIntegration.LagrangianSecondChernDegree
public import M9StacksIntegration.ChowProjectiveTensorInput
public import M9StacksIntegration.LineFamilyCapPower

/-! Original native Chern-cap commutativity binds the actual H^4 cap
after c2(Q) to the SAME existing mixed-degree class c2(Q) H^4.
The true commutation and all cap/grade comparisons are derived here.
No class, compatibility, or numerical-degree identity is a premise. -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open AlgebraicGeometry CategoryTheory Stacks.Chow Stacks.Chow.GenuineChern
universe u
namespace M9Native.LagrangianSecondChernCapOrder
open LagrangianGrassmannian LagrangianPluckerQuotient LagrangianDegree
open LagrangianQuotientChernRelation LagrangianSecondChernDegree
open ChowCapWords GradedLineCapSubring
variable (K : Type u) [Field K] [CharZero K]

theorem secondChern_commute_H (C : ChowSituation.{u}) (q : space K ⟶ C.S)
    [LocallyOfFiniteType q] : Commute (secondChern K C q) (H K C q) := by
  rw [secondChern, ← firstComponent_eq_H K C q]
  exact commute_homComponent_chernFamily C q
    (quotientOnLG K).target 3 (quotientOnLG K).target 3 2 1

/-- The actual existing mixed class is the original fourfold native
first-Chern cap after the original native second-Chern cap. -/
theorem mixedCap_eq_four_caps_secondChern :
    mixedCap K = capPow (fieldChowSituation K) (projection K)
      (lineCap (fieldChowSituation K) (projection K)
        ⟨determinantLine K, determinantLine_invertible K⟩) 4 4 0 (by omega)
      (chernCap (fieldChowSituation K) 3 (projection K) (quotientOnLG K).target 6
        ⟨2,by decide⟩ (fundamentalChowClass (fieldChowSituation K) (projection K) 6)) := by
  let C := fieldChowSituation K
  let q := projection K
  let L : InvertibleLine (space K) := ⟨determinantLine K, determinantLine_invertible K⟩
  have hprod : secondChern K C q * H K C q ^ 4 =
      H K C q ^ 4 * secondChern K C q :=
    ((secondChern_commute_H K C q).pow_right 4).eq
  have hclass : mixedCap K ≍
      (H K C q ^ 4) 4 4 (secondChern K C q 6 2 (lagrangianOwnFundamental K)) :=
    (heq_of_eq (congrArg (fun a : GradedCapFamily (chowGroup C q) =>
      a 6 6 (lagrangianOwnFundamental K)) hprod)).trans
      (ChowProjectiveTensorInput.homogeneous_mul_apply_heq
        (H K C q ^ 4) (secondChern K C q) 4 2
        (isHomogeneous_homComponent 2 _) 6 (lagrangianOwnFundamental K))
  have hsecond : secondChern K C q 6 2 (lagrangianOwnFundamental K) =
      chernCap C 3 q (quotientOnLG K).target 6 ⟨2,by decide⟩
        (fundamentalChowClass C q 6) := by
    rw [secondChern, homComponent_apply_self,
      chernFamily_apply_of_le C q (quotientOnLG K).target 3 6 (by decide : 2≤3)]
    rfl
  rw [hsecond] at hclass
  exact eq_of_heq (hclass.trans (heq_of_eq
    (LineFamilyCapPower.lineFamily_pow_apply C q L 4 4
      (chernCap C 3 q (quotientOnLG K).target 6 ⟨2,by decide⟩
        (fundamentalChowClass C q 6)))))

/-- Actual integral degree on the original LG, with the original
structural field map and original determinant line. -/
theorem four_caps_secondChern_degree_eq_mixedDegree :
    chowDegree (fieldChowSituation K) (fieldChowSituation_dimensionFunction_eq_zero K)
      (projection K) (IsLocalRing.closedPoint K)
      (capPow (fieldChowSituation K) (projection K)
        (lineCap (fieldChowSituation K) (projection K)
          ⟨determinantLine K, determinantLine_invertible K⟩) 4 4 0 (by omega)
        (chernCap (fieldChowSituation K) 3 (projection K) (quotientOnLG K).target 6
          ⟨2,by decide⟩ (fundamentalChowClass (fieldChowSituation K) (projection K) 6))) =
      mixedDegree K := by
  rw [← mixedCap_eq_four_caps_secondChern]
  rfl

end M9Native.LagrangianSecondChernCapOrder
