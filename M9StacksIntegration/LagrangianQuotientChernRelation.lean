module

public import M9StacksIntegration.SymplecticQuotientChernRelation
public import M9StacksIntegration.ChowDeterminantFirstComponent
public import M9StacksIntegration.SymplecticQuotientKernel

/-!
# The actual universal LG quotient satisfies the integral Chern relation

Q is the original universal quotient pulled to the original LG, and H
is the original determinant-line cap.  The actual short exact sequence
is constructed by the symplectic quotient kernel theorem.  No exactness,
Chern identity, numerical degree or Schubert cycle-class premise is supplied.

The second Chern family is named as such: its geometric identification
with the rank-drop Schubert scheme is a separate assertion.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false

open AlgebraicGeometry CategoryTheory Stacks.Chow Stacks.Chow.GenuineChern

universe u

namespace M9Native.LagrangianQuotientChernRelation

open LagrangianGrassmannian LagrangianPluckerQuotient

variable (K : Type u) [Field K] (C : ChowSituation.{u})
  (q : space K ⟶ C.S) [LocallyOfFiniteType q]

/-- The original Plucker determinant-line cap, on original integral Chow groups. -/
def H : GradedCapFamily (chowGroup C q) :=
  GradedLineCapSubring.lineFamily C q
    ⟨determinantLine K, determinantLine_invertible K⟩

/-- The actual second Chern cap of the original universal quotient. -/
def secondChern : GradedCapFamily (chowGroup C q) :=
  homComponent 2 (chernFamily C q (quotientOnLG K).target 3)

/-- Native determinant normalization binds H to c1 of the SAME quotient. -/
theorem firstComponent_eq_H :
    homComponent 1 (chernFamily C q (quotientOnLG K).target 3) = H K C q := by
  let _ : SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} (quotientOnLG K).target (2+1) :=
    (quotientOnLG K).finiteLocallyFree
  exact ChowDeterminantFirstComponent.firstComponent_eq_lineFamily C q (quotientOnLG K).target 2

/-- The actual universal sequence derives the genuine total inverse relation. -/
theorem signed_total_mul_eq_one :
    capFamilySignScale (chernFamily C q (quotientOnLG K).target 3) *
      chernFamily C q (quotientOnLG K).target 3 = 1 := by
  let S := SymplecticQuotientKernel.lagrangianSequence K
  exact SymplecticQuotientChernRelation.signed_chern_mul_eq_one C q
    (quotientOnLG K).target 3 S.X₂ S.f S.g S.zero
    (SymplecticQuotientKernel.lagrangianSequence_shortExact K) (Iso.refl _)

/-- The true integral operational identity H squared = twice c2(Q). -/
theorem H_square_eq_two_secondChern :
    H K C q * H K C q = (2 : ℤ) • secondChern K C q := by
  have h := SymplecticQuotientChernRelation.first_square_eq_two_second
    (chernFamily C q (quotientOnLG K).target 3)
    (chernFamily_apply_zero C q (quotientOnLG K).target 3) (signed_total_mul_eq_one K C q)
  simpa only [firstComponent_eq_H, secondChern] using h

/-- The genuine sixfold integral cap relation, before any degree map. -/
theorem H_sixth_eq_two_secondChern_H_fourth :
    H K C q ^ 6 = (2 : ℤ) • (secondChern K C q * H K C q ^ 4) := by
  have h := SymplecticQuotientChernRelation.first_sixth_eq_two_second_first_fourth
    (chernFamily C q (quotientOnLG K).target 3)
    (chernFamily_apply_zero C q (quotientOnLG K).target 3) (signed_total_mul_eq_one K C q)
  simpa only [firstComponent_eq_H, secondChern] using h

/-- The same actual quotient relation after EVERY scheme pullback,
including nonreduced tests; no flatness of the test map is needed. -/
theorem pullback_first_square_eq_two_second
    {T : Scheme.{u}} (l : T ⟶ space K) (qT : T ⟶ C.S) [LocallyOfFiniteType qT] :
    letI := LagrangianUniversalSections.bundle_rank K l
    homComponent 1 (chernFamily C qT (LagrangianUniversalSections.bundle K l) 3) *
        homComponent 1 (chernFamily C qT (LagrangianUniversalSections.bundle K l) 3) =
      (2 : ℤ) • homComponent 2 (chernFamily C qT (LagrangianUniversalSections.bundle K l) 3) := by
  let _ := LagrangianUniversalSections.bundle_rank K l
  let S := SymplecticQuotientKernel.universalSequence K l
  exact SymplecticQuotientChernRelation.chern_first_square_eq_two_second C qT
    (LagrangianUniversalSections.bundle K l) 3 S.X₂ S.f S.g S.zero
    (SymplecticQuotientKernel.universalSequence_shortExact K l) (Iso.refl _)

end M9Native.LagrangianQuotientChernRelation
