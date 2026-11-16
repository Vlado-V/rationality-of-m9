module

public import M9StacksIntegration.LagrangianAdmissibleCharts
public import M9StacksIntegration.MukaiConormalBigCellSections

/-! The literal first-column equations on the eight symplectic charts,
and the polynomial quotient which erases one symmetric row and column. -/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 4096

open AlgebraicGeometry CategoryTheory Matrix

universe u

namespace M9Native.LagrangianCommonKernelChartAlgebra

open LagrangianAdmissibleMinors LagrangianAdmissibleCharts LagrangianMatrixChart
open LagrangianTransitivity

variable (R : Type u) [CommRing R]

theorem swap_inverse_matrix (s : Choice) :
    ((LagrangianAdmissibleCharts.swap R s)⁻¹).val =
      Matrix.fromBlocks (Matrix.diagonal (keep R s)) (Matrix.diagonal (take R s))
        (-Matrix.diagonal (take R s)) (Matrix.diagonal (keep R s)) := by
  rw [SymplecticGroup.coe_inv]
  simp [LagrangianAdmissibleCharts.swap,swapMatrix,Matrix.J,Matrix.fromBlocks_transpose,Matrix.fromBlocks_neg,
    Matrix.fromBlocks_multiply]

/-- The sign is the actual inverse-swap sign: a chosen f-pivot sends
the original e-vector to minus the opposite coordinate vector. -/
theorem swap_inverse_column (s : Choice) (j : Fin 3) :
    (matrixSix R (LagrangianAdmissibleCharts.swap R s)⁻¹).col (j.castAdd 3) =
      if s j then -Pi.single (Fin.natAdd 3 j) 1 else Pi.single (j.castAdd 3) 1 := by
  funext i
  obtain ⟨i,rfl⟩ := splitIndex.surjective i
  cases i with
  | inl i =>
    change matrixSix R (LagrangianAdmissibleCharts.swap R s)⁻¹ (splitIndex (Sum.inl i)) (splitIndex (Sum.inl j)) = _
    rw [matrixSix_apply_split,swap_inverse_matrix]
    fin_cases i <;> fin_cases j
    all_goals
      simp [Matrix.fromBlocks,keep,take,splitIndex,finSumFinEquiv,Pi.single_apply] <;>
        split_ifs <;> simp_all
  | inr i =>
    change matrixSix R (LagrangianAdmissibleCharts.swap R s)⁻¹ (splitIndex (Sum.inr i)) (splitIndex (Sum.inl j)) = _
    rw [matrixSix_apply_split,swap_inverse_matrix]
    fin_cases i <;> fin_cases j
    all_goals
      simp [Matrix.fromBlocks,keep,take,splitIndex,finSumFinEquiv,Pi.single_apply] <;>
        split_ifs <;> simp_all

theorem mapped_swap_inverse_column {S : Type u} [CommRing S] (ρ : R →+* S)
    (s : Choice) (j : Fin 3) :
    (matrixSix S (mapSymplectic R ρ (LagrangianAdmissibleCharts.swap R s)⁻¹)).col (j.castAdd 3) =
      if s j then -Pi.single (Fin.natAdd 3 j) 1 else Pi.single (j.castAdd 3) 1 := by
  rw [matrixSix_map]
  funext i
  have h := congrArg (fun v : Fin 6 → R => ρ (v i)) (swap_inverse_column R s j)
  by_cases hs : s j
  · simpa [hs,Pi.single_apply] using h
  · simpa [hs,Pi.single_apply] using h

theorem product_mapped_swap_inverse_column {S : Type u} [CommRing S] (ρ : R →+* S)
    (M : Matrix (Fin 3) (Fin 6) S) (s : Choice) (j : Fin 3) :
    (M * matrixSix S (mapSymplectic R ρ (LagrangianAdmissibleCharts.swap R s)⁻¹)).col (j.castAdd 3) =
      if s j then -M.col (Fin.natAdd 3 j) else M.col (j.castAdd 3) := by
  funext i
  change M.mulVec ((matrixSix S (mapSymplectic R ρ (LagrangianAdmissibleCharts.swap R s)⁻¹)).col (j.castAdd 3)) i = _
  rw [mapped_swap_inverse_column]
  by_cases hs : s j <;> simp [hs,Matrix.mulVec_neg]

abbrev PolynomialSix := MvPolynomial (Fin 6) R

def entryIndex (i j : Fin 3) : Fin 6 :=
  symmetricEntryEquivFinSix.{u} (ULift.up (symmetricIndex (i,j)))

def headVariable (i : Fin 3) : PolynomialSix R := MvPolynomial.X (entryIndex.{u} i 0)

def headIdeal : Ideal (PolynomialSix R) := Ideal.span (Set.range (headVariable R))

/-- These are the actual three surviving upper-triangular entries. -/
abbrev TailEntry := {p : ULift.{u} SymmetricEntry // p.down.val.1 ≠ 0}

theorem card_tailEntry : Fintype.card TailEntry.{u} = 3 := by decide

def tailEntryEquivFinThree : TailEntry.{u} ≃ Fin 3 where
  toFun p := if p.val.down.val.1 = 1 then
    (if p.val.down.val.2 = 1 then 0 else 1) else 2
  invFun i := ![⟨ULift.up ⟨(1,1),by decide⟩,by decide⟩,
    ⟨ULift.up ⟨(1,2),by decide⟩,by decide⟩,
    ⟨ULift.up ⟨(2,2),by decide⟩,by decide⟩] i
  left_inv p := by
    rcases p with ⟨⟨⟨⟨i,j⟩,hij⟩⟩,hi⟩
    change i ≤ j at hij
    change i ≠ 0 at hi
    fin_cases i <;> fin_cases j
    · exact (hi rfl).elim
    · exact (hi rfl).elim
    · exact (hi rfl).elim
    · exact ((by decide : ¬ ((1 : Fin 3) ≤ 0)) hij).elim
    · rfl
    · rfl
    · exact ((by decide : ¬ ((2 : Fin 3) ≤ 0)) hij).elim
    · exact ((by decide : ¬ ((2 : Fin 3) ≤ 1)) hij).elim
    · rfl
  right_inv i := by fin_cases i <;> rfl

def eraseHead : PolynomialSix R →ₐ[R] MvPolynomial TailEntry.{u} R :=
  MvPolynomial.aeval fun i =>
    let p := symmetricEntryEquivFinSix.{u}.symm i
    if h : p.down.val.1 = 0 then 0 else MvPolynomial.X ⟨p,h⟩

theorem eraseHead_headVariable (i : Fin 3) : eraseHead R (headVariable R i) = 0 := by
  simp only [headVariable,eraseHead,MvPolynomial.aeval_X,entryIndex,
    Equiv.symm_apply_apply]
  rw [symmetricIndex_swap i 0]
  simp [symmetricIndex]

theorem headIdeal_le_ker : headIdeal R ≤ RingHom.ker (eraseHead R).toRingHom := by
  apply Ideal.span_le.mpr
  rintro _ ⟨i,rfl⟩
  exact eraseHead_headVariable R i

def quotientToTail : PolynomialSix R ⧸ headIdeal R →ₐ[R] MvPolynomial TailEntry.{u} R :=
  Ideal.Quotient.liftₐ (headIdeal R) (eraseHead R) (fun _ h => headIdeal_le_ker R h)

def tailToQuotient : MvPolynomial TailEntry.{u} R →ₐ[R] PolynomialSix R ⧸ headIdeal R :=
  MvPolynomial.aeval fun p => Ideal.Quotient.mk (headIdeal R)
    (MvPolynomial.X (symmetricEntryEquivFinSix.{u} p.val))

@[simp] theorem quotientToTail_mk (p : PolynomialSix R) :
    quotientToTail R (Ideal.Quotient.mk (headIdeal R) p) = eraseHead R p := rfl

@[simp] theorem tailToQuotient_X (p : TailEntry.{u}) :
    tailToQuotient R (MvPolynomial.X p) = Ideal.Quotient.mk (headIdeal R)
      (MvPolynomial.X (symmetricEntryEquivFinSix.{u} p.val)) := MvPolynomial.aeval_X _ _

theorem quotientToTail_comp_tailToQuotient :
    (quotientToTail R).comp (tailToQuotient R) = AlgHom.id R (MvPolynomial TailEntry.{u} R) := by
  apply MvPolynomial.algHom_ext
  intro p
  simp [eraseHead,p.property]

theorem tailToQuotient_comp_quotientToTail :
    (tailToQuotient R).comp (quotientToTail R) = AlgHom.id R (PolynomialSix R ⧸ headIdeal R) := by
  apply Ideal.Quotient.algHom_ext
  apply MvPolynomial.algHom_ext
  intro i
  obtain ⟨p,rfl⟩ := symmetricEntryEquivFinSix.{u}.surjective i
  change tailToQuotient R (eraseHead R (MvPolynomial.X (symmetricEntryEquivFinSix.{u} p))) =
    Ideal.Quotient.mk (headIdeal R) (MvPolynomial.X (symmetricEntryEquivFinSix.{u} p))
  simp only [eraseHead,MvPolynomial.aeval_X,Equiv.symm_apply_apply]
  by_cases hp : p.down.val.1 = 0
  · rw [dite_eq_left hp,map_zero]
    symm
    apply Ideal.Quotient.eq_zero_iff_mem.mpr
    have he : p = ULift.up (symmetricIndex (p.down.val.2,0)) := by
      rw [symmetricIndex_swap _ 0]
      apply ULift.ext
      apply Subtype.ext
      simp only [symmetricIndex, dite_eq_left (show (0 : Fin 3) ≤ p.down.val.2 from Fin.zero_le _)]
      exact Prod.ext hp rfl
    rw [he]
    exact Ideal.subset_span ⟨p.down.val.2,rfl⟩
  · rw [dite_eq_right hp,tailToQuotient_X]

def quotientTailEquiv : (PolynomialSix R ⧸ headIdeal R) ≃ₐ[R] MvPolynomial TailEntry.{u} R :=
  AlgEquiv.ofAlgHom (quotientToTail R) (tailToQuotient R)
    (quotientToTail_comp_tailToQuotient R) (tailToQuotient_comp_quotientToTail R)

/-- The actual polynomial quotient by one symmetric row/column is an
actual three-variable polynomial algebra, with both maps constructed. -/
def quotientAffineThreeEquiv :
    (PolynomialSix R ⧸ headIdeal R) ≃ₐ[R] MvPolynomial (Fin 3) R :=
  (quotientTailEquiv R).trans (MvPolynomial.renameEquiv R tailEntryEquivFinThree.{u})

def eraseHeadThree : PolynomialSix R →ₐ[R] MvPolynomial (Fin 3) R :=
  (MvPolynomial.renameEquiv R tailEntryEquivFinThree.{u}).toAlgHom.comp (eraseHead R)

theorem quotientAffineThreeEquiv_mk (p : PolynomialSix R) :
    quotientAffineThreeEquiv R (Ideal.Quotient.mk (headIdeal R) p) = eraseHeadThree R p := rfl

theorem eraseHeadThree_headVariable (i : Fin 3) :
    eraseHeadThree R (headVariable R i) = 0 := by
  change MvPolynomial.rename tailEntryEquivFinThree.{u} (eraseHead R (headVariable R i)) = _
  rw [eraseHead_headVariable,map_zero]

/-- The three actual surviving variables are ordered A11,A12,A22. -/
theorem eraseHeadThree_tailVariable (i : Fin 3) :
    eraseHeadThree R (MvPolynomial.X (symmetricEntryEquivFinSix.{u}
      (tailEntryEquivFinThree.{u}.symm i).val)) = MvPolynomial.X i := by
  change MvPolynomial.rename tailEntryEquivFinThree.{u}
    (eraseHead R (MvPolynomial.X (symmetricEntryEquivFinSix.{u}
      (tailEntryEquivFinThree.{u}.symm i).val))) = _
  simp [eraseHead,(tailEntryEquivFinThree.{u}.symm i).property]

end M9Native.LagrangianCommonKernelChartAlgebra
