module

public import M9.RadicalMap

/-! # Nonzero cofactor charts cover the rank-eight locus -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace M9.RadicalMap

open Module Matrix
open scoped BigOperators

section Rank

variable {K : Type*} [Field K]

private theorem standardRankEight_adjugate {n : ℕ} (hn : n = 1) (z : Fin n) :
    (Matrix.fromBlocks (1 : Matrix (Fin 8) (Fin 8) K)
      (0 : Matrix (Fin 8) (Fin n) K) (0 : Matrix (Fin n) (Fin 8) K)
      (0 : Matrix (Fin n) (Fin n) K)).adjugate (Sum.inr z) (Sum.inr z) = 1 := by
  subst n
  classical
  have hd : Matrix.fromBlocks (1 : Matrix (Fin 8) (Fin 8) K)
      (0 : Matrix (Fin 8) (Fin 1) K) (0 : Matrix (Fin 1) (Fin 8) K)
      (0 : Matrix (Fin 1) (Fin 1) K) =
      Matrix.diagonal (Sum.elim (fun _ => (1 : K)) (fun _ => 0)) := by
    ext i j
    rcases i with i | i <;> rcases j with j | j <;>
      simp [Matrix.fromBlocks, Matrix.diagonal, Matrix.one_apply]
  rw [hd, Matrix.adjugate_diagonal, Matrix.diagonal_apply_eq]
  apply Finset.prod_eq_one
  intro i hi
  rcases i with i | i
  · rfl
  · have hi' : Sum.inr i ≠ (Sum.inr z : Fin 8 ⊕ Fin 1) :=
      (Finset.mem_erase.mp hi).1
    exact False.elim (hi' (by congr 1; exact Subsingleton.elim _ _))

/-- Rank eight forces an actual nonzero adjugate entry, with no choice of minor assumed. -/
theorem adjugate_ne_zero_of_rank_eight (M : Matrix (Fin 9) (Fin 9) K) (hr : M.rank = 8) :
    M.adjugate ≠ 0 := by
  classical
  have hn := Matrix.exists_rank_normal_form M
  rw [hr] at hn
  obtain ⟨L,U,e,_,_,hLU⟩ := hn
  have hcard : Fintype.card (Fin 9) - 8 = 1 := by rw [Fintype.card_fin]
  let z : Fin (Fintype.card (Fin 9) - 8) := ⟨0,by rw [hcard]; decide⟩
  intro hz
  have hzero : (L * M * U).adjugate = 0 := by
    simp only [Matrix.adjugate_mul_distrib,hz,Matrix.mul_zero,Matrix.zero_mul]
  rw [hLU,Matrix.adjugate_submatrix_equiv_self] at hzero
  have h := congrArg (fun A : Matrix (Fin 9) (Fin 9) K =>
      A (e.symm (Sum.inr z)) (e.symm (Sum.inr z))) hzero
  simp only [Matrix.submatrix_apply,e.apply_symm_apply,standardRankEight_adjugate hcard z,
    Matrix.zero_apply,one_ne_zero] at h

theorem exists_nonzero_cofactor_of_rank_eight (M : Matrix (Fin 9) (Fin 9) K)
    (hr : M.rank = 8) : ∃ i j, M.adjugate i j ≠ 0 := by
  by_contra! hz
  apply adjugate_ne_zero_of_rank_eight M hr
  ext i j
  exact hz i j

/-- A nonzero cofactor of an odd alternating matrix forces rank exactly eight. -/
theorem rank_eight_of_nonzero_cofactor [CharZero K] (M : Matrix (Fin 9) (Fin 9) K)
    (hM : M.transpose = -M) (i j : Fin 9) (hij : M.adjugate i j ≠ 0) : M.rank = 8 := by
  have hd : (M.submatrix j.succAbove i.succAbove).det ≠ 0 := by
    intro hz
    apply hij
    rw [Matrix.adjugate_fin_succ_eq_det_submatrix,hz,mul_zero]
  have hlo := Matrix.rank_submatrix_le M j.succAbove i.succAbove
  rw [Matrix.rank_of_det_ne_zero hd] at hlo
  simp only [Fintype.card_fin] at hlo
  have hpos : 0 < finrank K (LinearMap.ker M.mulVecLin) := by
    apply Module.finrank_pos_iff_exists_ne_zero.mpr
    refine ⟨⟨kernelVector M j,mulVec_kernelVector M hM j⟩,?_⟩
    intro hz
    exact kernelVector_ne_zero M i j hij (congrArg Subtype.val hz)
  have he := M.mulVecLin.finrank_range_add_finrank_ker
  change M.rank + finrank K (LinearMap.ker M.mulVecLin) = finrank K (Fin 9 → K) at he
  simp only [Module.finrank_pi,Fintype.card_fin] at he
  omega

/-- The principal nonzero-cofactor charts cover precisely the rank-eight locus. -/
theorem rank_eight_iff_nonzero_cofactor [CharZero K] (M : Matrix (Fin 9) (Fin 9) K)
    (hM : M.transpose = -M) : M.rank = 8 ↔ ∃ i j, M.adjugate i j ≠ 0 := by
  constructor
  · exact exists_nonzero_cofactor_of_rank_eight M
  · rintro ⟨i,j,hij⟩
    exact rank_eight_of_nonzero_cofactor M hM i j hij

end Rank

end M9.RadicalMap
