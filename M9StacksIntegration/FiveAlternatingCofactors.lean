module

public import M9.RadicalMapRank
public import M9StacksIntegration.MatrixChartFieldRecovery

/-! Actual polynomial kernel vectors for the five-dimensional annihilator Gram matrix.
The nonzero cofactor is derived from rank four; no chosen cofactor is a premise. -/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false

open Matrix
open scoped BigOperators

namespace M9Native.FiveAlternatingCofactors

variable {K : Type*} [Field K]

private theorem standardRankFour_adjugate {n : ℕ} (hn : n = 1) (z : Fin n) :
    (Matrix.fromBlocks (1 : Matrix (Fin 4) (Fin 4) K)
      (0 : Matrix (Fin 4) (Fin n) K) (0 : Matrix (Fin n) (Fin 4) K)
      (0 : Matrix (Fin n) (Fin n) K)).adjugate (Sum.inr z) (Sum.inr z) = 1 := by
  subst n
  classical
  have hd : Matrix.fromBlocks (1 : Matrix (Fin 4) (Fin 4) K)
      (0 : Matrix (Fin 4) (Fin 1) K) (0 : Matrix (Fin 1) (Fin 4) K)
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
  · have hi' : Sum.inr i ≠ (Sum.inr z : Fin 4 ⊕ Fin 1) := (Finset.mem_erase.mp hi).1
    exact False.elim (hi' (by congr 1; exact Subsingleton.elim _ _))

theorem adjugate_ne_zero_of_rank_four (M : Matrix (Fin 5) (Fin 5) K) (hr : M.rank = 4) :
    M.adjugate ≠ 0 := by
  classical
  have hn := Matrix.exists_rank_normal_form M
  rw [hr] at hn
  obtain ⟨L, U, e, _, _, hLU⟩ := hn
  have hcard : Fintype.card (Fin 5) - 4 = 1 := by rw [Fintype.card_fin]
  let z : Fin (Fintype.card (Fin 5) - 4) := ⟨0, by rw [hcard]; decide⟩
  intro hz
  have hzero : (L*M*U).adjugate = 0 := by
    simp only [Matrix.adjugate_mul_distrib, hz, Matrix.mul_zero, Matrix.zero_mul]
  rw [hLU, Matrix.adjugate_submatrix_equiv_self] at hzero
  have h := congrArg (fun A : Matrix (Fin 5) (Fin 5) K =>
    A (e.symm (Sum.inr z)) (e.symm (Sum.inr z))) hzero
  simp only [Matrix.submatrix_apply, e.apply_symm_apply, standardRankFour_adjugate hcard z,
    Matrix.zero_apply, one_ne_zero] at h

theorem exists_nonzero_cofactor_of_rank_four (M : Matrix (Fin 5) (Fin 5) K) (hr : M.rank = 4) :
    ∃ i j, M.adjugate i j ≠ 0 := by
  by_contra! hz
  apply adjugate_ne_zero_of_rank_four M hr
  ext i j
  exact hz i j

def kernelVector (M : Matrix (Fin 5) (Fin 5) K) (j : Fin 5) : Fin 5 → K :=
  fun i => M.adjugate i j

theorem kernelVector_ne_zero (M : Matrix (Fin 5) (Fin 5) K) (i j : Fin 5)
    (hij : M.adjugate i j ≠ 0) : kernelVector M j ≠ 0 := by
  intro h
  exact hij (congrFun h i)

theorem mulVec_kernelVector (M : Matrix (Fin 5) (Fin 5) K) (hd : M.det = 0) (j : Fin 5) :
    M *ᵥ kernelVector M j = 0 := by
  have hm : M*M.adjugate = 0 := by rw [Matrix.mul_adjugate, hd, zero_smul]
  funext i
  have h := congrArg (fun A : Matrix (Fin 5) (Fin 5) K => A i j) hm
  simpa only [Matrix.mul_apply, Matrix.zero_apply, Matrix.mulVec, dotProduct, kernelVector,
    Pi.zero_apply] using h

theorem kernelVector_mem (E : Subfield K) (M : Matrix (Fin 5) (Fin 5) K)
    (hM : MatrixChartFieldRecovery.EntriesIn E M) (j i : Fin 5) : kernelVector M j i ∈ E := by
  have h := E.subtype.map_adjugate (MatrixChartFieldRecovery.restrictMatrix E M hM)
  change ((MatrixChartFieldRecovery.restrictMatrix E M hM).adjugate.map E.subtype) =
    ((MatrixChartFieldRecovery.restrictMatrix E M hM).map E.subtype).adjugate at h
  rw [MatrixChartFieldRecovery.map_restrictMatrix] at h
  have hm : E.subtype ((MatrixChartFieldRecovery.restrictMatrix E M hM).adjugate i j) ∈ E :=
    ((MatrixChartFieldRecovery.restrictMatrix E M hM).adjugate i j).property
  change ((MatrixChartFieldRecovery.restrictMatrix E M hM).adjugate.map E.subtype) i j ∈ E at hm
  rw [h] at hm
  exact hm

end M9Native.FiveAlternatingCofactors
