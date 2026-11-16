module

public import M9StacksIntegration.MatrixChartFieldRecovery
public import M9StacksIntegration.PrimitiveRhoFiberChart

/-! Explicit inverse formulas for the actual rho-plus-graph quotient.
These recover the original A, X and B coefficients from its literal quotient matrix. -/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 2000000

open Matrix

namespace M9Native.PrimitiveRhoGraphRecovery

open PrimitiveRhoFiberChart MatrixChartFieldRecovery M9.GraphBundleDescent

variable (K : Type) [Field K] [Algebra ℂ K]

theorem recover_frame (P : Matrix (Fin 12) (Fin 4) K) :
    (quotientMatrix K P * (pairingIsomorphism⁻¹).val.map (algebraMap ℂ K)).transpose = frame K P := by
  have hJ : pairingMatrix.map (algebraMap ℂ K) *
      (pairingIsomorphism⁻¹).val.map (algebraMap ℂ K) = 1 := by
    rw [← Matrix.map_mul]
    change ((pairingIsomorphism * pairingIsomorphism⁻¹).val.map (algebraMap ℂ K)) = 1
    rw [mul_inv_cancel, Units.val_one, Matrix.map_one] <;> simp
  rw [quotientMatrix, Matrix.mul_assoc, hJ, Matrix.mul_one, Matrix.transpose_transpose]

theorem frame_tail (P : Matrix (Fin 12) (Fin 4) K) :
    (frame K P).submatrix id (Fin.natAdd 1) = liftMatrix.map (algebraMap ℂ K) * P := by
  ext i j
  change sumFrame K P i ((finSumFinEquiv : Fin 1 ⊕ Fin 4 ≃ Fin 5).symm (Fin.natAdd 1 j)) = _
  rw [finSumFinEquiv_symm_apply_natAdd]
  rfl

theorem recover_mixed_frame (P : Matrix (Fin 12) (Fin 4) K) :
    (retractionMatrix.map (algebraMap ℂ K) * frame K P).submatrix id (Fin.natAdd 1) = P := by
  calc
    _ = retractionMatrix.map (algebraMap ℂ K) * (frame K P).submatrix id (Fin.natAdd 1) := by
      ext i j
      rfl
    _ = P := by
      rw [frame_tail, ← Matrix.mul_assoc, ← Matrix.map_mul,
        retractionMatrix_liftMatrix, Matrix.map_one, Matrix.one_mul] <;> simp

/-- The actual twelve-by-four graph is recovered by fixed linear operations on Qrho. -/
theorem recover_graph (P : Matrix (Fin 12) (Fin 4) K) :
    (retractionMatrix.map (algebraMap ℂ K) *
      (quotientMatrix K P * (pairingIsomorphism⁻¹).val.map (algebraMap ℂ K)).transpose).submatrix
        id (Fin.natAdd 1) = P := by
  rw [recover_frame, recover_mixed_frame]

theorem entriesIn_graph (E : Subfield K) (hC : ∀ c : ℂ, algebraMap ℂ K c ∈ E)
    (P : Matrix (Fin 12) (Fin 4) K) (hQ : EntriesIn E (quotientMatrix K P)) : EntriesIn E P := by
  have hFull : EntriesIn E
      ((retractionMatrix.map (algebraMap ℂ K) *
        (quotientMatrix K P * (pairingIsomorphism⁻¹).val.map (algebraMap ℂ K)).transpose).submatrix
          id (Fin.natAdd 1 : Fin 4 → Fin 5)) := by
    intro i j
    change (∑ k : Fin 14, algebraMap ℂ K (retractionMatrix i k) *
      (∑ l : Fin 14, quotientMatrix K P (Fin.natAdd 1 j) l *
        algebraMap ℂ K ((pairingIsomorphism⁻¹).val l k))) ∈ E
    apply E.sum_mem
    intro k _
    apply E.mul_mem (hC _)
    apply E.sum_mem
    intro l _
    exact E.mul_mem (hQ _ _) (hC _)
  exact Eq.mp (congrArg (EntriesIn E) (recover_graph K P)) hFull

theorem graph_A_entry (A B : BaseMatrix K) (X : Matrix.GeneralLinearGroup (Fin 4) K)
    (i : Fin 2) (j : Fin 4) :
    graphMatrix K A B X (GraphGrassmannianChart.pivot (GraphGrassmannianChart.rowEquiv (.inl i))) j =
      A i j := by
  have h := congrFun (graphMatrix_mulVec K A B X (Pi.single j 1))
    (GraphGrassmannianChart.pivot (GraphGrassmannianChart.rowEquiv (.inl i)))
  rw [Matrix.mulVec_single_one, graphFamilyEmbedding_apply,
    GraphGrassmannianChart.ambientCoordinates_pivot] at h
  simpa only [Sum.elim_inl, Matrix.mulVec_single_one, Matrix.col_apply] using h

theorem graph_X_entry (A B : BaseMatrix K) (X : Matrix.GeneralLinearGroup (Fin 4) K)
    (i j : Fin 4) :
    graphMatrix K A B X
      (GraphGrassmannianChart.pivot (GraphGrassmannianChart.rowEquiv (.inr (.inl i)))) j = X.val i j := by
  have h := congrFun (graphMatrix_mulVec K A B X (Pi.single j 1))
    (GraphGrassmannianChart.pivot (GraphGrassmannianChart.rowEquiv (.inr (.inl i))))
  rw [Matrix.mulVec_single_one, graphFamilyEmbedding_apply,
    GraphGrassmannianChart.ambientCoordinates_pivot] at h
  simpa only [Sum.elim_inr, Sum.elim_inl, Matrix.mulVec_single_one, Matrix.col_apply] using h

theorem graph_BX_entry (A B : BaseMatrix K) (X : Matrix.GeneralLinearGroup (Fin 4) K)
    (i : Fin 2) (j : Fin 4) :
    graphMatrix K A B X
      (GraphGrassmannianChart.pivot (GraphGrassmannianChart.rowEquiv (.inr (.inr i)))) j =
        (B*X.val) i j := by
  have h := congrFun (graphMatrix_mulVec K A B X (Pi.single j 1))
    (GraphGrassmannianChart.pivot (GraphGrassmannianChart.rowEquiv (.inr (.inr i))))
  rw [Matrix.mulVec_single_one, graphFamilyEmbedding_apply,
    GraphGrassmannianChart.ambientCoordinates_pivot] at h
  simpa only [Sum.elim_inr, Matrix.mulVec_single_one, Matrix.col_apply] using h

theorem entriesIn_base_left (E : Subfield K) (A B : BaseMatrix K)
    (X : Matrix.GeneralLinearGroup (Fin 4) K) (hP : EntriesIn E (graphMatrix K A B X)) :
    EntriesIn E A := by
  intro i j
  rw [← graph_A_entry K A B X i j]
  exact hP _ _

theorem entriesIn_fiber (E : Subfield K) (A B : BaseMatrix K)
    (X : Matrix.GeneralLinearGroup (Fin 4) K) (hP : EntriesIn E (graphMatrix K A B X)) :
    EntriesIn E X.val := by
  intro i j
  rw [← graph_X_entry K A B X i j]
  exact hP _ _

theorem entriesIn_base_right (E : Subfield K) (A B : BaseMatrix K)
    (X : Matrix.GeneralLinearGroup (Fin 4) K) (hP : EntriesIn E (graphMatrix K A B X)) :
    EntriesIn E B := by
  have hBX : EntriesIn E (B*X.val) := by
    intro i j
    rw [← graph_BX_entry K A B X i j]
    exact hP _ _
  have hInv := (entriesIn_fiber K E A B X hP).inv E
  have hX : X.val⁻¹ = (X⁻¹).val := Matrix.inv_eq_left_inv (Units.inv_mul X)
  have hB : B*X.val*X.val⁻¹ = B := by
    rw [hX, Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one]
  simpa only [hB] using hBX.mul E hInv

/-- All thirty-two original parameters are recovered from the actual quotient matrix. -/
theorem entriesIn_parameters (E : Subfield K) (hC : ∀ c : ℂ, algebraMap ℂ K c ∈ E)
    (A B : BaseMatrix K) (X : Matrix.GeneralLinearGroup (Fin 4) K)
    (hQ : EntriesIn E (quotientMatrix K (graphMatrix K A B X))) :
    EntriesIn E A ∧ EntriesIn E X.val ∧ EntriesIn E B := by
  have hP := entriesIn_graph K E hC _ hQ
  exact ⟨entriesIn_base_left K E A B X hP, entriesIn_fiber K E A B X hP,
    entriesIn_base_right K E A B X hP⟩

end M9Native.PrimitiveRhoGraphRecovery
