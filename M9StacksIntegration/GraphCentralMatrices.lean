module

public import M9StacksIntegration.ReducedGraphAction

/-! Literal diagonal matrices for the actual cubic center on the native
graph chart. The graph coordinate is scaled; its center action is retained. -/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000

open Matrix

namespace M9Native.GraphCentralMatrices

open M9.GraphBundleDescent GraphGrassmannianChart ReducedGraphAction

section Ring
variable {R : Type*} [CommRing R]

def rowWeights (s t : R) (i : Fin 8) : R :=
  Sum.elim (fun _ : Fin 2 => s) (fun _ : Fin 4 ⊕ Fin 2 => t) (rowEquiv.symm i)

def ambientWeights (s t : R) (j : Fin 12) : R :=
  Sum.elim (fun _ : Fin 4 => s) (rowWeights s t) (finSumFinEquiv.symm j)

omit [CommRing R] in
@[simp] theorem rowWeights_first (s t : R) (i : Fin 2) :
    rowWeights s t (rowEquiv (.inl i)) = s := by simp [rowWeights]

omit [CommRing R] in
@[simp] theorem rowWeights_second (s t : R) (i : Fin 4) :
    rowWeights s t (rowEquiv (.inr (.inl i))) = t := by simp [rowWeights]

omit [CommRing R] in
@[simp] theorem rowWeights_third (s t : R) (i : Fin 2) :
    rowWeights s t (rowEquiv (.inr (.inr i))) = t := by simp [rowWeights]

omit [CommRing R] in
@[simp] theorem ambientWeights_head (s t : R) (i : Fin 4) :
    ambientWeights s t (head i) = s := by
  change Sum.elim _ _ (finSumFinEquiv.symm (Fin.castAdd 8 i)) = _
  rw [finSumFinEquiv_symm_apply_castAdd]
  rfl

omit [CommRing R] in
@[simp] theorem ambientWeights_pivot (s t : R) (i : Fin 8) :
    ambientWeights s t (pivot i) = rowWeights s t i := by
  change Sum.elim _ _ (finSumFinEquiv.symm (Fin.natAdd 4 i)) = _
  rw [finSumFinEquiv_symm_apply_natAdd]
  rfl

theorem rowWeights_map {S : Type*} [CommRing S] (φ : R →+* S) (s t : R) (i : Fin 8) :
    φ (rowWeights s t i) = rowWeights (φ s) (φ t) i := by
  obtain ⟨r, rfl⟩ := rowEquiv.surjective i
  rcases r with i | i <;> simp [rowWeights]

theorem ambientWeights_map {S : Type*} [CommRing S] (φ : R →+* S) (s t : R) (j : Fin 12) :
    φ (ambientWeights s t j) = ambientWeights (φ s) (φ t) j := by
  obtain ⟨j, rfl⟩ := (finSumFinEquiv : Fin 4 ⊕ Fin 8 ≃ Fin 12).surjective j
  rcases j with j | j <;> simp [ambientWeights, rowWeights_map]

theorem diagonal_rowWeights_map {S : Type*} [CommRing S] (φ : R →+* S) (s t : R) :
    (Matrix.diagonal (rowWeights s t)).map φ = Matrix.diagonal (rowWeights (φ s) (φ t)) := by
  rw [Matrix.diagonal_map (map_zero φ)]
  congr 1
  funext i
  exact rowWeights_map φ s t i

theorem diagonal_ambientWeights_map {S : Type*} [CommRing S] (φ : R →+* S) (s t : R) :
    (Matrix.diagonal (ambientWeights s t)).map φ = Matrix.diagonal (ambientWeights (φ s) (φ t)) := by
  rw [Matrix.diagonal_map (map_zero φ)]
  congr 1
  funext i
  exact ambientWeights_map φ s t i

/-- Diagonal multiplication has the literal two-block ambient meaning. -/
theorem diagonal_mulVec_ambient (s t : R) (z : Ambient R × Ambient R) :
    (Matrix.diagonal (ambientWeights s t)).mulVec (ambientCoordinates z) =
      ambientCoordinates (s • z.1,t • z.2) := by
  ext j
  rw [Matrix.mulVec_diagonal]
  obtain ⟨j, rfl⟩ := (finSumFinEquiv : Fin 4 ⊕ Fin 8 ≃ Fin 12).surjective j
  rcases j with j | j
  · simp [ambientWeights, ambientCoordinates_apply, smul_eq_mul]
  · obtain ⟨r, rfl⟩ := rowEquiv.surjective j
    rcases r with i | (i | i)
    all_goals simp [ambientWeights, rowWeights, ambientCoordinates_apply, smul_eq_mul]

theorem kernelMatrix_scaled (A B : BaseMatrix R) (X : FiberMatrix R)
    (s t c : R) (hst : s = t * c) :
    kernelMatrix (blockRows A X (B * X)) * Matrix.diagonal (ambientWeights s t) =
      Matrix.diagonal (rowWeights s t) * kernelMatrix (blockRows A (c • X) (B * (c • X))) := by
  classical
  ext i j
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
  obtain ⟨r, rfl⟩ := rowEquiv.surjective i
  obtain ⟨j, rfl⟩ := (finSumFinEquiv : Fin 4 ⊕ Fin 8 ≃ Fin 12).surjective j
  rcases j with j | j
  · rcases r with i | (i | i)
    all_goals
      simp only [kernelMatrix, Equiv.symm_apply_apply, Sum.elim_inl, ambientWeights,
        rowWeights_first, rowWeights_second, rowWeights_third,
        blockRows_A, blockRows_X, blockRows_C, Matrix.mul_smul, Matrix.smul_apply, smul_eq_mul]
      rw [hst]
      ring
  · simp only [kernelMatrix, Equiv.symm_apply_apply, Sum.elim_inr, ambientWeights]
    split_ifs with h
    · rw [← h]
      ring
    · simp

/-- The target quotient diagonal is a genuine unit matrix whenever the two
ambient weights are units. -/
def rowWeightUnit (s t : Rˣ) : (Fin 8 → R)ˣ where
  val := rowWeights (s : R) (t : R)
  inv := rowWeights (↑s⁻¹ : R) (↑t⁻¹ : R)
  val_inv := by
    funext i
    obtain ⟨r, rfl⟩ := rowEquiv.surjective i
    rcases r with i | (i | i) <;> simp [Pi.mul_apply, rowWeights]
  inv_val := by
    funext i
    obtain ⟨r, rfl⟩ := rowEquiv.surjective i
    rcases r with i | (i | i) <;> simp [Pi.mul_apply, rowWeights]

def rowDiagonalUnit (s t : Rˣ) : Matrix.GeneralLinearGroup (Fin 8) R :=
  Units.map (Matrix.diagonalRingHom (Fin 8) R).toMonoidHom (rowWeightUnit s t)

@[simp] theorem rowDiagonalUnit_val (s t : Rˣ) :
    (rowDiagonalUnit s t).val = Matrix.diagonal (rowWeights (s : R) (t : R)) := rfl

end Ring

variable (K : Type*) [Field K] [CharZero K]

omit [CharZero K] in
/-- The displayed graph coordinates come from the actual symmetric space
and its dual, so the two scalar characters act on their literal blocks. -/
theorem actualCoordinates_scale (s t : K) (z : M9.PrimitiveTwistedReduced.DualMixed K) :
    actualCoordinates K (s • z.1,t • z.2) =
      (Matrix.diagonal (ambientWeights s t)).mulVec (actualCoordinates K z) := by
  change ambientCoordinates ((symmetricSplit K) (s • z.1),(dualSymmetricSplit K) (t • z.2)) =
    (Matrix.diagonal (ambientWeights s t)).mulVec
      (ambientCoordinates ((symmetricSplit K) z.1,(dualSymmetricSplit K) z.2))
  rw [diagonal_mulVec_ambient, map_smul, map_smul]

/-- Literal native ambient matrix of an actual central SL3 element. -/
theorem matrixRepresentation_center_diagonal (a : K) (ha : a ^ 3 = 1) :
    (matrixRepresentation K (SemidirectProduct.inl
      (M9.PrimitiveRepresentation.centralElement K a ha))).val =
      Matrix.diagonal (ambientWeights (a^2) ((a⁻¹)^2)) := by
  apply Matrix.ext_of_mulVec_single
  intro j
  let z := (actualCoordinates K).symm (Pi.single j 1)
  have h := matrixRepresentation_center K a ha z
  rw [actualCoordinates_scale] at h
  simpa only [z, LinearEquiv.apply_symm_apply] using h

end M9Native.GraphCentralMatrices
