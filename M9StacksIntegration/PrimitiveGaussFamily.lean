module

public import M9StacksIntegration.PrimitiveGaussCoordinates
public import M9StacksIntegration.Sp6GroupScheme
public import M9StacksIntegration.PrimitiveRingRepresentation

/-! The thirteen-parameter Gauss family consists of actual symplectic matrices over
its localized coefficient ring. No field-point symplecticity hypothesis is used. -/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

open Matrix
open scoped BigOperators

namespace M9Native.PrimitiveGaussFamily

variable {R : Type*} [CommRing R]

def upper (B : Matrix (Fin 3) (Fin 3) R) (hB : Bᵀ = B) :
    Matrix.symplecticGroup (Fin 3) R :=
  ⟨Matrix.fromBlocks 1 B 0 1, by
    apply SymplecticGroup.fromBlocks_mem_iff.mpr
    simp [hB]⟩

def lower (C : Matrix (Fin 3) (Fin 3) R) (hC : Cᵀ = C) :
    Matrix.symplecticGroup (Fin 3) R :=
  ⟨Matrix.fromBlocks 1 0 C 1, by
    apply SymplecticGroup.fromBlocks_mem_iff.mpr
    simp [hC]⟩

def torus (u : Rˣ) : Matrix.symplecticGroup (Fin 3) R :=
  ⟨Matrix.fromBlocks (Matrix.diagonal ![(u : R), 1, 1]) 0 0
      (Matrix.diagonal ![((u⁻¹ : Rˣ) : R), 1, 1]), by
    apply SymplecticGroup.fromBlocks_mem_iff.mpr
    simp only [Matrix.diagonal_transpose, Matrix.mul_zero, Matrix.zero_mul,
      Matrix.transpose_zero, sub_zero, Matrix.diagonal_mul_diagonal, and_self,
      true_and]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.diagonal]⟩

def gauss (u : Rˣ) (B C : Matrix (Fin 3) (Fin 3) R) (hB : Bᵀ = B) (hC : Cᵀ = C) :
    Matrix.symplecticGroup (Fin 3) R := upper B hB * torus u * lower C hC

private lemma gauss_val_blocks (u : Rˣ) (B C : Matrix (Fin 3) (Fin 3) R)
    (hB : Bᵀ = B) (hC : Cᵀ = C) :
    (gauss u B C hB hC).val =
      Matrix.fromBlocks
        (Matrix.diagonal ![(u : R), 1, 1] + B * Matrix.diagonal ![(↑u⁻¹ : R), 1, 1] * C)
        (B * Matrix.diagonal ![(↑u⁻¹ : R), 1, 1])
        (Matrix.diagonal ![(↑u⁻¹ : R), 1, 1] * C)
        (Matrix.diagonal ![(↑u⁻¹ : R), 1, 1]) := by
  simp only [gauss, upper, torus, lower, Submonoid.coe_mul]
  change Matrix.fromBlocks 1 B 0 1 *
    Matrix.fromBlocks (Matrix.diagonal ![(u : R), 1, 1]) 0 0
      (Matrix.diagonal ![(↑u⁻¹ : R), 1, 1]) * Matrix.fromBlocks 1 0 C 1 = _
  rw [Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply]
  simp only [Matrix.one_mul, Matrix.mul_one, Matrix.zero_mul, Matrix.mul_zero, zero_add, add_zero]

private lemma scale_gauss_upper (u : Rˣ) (i : Fin 3) :
    (u : R) * (![(u : R), 1, 1] : Fin 3 → R) i = ![(u : R)^2, (u : R), (u : R)] i := by
  fin_cases i <;> simp [pow_two]

private lemma scale_gauss_lower (u : Rˣ) (i : Fin 3) :
    (u : R) * (![(↑u⁻¹ : R), 1, 1] : Fin 3 → R) i = ![1, (u : R), (u : R)] i := by
  fin_cases i <;> simp

/-- The original polynomial matrix is the unit-scaled genuine symplectic matrix. -/
theorem gauss_scaled (u : Rˣ) (B C : Matrix (Fin 3) (Fin 3) R)
    (hB : Bᵀ = B) (hC : Cᵀ = C) :
    (u : R) • LagrangianTransitivity.matrixSix R (gauss u B C hB hC) =
      M9.PrimitiveOpenOrbit.gaussEntries (u : R) B C := by
  apply (Matrix.submatrix_injective LagrangianTransitivity.splitIndex.surjective
    LagrangianTransitivity.splitIndex.surjective)
  ext (i | i) (j | j)
  all_goals
    simp only [Matrix.submatrix_apply, Matrix.smul_apply, smul_eq_mul,
      LagrangianTransitivity.matrixSix, Equiv.symm_apply_apply]
  all_goals first
  |
    change (u : R) * (gauss u B C hB hC).val (Sum.inl i) (Sum.inl j) =
      M9.PrimitiveOpenOrbit.gaussEntries (u : R) B C (i.castAdd 3) (j.castAdd 3)
  |
    change (u : R) * (gauss u B C hB hC).val (Sum.inl i) (Sum.inr j) =
      M9.PrimitiveOpenOrbit.gaussEntries (u : R) B C (i.castAdd 3) (Fin.natAdd 3 j)
  |
    change (u : R) * (gauss u B C hB hC).val (Sum.inr i) (Sum.inl j) =
      M9.PrimitiveOpenOrbit.gaussEntries (u : R) B C (Fin.natAdd 3 i) (j.castAdd 3)
  |
    change (u : R) * (gauss u B C hB hC).val (Sum.inr i) (Sum.inr j) =
      M9.PrimitiveOpenOrbit.gaussEntries (u : R) B C (Fin.natAdd 3 i) (Fin.natAdd 3 j)
  all_goals rw [gauss_val_blocks]
  all_goals simp only [M9.PrimitiveOpenOrbit.gaussEntries, Fin.addCases_left, Fin.addCases_right]
  · simp only [Matrix.fromBlocks_apply₁₁, Matrix.add_apply, Matrix.diagonal_apply, mul_add]
    congr 1
    · split_ifs <;> simp [scale_gauss_upper]
    · rw [Matrix.mul_apply, Finset.mul_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [Matrix.mul_diagonal, ← scale_gauss_lower u k]
      ac_rfl
  · rw [Matrix.fromBlocks_apply₁₂, Matrix.mul_diagonal, ← scale_gauss_lower u j]
    ac_rfl
  · rw [Matrix.fromBlocks_apply₂₁, Matrix.diagonal_mul, ← scale_gauss_lower u i]
    ac_rfl
  · rw [Matrix.fromBlocks_apply₂₂, Matrix.diagonal_apply]
    split_ifs <;> simp [scale_gauss_lower]

variable (K : Type*) [Field K]

open PrimitiveGaussCoordinates M9.PrimitiveOpenOrbit

def parameter : (sourceRing K)ˣ := (parameter_unit K).unit

@[simp] theorem parameter_val : (parameter K : sourceRing K) =
    algebraMap (polynomial K) (sourceRing K) (MvPolynomial.X 0) :=
  (parameter_unit K).unit_spec

def family : Matrix.symplecticGroup (Fin 3) (sourceRing K) :=
  gauss (parameter K)
    (upperParameters (fun i => algebraMap (polynomial K) (sourceRing K) (MvPolynomial.X i)))
    (lowerParameters (fun i => algebraMap (polynomial K) (sourceRing K) (MvPolynomial.X i)))
    (upperParameters_symmetric _) (lowerParameters_symmetric _)

theorem family_scaled :
    algebraMap (polynomial K) (sourceRing K) (MvPolynomial.X 0) •
      LagrangianTransitivity.matrixSix (sourceRing K) (family K) =
        (formalMatrix K).map (algebraMap (polynomial K) (sourceRing K)) := by
  rw [← parameter_val, family, gauss_scaled]
  have hB : (upperParameters (MvPolynomial.X : Fin 13 → polynomial K)).map
      (algebraMap (polynomial K) (sourceRing K)) =
      upperParameters (fun i => algebraMap (polynomial K) (sourceRing K) (MvPolynomial.X i)) := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  have hC : (lowerParameters (MvPolynomial.X : Fin 13 → polynomial K)).map
      (algebraMap (polynomial K) (sourceRing K)) =
      lowerParameters (fun i => algebraMap (polynomial K) (sourceRing K) (MvPolynomial.X i)) := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  ext i j
  simp only [formalMatrix, Matrix.map_apply,
    map_gaussEntries (algebraMap (polynomial K) (sourceRing K)), parameter_val, hB, hC]

end M9Native.PrimitiveGaussFamily
