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
  all_goals
    simp only [M9.PrimitiveOpenOrbit.gaussEntries, Fin.addCases_left, Fin.addCases_right]
    fin_cases i <;> fin_cases j <;>
      simp [gauss, upper, lower, torus,
        Matrix.mul_apply, Fin.sum_univ_succ, Matrix.diagonal,
        Matrix.one_apply, Matrix.fromBlocks, mul_assoc, mul_left_comm, mul_comm] <;>
      ring_nf <;> simp only [Units.mul_inv, one_mul] <;> ring

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
