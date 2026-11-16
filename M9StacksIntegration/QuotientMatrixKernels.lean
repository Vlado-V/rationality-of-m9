module

public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.LinearAlgebra.Matrix.ToLin

/-! Surjective matrix quotients with the same actual kernel differ by an
invertible target matrix. This also controls the selected quotient minors. -/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace M9Native.QuotientMatrixKernels

variable {K : Type*} [Field K]

abbrev QMat (K : Type*) := Matrix (Fin 2) (Fin 6) K

theorem factor_of_kernel_le (Q Q' : QMat K) (S : Matrix (Fin 6) (Fin 2) K)
    (hS : Q * S = 1) (hker : LinearMap.ker Q.mulVecLin ≤ LinearMap.ker Q'.mulVecLin) :
    Q' = (Q' * S) * Q := by
  have hval (x : Fin 6 → K) : Q'.mulVec x = ((Q' * S) * Q).mulVec x := by
    let v := x - S.mulVec (Q.mulVec x)
    have hv : Q.mulVec v = 0 := by
      rw [Matrix.mulVec_sub,Matrix.mulVec_mulVec,hS,Matrix.one_mulVec,sub_self]
    have hv' : Q'.mulVec v = 0 := hker hv
    simpa only [v,Matrix.mulVec_sub,Matrix.mulVec_mulVec,sub_eq_zero,Matrix.mul_assoc] using hv'
  apply Matrix.ext_of_mulVec_single
  exact fun i => hval (Pi.single i 1)

theorem exists_unit_factor_of_kernel_eq (Q Q' : QMat K)
    (hQ : Function.Surjective Q.mulVec) (hQ' : Function.Surjective Q'.mulVec)
    (hker : LinearMap.ker Q.mulVecLin = LinearMap.ker Q'.mulVecLin) :
    ∃ A : Matrix (Fin 2) (Fin 2) K, IsUnit A.det ∧ Q' = A * Q := by
  obtain ⟨S,hS⟩ := Matrix.mulVec_surjective_iff_exists_right_inverse.mp hQ
  let A := Q' * S
  have heq : Q' = A * Q := factor_of_kernel_le Q Q' S hS hker.le
  have hA : Function.Surjective A.mulVec := by
    intro y
    obtain ⟨x,hx⟩ := hQ' y
    refine ⟨Q.mulVec x,?_⟩
    rw [Matrix.mulVec_mulVec,← heq,hx]
  exact ⟨A,(Matrix.isUnit_iff_isUnit_det _).mp
    (Matrix.mulVec_surjective_iff_isUnit.mp hA),heq⟩

theorem unit_minor_of_kernel_eq (Q Q' : QMat K) (ι : Fin 2 ↪ Fin 6)
    (hQ : Function.Surjective Q.mulVec) (hQ' : Function.Surjective Q'.mulVec)
    (hker : LinearMap.ker Q.mulVecLin = LinearMap.ker Q'.mulVecLin)
    (hp : IsUnit (Q.submatrix id ι).det) : IsUnit (Q'.submatrix id ι).det := by
  obtain ⟨A,hA,rfl⟩ := exists_unit_factor_of_kernel_eq Q Q' hQ hQ' hker
  rw [Matrix.submatrix_mul _ _ id id ι Function.bijective_id,Matrix.submatrix_id_id,Matrix.det_mul]
  exact hA.mul hp

def normalize (Q : QMat K) (ι : Fin 2 ↪ Fin 6) : QMat K := (Q.submatrix id ι)⁻¹ * Q

theorem normalize_eq_of_kernel_eq (Q Q' : QMat K) (ι : Fin 2 ↪ Fin 6)
    (hQ : Function.Surjective Q.mulVec) (hQ' : Function.Surjective Q'.mulVec)
    (hker : LinearMap.ker Q.mulVecLin = LinearMap.ker Q'.mulVecLin)
    (hp : IsUnit (Q.submatrix id ι).det) : normalize Q ι = normalize Q' ι := by
  obtain ⟨A,hA,heq⟩ := exists_unit_factor_of_kernel_eq Q Q' hQ hQ' hker
  have hp' := unit_minor_of_kernel_eq Q Q' ι hQ hQ' hker hp
  have hminor : Q'.submatrix id ι = A * Q.submatrix id ι := by
    rw [heq,Matrix.submatrix_mul _ _ id id ι Function.bijective_id,Matrix.submatrix_id_id]
  have hleft : (Q'.submatrix id ι)⁻¹ * A = (Q.submatrix id ι)⁻¹ := by
    calc
      _ = ((Q'.submatrix id ι)⁻¹ * A) *
          ((Q.submatrix id ι) * (Q.submatrix id ι)⁻¹) := by rw [Matrix.mul_nonsing_inv _ hp,Matrix.mul_one]
      _ = ((Q'.submatrix id ι)⁻¹ * (A * Q.submatrix id ι)) * (Q.submatrix id ι)⁻¹ := by
        simp only [Matrix.mul_assoc]
      _ = (Q.submatrix id ι)⁻¹ := by
        rw [← hminor,Matrix.nonsing_inv_mul _ hp',Matrix.one_mul]
  change (Q.submatrix id ι)⁻¹ * Q = (Q'.submatrix id ι)⁻¹ * Q'
  calc
    _ = ((Q'.submatrix id ι)⁻¹ * A) * Q := by rw [hleft]
    _ = (Q'.submatrix id ι)⁻¹ * (A * Q) := Matrix.mul_assoc _ _ _
    _ = (Q'.submatrix id ι)⁻¹ * Q' := by rw [← heq]

end M9Native.QuotientMatrixKernels
