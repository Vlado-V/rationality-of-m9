module

public import M9StacksIntegration.ConicFrameClosedFiber
public import M9StacksIntegration.ConicFrameBaseChange
public import M9StacksIntegration.QuotientMatrixKernels

/-! The actual right tetrahedral matrices preserve the polynomial quotient
up to an invertible two-by-two target change, over every complex algebra. -/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace M9Native.ConicFrameGammaCongruence

open ConicFrame ConicFrameClosedFiber QuotientMatrixKernels

abbrev Gamma := M9.TetrahedralGroup.Gamma

@[simp] theorem quotientMatrix_one : quotientMatrix (1 : Mat3 ℂ) = standardQuotient (R := ℂ) := by
  simp [quotientMatrix,congruence_one]

theorem gamma_quotient_factor (g : Gamma) :
    ∃ A : Matrix (Fin 2) (Fin 2) ℂ,
      IsUnit A.det ∧ quotientMatrix (M9.TetrahedralGroup.matrix g) = A * standardQuotient (R := ℂ) := by
  have hg : IsUnit (M9.TetrahedralGroup.matrix g).det := by
    rw [M9.TetrahedralGroup.matrix_det]
    exact isUnit_one
  have hk : LinearMap.ker (quotientMatrix (1 : Mat3 ℂ)).mulVecLin =
      LinearMap.ker (quotientMatrix (M9.TetrahedralGroup.matrix g)).mulVecLin :=
    (matrixKernel_fiber_iff 1 (M9.TetrahedralGroup.matrix g) (by simp) hg.ne_zero).mpr
      ⟨g,1,one_ne_zero,by simp⟩
  obtain ⟨A,hA,heq⟩ := exists_unit_factor_of_kernel_eq
    (quotientMatrix (1 : Mat3 ℂ)) (quotientMatrix (M9.TetrahedralGroup.matrix g))
    (quotientMatrix_surjective _ (by simp)) (quotientMatrix_surjective _ hg) hk
  exact ⟨A,hA,by simpa only [quotientMatrix_one] using heq⟩

def gammaFactor (g : Gamma) : Matrix (Fin 2) (Fin 2) ℂ :=
  (gamma_quotient_factor g).choose

theorem gammaFactor_det_unit (g : Gamma) : IsUnit (gammaFactor g).det :=
  (gamma_quotient_factor g).choose_spec.1

theorem gammaFactor_spec (g : Gamma) :
    quotientMatrix (M9.TetrahedralGroup.matrix g) = gammaFactor g * standardQuotient (R := ℂ) :=
  (gamma_quotient_factor g).choose_spec.2

variable {R : Type*} [CommRing R] [Algebra ℂ R]

theorem quotientMatrix_mul_gamma (F : Mat3 R) (g : Gamma) :
    quotientMatrix (F * (M9.TetrahedralGroup.matrix g).map (algebraMap ℂ R)) =
      (gammaFactor g).map (algebraMap ℂ R) * quotientMatrix F := by
  have hg := congrArg (fun A : Matrix (Fin 2) (Fin 6) ℂ => A.map (algebraMap ℂ R))
    (gammaFactor_spec g)
  rw [quotientMatrix_map,Matrix.map_mul,standardQuotient_map] at hg
  change standardQuotient (R := R) * congruence
      (F * (M9.TetrahedralGroup.matrix g).map (algebraMap ℂ R)).adjugate = _
  rw [Matrix.adjugate_mul_distrib,congruence_mul,← Matrix.mul_assoc]
  change quotientMatrix ((M9.TetrahedralGroup.matrix g).map (algebraMap ℂ R)) *
      congruence F.adjugate = _
  rw [hg,Matrix.mul_assoc]
  rfl

theorem normalize_mul_left {K : Type*} [Field K]
    (A : Matrix (Fin 2) (Fin 2) K) (Q : QMat K) (ι : Fin 2 ↪ Fin 6)
    (hA : IsUnit A.det) (hp : IsUnit (Q.submatrix id ι).det) :
    normalize (A * Q) ι = normalize Q ι := by
  have hp' : IsUnit ((A * Q).submatrix id ι).det := by
    rw [Matrix.submatrix_mul _ _ id id ι Function.bijective_id,
      Matrix.submatrix_id_id,Matrix.det_mul]
    exact hA.mul hp
  have hminor : (A * Q).submatrix id ι = A * Q.submatrix id ι := by
    rw [Matrix.submatrix_mul _ _ id id ι Function.bijective_id,Matrix.submatrix_id_id]
  have hc : ((A * Q).submatrix id ι)⁻¹ * A = (Q.submatrix id ι)⁻¹ := by
    calc
      _ = (((A * Q).submatrix id ι)⁻¹ * A) *
          ((Q.submatrix id ι) * (Q.submatrix id ι)⁻¹) := by
            rw [Matrix.mul_nonsing_inv _ hp,Matrix.mul_one]
      _ = (((A * Q).submatrix id ι)⁻¹ * (A * Q.submatrix id ι)) *
          (Q.submatrix id ι)⁻¹ := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [← hminor,Matrix.nonsing_inv_mul _ hp',Matrix.one_mul]
  change ((A * Q).submatrix id ι)⁻¹ * (A * Q) = _
  rw [← Matrix.mul_assoc,hc]
  rfl

end M9Native.ConicFrameGammaCongruence
