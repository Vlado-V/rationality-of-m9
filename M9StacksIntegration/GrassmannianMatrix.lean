module

public import Mathlib.LinearAlgebra.Vandermonde
public import Mathlib.RingTheory.Localization.FractionRing

/-! Pure matrix preparation for the native Grassmannian charts. -/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false

universe u

namespace M9Native.GrassmannianCharts

variable (K : Type u) [Field K] (r n : ℕ)

/-- A rectangular Vandermonde matrix whose every maximal column minor is nonzero. -/
def fullMinorMatrix [Infinite K] : Matrix (Fin (n-r)) (Fin n) K :=
  fun i j => (Infinite.natEmbedding K j.val) ^ i.val

theorem fullMinorMatrix_det_ne_zero [Infinite K] (ι : Fin (n-r) ↪ Fin n) :
    Matrix.det ((fullMinorMatrix K r n).submatrix id ι) ≠ 0 := by
  have hmat : (fullMinorMatrix K r n).submatrix id ι =
      (Matrix.vandermonde (fun j : Fin (n-r) => Infinite.natEmbedding K (ι j).val)).transpose := rfl
  rw [hmat,Matrix.det_transpose,Matrix.det_vandermonde_ne_zero_iff]
  exact (Infinite.natEmbedding K).injective.comp (Fin.val_injective.comp ι.injective)

/-- Normalize the rectangular matrix on the selected pivot columns. -/
def normalizedMatrix [Infinite K] (κ : Fin (n-r) ↪ Fin n) : Matrix (Fin (n-r)) (Fin n) K :=
  ((fullMinorMatrix K r n).submatrix id κ)⁻¹ * fullMinorMatrix K r n

theorem normalizedMatrix_submatrix [Infinite K] (κ ι : Fin (n-r) ↪ Fin n) :
    (normalizedMatrix K r n κ).submatrix id ι =
      ((fullMinorMatrix K r n).submatrix id κ)⁻¹ * (fullMinorMatrix K r n).submatrix id ι := rfl

theorem normalizedMatrix_pivots [Infinite K] (κ : Fin (n-r) ↪ Fin n) :
    (normalizedMatrix K r n κ).submatrix id κ = 1 := by
  rw [normalizedMatrix_submatrix]
  exact Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr (fullMinorMatrix_det_ne_zero K r n κ))

theorem normalizedMatrix_det_ne_zero [Infinite K] (κ ι : Fin (n-r) ↪ Fin n) :
    Matrix.det ((normalizedMatrix K r n κ).submatrix id ι) ≠ 0 := by
  rw [normalizedMatrix_submatrix,Matrix.det_mul]
  exact mul_ne_zero (isUnit_iff_ne_zero.mp (Matrix.isUnit_nonsing_inv_det _
    (isUnit_iff_ne_zero.mpr (fullMinorMatrix_det_ne_zero K r n κ))))
    (fullMinorMatrix_det_ne_zero K r n ι)

end M9Native.GrassmannianCharts
