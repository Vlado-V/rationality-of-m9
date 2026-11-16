module

public import M9StacksIntegration.MatrixChartFieldRecovery

/-! A normalized quotient chart is the actual pivot normalization of every split quotient
with the same literal kernel. All row-change and pivot invertibility statements are derived. -/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open Matrix

namespace M9Native.MatrixKernelChartNormalization

variable {K m n : Type*} [Field K] [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]

def pivotSection (e : m → n) : Matrix n m K := (1 : Matrix n n K).submatrix id e

theorem mul_section (A : Matrix m n K) (e : m → n) : A * pivotSection e = A.submatrix id e := by
  ext i j
  simp [pivotSection, Matrix.mul_apply, Matrix.one_apply]

theorem row_change (Q N : Matrix m n K) (e : m → n) (hN : N.submatrix id e = 1)
    (hker : ∀ v, N *ᵥ v = 0 → Q *ᵥ v = 0) : Q = Q.submatrix id e * N := by
  have hNS : N * (pivotSection (K := K) e : Matrix n m K) = (1 : Matrix m m K) :=
    (mul_section N e).trans hN
  apply Matrix.toLin'.injective
  apply LinearMap.ext
  intro v
  have hz : N *ᵥ (v - pivotSection e *ᵥ (N *ᵥ v)) = 0 := by
    rw [Matrix.mulVec_sub, Matrix.mulVec_mulVec, hNS, Matrix.one_mulVec, sub_self]
  have hq := hker _ hz
  rw [Matrix.mulVec_sub] at hq
  have he := sub_eq_zero.mp hq
  change Q *ᵥ v = (Q.submatrix id e * N) *ᵥ v
  rw [← Matrix.mulVec_mulVec, ← mul_section Q e, ← Matrix.mulVec_mulVec]
  exact he

/-- Actual same-kernel normalized chart data force a unit pivot and the precise matrix formula. -/
theorem normalize_of_same_kernel (Q N : Matrix m n K) (R : Matrix n m K)
    (hQR : Q*R = 1) (e : m → n) (hN : N.submatrix id e = 1)
    (hker : ∀ v, N *ᵥ v = 0 → Q *ᵥ v = 0) :
    IsUnit (Q.submatrix id e).det ∧ N = (Q.submatrix id e)⁻¹ * Q := by
  have hQ := row_change Q N e hN hker
  have hunit : IsUnit (Q.submatrix id e).det := by
    apply isUnit_iff_exists_inv.mpr
    refine ⟨(N*R).det, ?_⟩
    rw [← Matrix.det_mul, ← Matrix.mul_assoc, ← hQ, hQR, Matrix.det_one]
  refine ⟨hunit, ?_⟩
  apply Eq.symm
  calc
    _ = (Q.submatrix id e)⁻¹ * (Q.submatrix id e * N) :=
      congrArg (fun A : Matrix m n K => (Q.submatrix id e)⁻¹ * A) hQ
    _ = N := by
      rw [← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hunit, Matrix.one_mul]

end M9Native.MatrixKernelChartNormalization
