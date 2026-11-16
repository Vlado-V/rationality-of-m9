module

public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.Algebra.Field.Subfield.Basic
public import Mathlib.Tactic

/-! Literal recovery of a split quotient from an acted normalized matrix chart.
The formula uses its actual fixed right inverse, and also proves field-of-definition recovery. -/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open Matrix
open scoped BigOperators

universe u v w

namespace M9Native.MatrixChartFieldRecovery

variable {K : Type u} [Field K] {m : Type v} {n : Type w}
  [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]

def normalized (Q : Matrix m n K) (M : Matrix.GeneralLinearGroup n K) (e : m → n) :
    Matrix m n K := ((Q * (↑M⁻¹ : Matrix n n K)).submatrix id e)⁻¹ * Q * (↑M⁻¹ : Matrix n n K)

theorem normalized_mul (Q : Matrix m n K) (M : Matrix.GeneralLinearGroup n K) (e : m → n) :
    normalized Q M e * (M : Matrix n n K) =
      ((Q * (↑M⁻¹ : Matrix n n K)).submatrix id e)⁻¹ * Q := by
  rw [normalized, Matrix.mul_assoc, Units.inv_mul, Matrix.mul_one]

theorem normalized_mul_section (Q : Matrix m n K) (S : Matrix n m K)
    (hQS : Q*S = 1) (M : Matrix.GeneralLinearGroup n K) (e : m → n) :
    normalized Q M e * (M : Matrix n n K) * S =
      ((Q * (↑M⁻¹ : Matrix n n K)).submatrix id e)⁻¹ := by
  rw [normalized_mul, Matrix.mul_assoc, hQS, Matrix.mul_one]

/-- The original quotient is rationally recovered from its actual normalized translate,
the actual translating matrix, and the original fixed section. -/
theorem recover (Q : Matrix m n K) (S : Matrix n m K) (hQS : Q*S = 1)
    (M : Matrix.GeneralLinearGroup n K) (e : m → n)
    (hP : IsUnit ((Q * (↑M⁻¹ : Matrix n n K)).submatrix id e).det) :
    (normalized Q M e * (M : Matrix n n K) * S)⁻¹ *
      (normalized Q M e * (M : Matrix n n K)) = Q := by
  cases ((Matrix.isUnit_iff_isUnit_det _).mpr hP).nonempty_invertible
  rw [normalized_mul_section Q S hQS, normalized_mul, Matrix.inv_inv_of_invertible,
    ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hP, Matrix.one_mul]

variable (E : Subfield K)

def EntriesIn {ι κ : Type*} (A : Matrix ι κ K) : Prop := ∀ i j, A i j ∈ E

theorem EntriesIn.mul {ι κ τ : Type*} [Fintype κ]
    {A : Matrix ι κ K} {B : Matrix κ τ K} (hA : EntriesIn E A) (hB : EntriesIn E B) :
    EntriesIn E (A*B) := by
  intro i j
  exact E.sum_mem (fun k _ => E.mul_mem (hA i k) (hB k j))

theorem EntriesIn.transpose {ι κ : Type*} {A : Matrix ι κ K} (hA : EntriesIn E A) :
    EntriesIn E Aᵀ := fun i j => hA j i

theorem EntriesIn.submatrix {ι κ τ υ : Type*} {A : Matrix ι κ K}
    (hA : EntriesIn E A) (f : τ → ι) (g : υ → κ) : EntriesIn E (A.submatrix f g) :=
  fun i j => hA (f i) (g j)

def restrictMatrix {ι κ : Type*} (A : Matrix ι κ K) (hA : EntriesIn E A) : Matrix ι κ E :=
  fun i j => ⟨A i j, hA i j⟩

theorem map_restrictMatrix {ι κ : Type*} (A : Matrix ι κ K) (hA : EntriesIn E A) :
    (restrictMatrix E A hA).map E.subtype = A := rfl

theorem inverse_map_fields {L : Type*} [Field L] (φ : K →+* L) (A : Matrix m m K) :
    A⁻¹.map φ = (A.map φ)⁻¹ := by
  ext i j
  simp only [Matrix.inv_def, Matrix.map_apply, Matrix.smul_apply, smul_eq_mul,
    map_mul, Ring.inverse_eq_inv, map_inv₀]
  rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]
  have h := φ.map_adjugate A
  exact congrArg (fun M : Matrix m m L =>
    (φ A.det)⁻¹ * M i j) h

theorem EntriesIn.inv {A : Matrix m m K} (hA : EntriesIn E A) : EntriesIn E A⁻¹ := by
  have he : (restrictMatrix E A hA)⁻¹.map E.subtype = A⁻¹ := by
    rw [inverse_map_fields, map_restrictMatrix]
  intro i j
  have hm : E.subtype (((restrictMatrix E A hA)⁻¹) i j) ∈ E :=
    (((restrictMatrix E A hA)⁻¹) i j).property
  change ((restrictMatrix E A hA)⁻¹.map E.subtype) i j ∈ E at hm
  rw [he] at hm
  exact hm

/-- Field-of-definition recovery is deduced from the explicit formula, not assumed. -/
theorem entriesIn_recovered_quotient (Q : Matrix m n K) (S : Matrix n m K) (hQS : Q*S = 1)
    (M : Matrix.GeneralLinearGroup n K) (e : m → n)
    (hP : IsUnit ((Q * (↑M⁻¹ : Matrix n n K)).submatrix id e).det)
    (hN : EntriesIn E (normalized Q M e)) (hM : EntriesIn E (M : Matrix n n K))
    (hS : EntriesIn E S) : EntriesIn E Q := by
  rw [← recover Q S hQS M e hP]
  exact (((hN.mul E hM).mul E hS).inv E).mul E (hN.mul E hM)

end M9Native.MatrixChartFieldRecovery
