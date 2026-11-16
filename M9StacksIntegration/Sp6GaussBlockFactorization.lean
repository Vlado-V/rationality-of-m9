module

public import M9StacksIntegration.PrimitiveGaussFamily
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs

/-!
# Full GL3 Gauss factorization in the actual symplectic group

All identities hold over every commutative ring. The actual invertible
top-left block supplies the inverse coordinates, and symplecticity
proves that both shear coordinates are symmetric. No reducedness,
domain or density hypothesis occurs.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
set_option maxRecDepth 4096

open Matrix

universe u

namespace M9Native.Sp6GaussBlockFactorization

abbrev Mat3 (R : Type u) := Matrix (Fin 3) (Fin 3) R
abbrev Symmetric3 (R : Type u) := {A : Mat3 R // A.transpose = A}

variable {R : Type u} [CommRing R]

/-- The full actual GL3 Levi subgroup of the native symplectic group. -/
def levi (A : Matrix.GeneralLinearGroup (Fin 3) R) :
    Matrix.symplecticGroup (Fin 3) R :=
  ⟨Matrix.fromBlocks A.val 0 0 (A⁻¹).val.transpose, by
    apply SymplecticGroup.fromBlocks_mem_iff.mpr
    refine ⟨by simp, by simp, ?_⟩
    simp only [Matrix.transpose_zero, Matrix.zero_mul, sub_zero]
    have hm : (A⁻¹).val * A.val = 1 := A.inv_val
    rw [← Matrix.transpose_mul, hm, Matrix.transpose_one]⟩

/-- The actual lower–Levi–upper Gauss matrix. -/
def gauss (S : Symmetric3 R) (A : Matrix.GeneralLinearGroup (Fin 3) R)
    (T : Symmetric3 R) : Matrix.symplecticGroup (Fin 3) R :=
  PrimitiveGaussFamily.lower S.val S.property * levi A *
    PrimitiveGaussFamily.upper T.val T.property

theorem gauss_blocks (S : Symmetric3 R) (A : Matrix.GeneralLinearGroup (Fin 3) R)
    (T : Symmetric3 R) :
    (gauss S A T).val = Matrix.fromBlocks A.val (A.val * T.val) (S.val * A.val)
      (S.val * A.val * T.val + (A⁻¹).val.transpose) := by
  simp only [gauss, levi, PrimitiveGaussFamily.lower, PrimitiveGaussFamily.upper,
    Submonoid.coe_mul, Matrix.fromBlocks_multiply, Matrix.mul_zero, Matrix.zero_mul,
    Matrix.mul_one, Matrix.one_mul, add_zero, zero_add]

variable (A B C D : Mat3 R)
  (h : Matrix.fromBlocks A B C D ∈ Matrix.symplecticGroup (Fin 3) R)
  (hA : IsUnit A.det)

include h hA

/-- The actual lower inverse coordinate is symmetric. -/
theorem lower_coordinate_symmetric : (C * A⁻¹).transpose = C * A⁻¹ := by
  have hAC := (SymplecticGroup.fromBlocks_mem_iff.mp h).1
  have hAT : IsUnit A.transpose.det := by simpa only [Matrix.det_transpose] using hA
  calc
    (C * A⁻¹).transpose = A.transpose⁻¹ * C.transpose := by
      rw [Matrix.transpose_mul, Matrix.transpose_nonsing_inv]
    _ = A.transpose⁻¹ * (C.transpose * A) * A⁻¹ := by
      simp only [Matrix.mul_assoc, Matrix.mul_nonsing_inv A hA, Matrix.mul_one]
    _ = A.transpose⁻¹ * (A.transpose * C) * A⁻¹ := by rw [hAC]
    _ = C * A⁻¹ := by
      simp only [← Matrix.mul_assoc, Matrix.nonsing_inv_mul A.transpose hAT, Matrix.one_mul]

/-- The actual upper inverse coordinate is symmetric. -/
theorem upper_coordinate_symmetric : (A⁻¹ * B).transpose = A⁻¹ * B := by
  have ht := SymplecticGroup.transpose_mem h
  rw [Matrix.fromBlocks_transpose] at ht
  have hAB : A * B.transpose = B * A.transpose := by
    simpa only [Matrix.transpose_transpose] using
      (SymplecticGroup.fromBlocks_mem_iff.mp ht).1
  have hAT : IsUnit A.transpose.det := by simpa only [Matrix.det_transpose] using hA
  calc
    (A⁻¹ * B).transpose = B.transpose * A.transpose⁻¹ := by
      rw [Matrix.transpose_mul, Matrix.transpose_nonsing_inv]
    _ = A⁻¹ * (A * B.transpose) * A.transpose⁻¹ := by
      simp only [← Matrix.mul_assoc, Matrix.nonsing_inv_mul A hA, Matrix.one_mul]
    _ = A⁻¹ * (B * A.transpose) * A.transpose⁻¹ := by rw [hAB]
    _ = A⁻¹ * B := by
      simp only [Matrix.mul_assoc, Matrix.mul_nonsing_inv A.transpose hAT, Matrix.mul_one]

/-- Symplecticity determines the remaining lower-right block from
the three actual Gauss coordinates. -/
theorem lowerRight_eq :
    D = C * A⁻¹ * B + A⁻¹.transpose := by
  have hD0 : A.transpose * D = 1 + C.transpose * B :=
    (sub_eq_iff_eq_add).mp (SymplecticGroup.fromBlocks_mem_iff.mp h).2.2
  have hAT : IsUnit A.transpose.det := by simpa only [Matrix.det_transpose] using hA
  have hD : D = A.transpose⁻¹ + A.transpose⁻¹ * C.transpose * B := by
    simpa only [Matrix.mul_add, Matrix.mul_one, ← Matrix.mul_assoc,
      Matrix.nonsing_inv_mul A.transpose hAT, Matrix.one_mul] using
      congrArg (fun M : Mat3 R => A.transpose⁻¹ * M) hD0
  have hCA : A⁻¹.transpose * C.transpose = C * A⁻¹ := by
    simpa only [Matrix.transpose_mul] using lower_coordinate_symmetric A B C D h hA
  simpa only [← Matrix.transpose_nonsing_inv, hCA, add_comm] using hD

/-- The actual inverse Gauss coordinates reconstruct the original
matrix over the original coefficient ring. -/
theorem gauss_reconstruct :
    (gauss ⟨C * A⁻¹, lower_coordinate_symmetric A B C D h hA⟩
      (Matrix.GeneralLinearGroup.mk'' A hA)
      ⟨A⁻¹ * B, upper_coordinate_symmetric A B C D h hA⟩).val =
        Matrix.fromBlocks A B C D := by
  rw [gauss_blocks]
  change Matrix.fromBlocks A (A * (A⁻¹ * B)) ((C * A⁻¹) * A)
    (((C * A⁻¹) * A) * (A⁻¹ * B) + A⁻¹.transpose) =
      Matrix.fromBlocks A B C D
  apply Matrix.fromBlocks_inj.mpr
  refine ⟨rfl, Matrix.mul_nonsing_inv_cancel_left A B hA,
    Matrix.nonsing_inv_mul_cancel_right A C hA, ?_⟩
  rw [Matrix.nonsing_inv_mul_cancel_right A C hA]
  simpa only [Matrix.mul_assoc] using (lowerRight_eq A B C D h hA).symm

end M9Native.Sp6GaussBlockFactorization

