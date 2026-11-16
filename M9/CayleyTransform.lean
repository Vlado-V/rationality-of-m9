module

public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Tactic.NoncommRing
import Mathlib.Tactic.Module
import Mathlib.Tactic.NormNum

/-!
The matrix Cayley transformation in Sections 5.2--5.3 of the source paper
`024b7b64a33ccccd578888d0b433357414fbe9c6e0510ef48151852ffae53199`.
All identities concern actual finite square matrices; denominators are
controlled by their determinants.
-/

@[expose] public section

noncomputable section

namespace M9

open Matrix

variable {K : Type*} [Field K] [CharZero K]
variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The Cayley coordinate of an actual square matrix. -/
def cayley (X : Matrix n n K) : Matrix n n K :=
  (X - 1) * (X + 1)⁻¹

/-- The rational inverse Cayley coordinate. -/
def inverseCayley (C : Matrix n n K) : Matrix n n K :=
  (1 - C)⁻¹ * (1 + C)

private theorem two_ne_zero : (2 : K) ≠ 0 := by norm_num

omit [CharZero K] in
theorem cayley_mul_add_one (X : Matrix n n K) (hplus : (X + 1).det ≠ 0) :
    cayley X * (X + 1) = X - 1 := by
  exact Matrix.nonsing_inv_mul_cancel_right (X + 1) (X - 1)
    (isUnit_iff_ne_zero.mpr hplus)

omit [CharZero K] in
theorem add_one_mul_cayley (X : Matrix n n K) (hplus : (X + 1).det ≠ 0) :
    (X + 1) * cayley X = X - 1 := by
  have hcomm : (X + 1) * (X - 1) = (X - 1) * (X + 1) := by noncomm_ring
  unfold cayley
  rw [← mul_assoc, hcomm]
  exact Matrix.mul_nonsing_inv_cancel_right (X + 1) (X - 1)
    (isUnit_iff_ne_zero.mpr hplus)

omit [CharZero K] in
theorem one_sub_cayley_mul_add_one (X : Matrix n n K) (hplus : (X + 1).det ≠ 0) :
    (1 - cayley X) * (X + 1) = (2 : K) • (1 : Matrix n n K) := by
  rw [sub_mul, one_mul, cayley_mul_add_one X hplus]
  rw [two_smul]
  noncomm_ring

omit [CharZero K] in
theorem one_add_cayley_mul_add_one (X : Matrix n n K) (hplus : (X + 1).det ≠ 0) :
    (1 + cayley X) * (X + 1) = (2 : K) • X := by
  rw [add_mul, one_mul, cayley_mul_add_one X hplus, two_smul]
  noncomm_ring

theorem one_sub_cayley_det_ne_zero (X : Matrix n n K) (hplus : (X + 1).det ≠ 0) :
    (1 - cayley X).det ≠ 0 := by
  have h : ((1 - cayley X) * (X + 1)).det ≠ 0 := by
    rw [one_sub_cayley_mul_add_one X hplus, Matrix.det_smul, Matrix.det_one]
    exact mul_ne_zero (pow_ne_zero _ two_ne_zero) one_ne_zero
  rw [Matrix.det_mul] at h
  exact (mul_ne_zero_iff.mp h).1

theorem one_add_cayley_det_ne_zero (X : Matrix n n K)
    (hX : X.det ≠ 0) (hplus : (X + 1).det ≠ 0) :
    (1 + cayley X).det ≠ 0 := by
  have h : ((1 + cayley X) * (X + 1)).det ≠ 0 := by
    rw [one_add_cayley_mul_add_one X hplus, Matrix.det_smul]
    exact mul_ne_zero (pow_ne_zero _ two_ne_zero) hX
  rw [Matrix.det_mul] at h
  exact (mul_ne_zero_iff.mp h).1

theorem one_sub_cayley_inv (X : Matrix n n K) (hplus : (X + 1).det ≠ 0) :
    (1 - cayley X)⁻¹ = (2 : K)⁻¹ • (X + 1) := by
  apply Matrix.inv_eq_right_inv
  rw [Matrix.mul_smul, one_sub_cayley_mul_add_one X hplus, smul_smul]
  simp

theorem inverseCayley_cayley (X : Matrix n n K) (hplus : (X + 1).det ≠ 0) :
    inverseCayley (cayley X) = X := by
  rw [inverseCayley, one_sub_cayley_inv X hplus, Matrix.smul_mul,
    mul_add, mul_one, add_one_mul_cayley X hplus]
  have h : (X + 1) + (X - 1) = (2 : K) • X := by rw [two_smul]; noncomm_ring
  rw [h, smul_smul]
  simp

omit [CharZero K] in
theorem inverseCayley_add_one_mul (C : Matrix n n K) (hminus : (1 - C).det ≠ 0) :
    (inverseCayley C + 1) * (1 - C) = (2 : K) • (1 : Matrix n n K) := by
  have hcomm : (1 + C) * (1 - C) = (1 - C) * (1 + C) := by noncomm_ring
  unfold inverseCayley
  rw [add_mul, one_mul, mul_assoc, hcomm,
    Matrix.nonsing_inv_mul_cancel_left _ _ (isUnit_iff_ne_zero.mpr hminus), two_smul]
  noncomm_ring

omit [CharZero K] in
theorem inverseCayley_sub_one_mul (C : Matrix n n K) (hminus : (1 - C).det ≠ 0) :
    (inverseCayley C - 1) * (1 - C) = (2 : K) • C := by
  have hcomm : (1 + C) * (1 - C) = (1 - C) * (1 + C) := by noncomm_ring
  unfold inverseCayley
  rw [sub_mul, one_mul, mul_assoc, hcomm,
    Matrix.nonsing_inv_mul_cancel_left _ _ (isUnit_iff_ne_zero.mpr hminus), two_smul]
  noncomm_ring

theorem inverseCayley_add_one_inv (C : Matrix n n K) (hminus : (1 - C).det ≠ 0) :
    (inverseCayley C + 1)⁻¹ = (2 : K)⁻¹ • (1 - C) := by
  apply Matrix.inv_eq_right_inv
  rw [Matrix.mul_smul, inverseCayley_add_one_mul C hminus, smul_smul]
  simp

theorem cayley_inverseCayley (C : Matrix n n K) (hminus : (1 - C).det ≠ 0) :
    cayley (inverseCayley C) = C := by
  rw [cayley, inverseCayley_add_one_inv C hminus, Matrix.mul_smul,
    inverseCayley_sub_one_mul C hminus, smul_smul]
  simp

omit [CharZero K] in
theorem inverseCayley_det_ne_zero (C : Matrix n n K)
    (hminus : (1 - C).det ≠ 0) (hplus : (1 + C).det ≠ 0) :
    (inverseCayley C).det ≠ 0 := by
  rw [inverseCayley, Matrix.det_mul]
  exact mul_ne_zero
    (Matrix.isUnit_nonsing_inv_det _ (isUnit_iff_ne_zero.mpr hminus)).ne_zero hplus

theorem inverseCayley_add_one_det_ne_zero (C : Matrix n n K)
    (hminus : (1 - C).det ≠ 0) : (inverseCayley C + 1).det ≠ 0 := by
  have h : ((inverseCayley C + 1) * (1 - C)).det ≠ 0 := by
    rw [inverseCayley_add_one_mul C hminus, Matrix.det_smul, Matrix.det_one]
    exact mul_ne_zero (pow_ne_zero _ two_ne_zero) one_ne_zero
  rw [Matrix.det_mul] at h
  exact (mul_ne_zero_iff.mp h).1

/-- The actual two determinant opens on the graph coordinate space. -/
def CayleySource (K : Type*) [Field K] (n : Type*) [Fintype n] [DecidableEq n] :=
  {X : Matrix n n K // X.det ≠ 0 ∧ (X + 1).det ≠ 0}

/-- The corresponding two determinant opens in the linearized coordinates. -/
def CayleyTarget (K : Type*) [Field K] (n : Type*) [Fintype n] [DecidableEq n] :=
  {C : Matrix n n K // (1 - C).det ≠ 0 ∧ (1 + C).det ≠ 0}

/-- Mutually inverse rational matrix coordinates on the specified opens. -/
def cayleyEquiv : CayleySource K n ≃ CayleyTarget K n where
  toFun X := ⟨cayley X.val, one_sub_cayley_det_ne_zero _ X.property.2,
    one_add_cayley_det_ne_zero _ X.property.1 X.property.2⟩
  invFun C := ⟨inverseCayley C.val,
    inverseCayley_det_ne_zero _ C.property.1 C.property.2,
    inverseCayley_add_one_det_ne_zero _ C.property.1⟩
  left_inv X := Subtype.ext (inverseCayley_cayley _ X.property.2)
  right_inv C := Subtype.ext (cayley_inverseCayley _ C.property.1)

omit [CharZero K] in
theorem inverse_add_one_inv (X : Matrix n n K)
    (hX : X.det ≠ 0) (hplus : (X + 1).det ≠ 0) :
    (X⁻¹ + 1)⁻¹ = X * (X + 1)⁻¹ := by
  apply Matrix.inv_eq_right_inv
  rw [← mul_assoc, add_mul,
    Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr hX), one_mul, add_comm]
  exact Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hplus)

omit [CharZero K] in
theorem inverse_add_one_det_ne_zero (X : Matrix n n K)
    (hX : X.det ≠ 0) (hplus : (X + 1).det ≠ 0) :
    (X⁻¹ + 1).det ≠ 0 := by
  apply Matrix.det_ne_zero_of_right_inverse
  rw [← mul_assoc, add_mul,
    Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr hX), one_mul, add_comm]
  exact Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hplus)

omit [CharZero K] in
/-- Matrix inversion becomes negation in Cayley coordinates. -/
theorem cayley_inv (X : Matrix n n K)
    (hX : X.det ≠ 0) (hplus : (X + 1).det ≠ 0) :
    cayley X⁻¹ = -cayley X := by
  unfold cayley
  rw [inverse_add_one_inv X hX hplus, ← mul_assoc, sub_mul,
    Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr hX), one_mul]
  noncomm_ring

open scoped BigOperators in
omit [CharZero K] in
/-- Every coordinate is the displayed rational expression with determinant denominator. -/
theorem cayley_apply (X : Matrix n n K) (i j : n) :
    cayley X i j =
      (X + 1).det⁻¹ * ∑ k, (X - 1) i k * (X + 1).adjugate k j := by
  rw [cayley, Matrix.inv_def, Ring.inverse_eq_inv, Matrix.mul_smul]
  simp only [Matrix.smul_apply, smul_eq_mul, Matrix.mul_apply]

open scoped BigOperators in
omit [CharZero K] in
theorem inverseCayley_apply (C : Matrix n n K) (i j : n) :
    inverseCayley C i j =
      (1 - C).det⁻¹ * ∑ k, (1 - C).adjugate i k * (1 + C) k j := by
  rw [inverseCayley, Matrix.inv_def, Ring.inverse_eq_inv, Matrix.smul_mul]
  simp only [Matrix.smul_apply, smul_eq_mul, Matrix.mul_apply]

section CoefficientMaps

variable {F : Type*} [Field F] [CharZero F]

omit [CharZero K] [CharZero F] in
theorem map_matrix_inverse (φ : K →+* F) (X : Matrix n n K) (hX : X.det ≠ 0) :
    φ.mapMatrix X⁻¹ = (φ.mapMatrix X)⁻¹ := by
  symm
  apply Matrix.inv_eq_right_inv
  rw [← map_mul, Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hX), map_one]

omit [CharZero K] [CharZero F] in
theorem map_cayley (φ : K →+* F) (X : Matrix n n K) (hplus : (X + 1).det ≠ 0) :
    φ.mapMatrix (cayley X) = cayley (φ.mapMatrix X) := by
  rw [cayley, map_mul, map_sub, map_one, map_matrix_inverse φ (X + 1) hplus,
    map_add, map_one]
  rfl

end CoefficientMaps

omit [CharZero K] in
/-- An entrywise field automorphism acting by inversion on the graph matrix
acts by negation on its Cayley matrix. -/
theorem map_cayley_of_inversion (σ : K ≃+* K) (X : Matrix n n K)
    (hX : X.det ≠ 0) (hplus : (X + 1).det ≠ 0)
    (hσ : σ.toRingHom.mapMatrix X = X⁻¹) :
    σ.toRingHom.mapMatrix (cayley X) = -cayley X := by
  rw [map_cayley σ.toRingHom X hplus, hσ, cayley_inv X hX hplus]

omit [CharZero K] in
/-- Dividing Cayley coordinates by an anti-invariant scalar makes every
matrix entry invariant under the given field automorphism. -/
theorem normalized_cayley_fixed (σ : K ≃+* K) (X : Matrix n n K) (θ : K)
    (hX : X.det ≠ 0) (hplus : (X + 1).det ≠ 0)
    (hσ : σ.toRingHom.mapMatrix X = X⁻¹) (hθ : σ θ = -θ) :
    σ.toRingHom.mapMatrix (θ⁻¹ • cayley X) = θ⁻¹ • cayley X := by
  have hC := map_cayley_of_inversion σ X hX hplus hσ
  ext i j
  have hentry : σ (cayley X i j) = -(cayley X i j) :=
    congrFun (congrFun hC i) j
  change σ (θ⁻¹ * cayley X i j) = θ⁻¹ * cayley X i j
  rw [map_mul, map_inv₀, hθ, hentry]
  simp

end M9
