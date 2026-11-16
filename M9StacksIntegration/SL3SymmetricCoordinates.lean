module

public import M9.PrimitiveRepresentation
public import M9StacksIntegration.SL3CoordinateRing
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Basic

@[expose] public section

/-! Actual six-entry congruence matrices over arbitrary commutative rings.
Their coordinate specialization is the frozen symmetric-matrix action.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1500000

open Matrix

namespace M9Native.SL3SymmetricCoordinates

variable (R : Type) [CommRing R]

def entries (M : Matrix (Fin 3) (Fin 3) R) : M9.Upper3 → R :=
  fun ij => M ij.val.1 ij.val.2

omit [CommRing R] in
theorem entries_upperMatrix (v : M9.Upper3 → R) : entries R (M9.upperMatrix v) = v := by
  funext ij
  exact dite_eq_left ij.property

omit [CommRing R] in
theorem upperMatrix_entries (M : Matrix (Fin 3) (Fin 3) R) (hM : M.transpose = M) :
    M9.upperMatrix (entries R M) = M := by
  ext i j
  by_cases hij : i ≤ j
  · simp only [M9.upperMatrix, dite_eq_left hij, entries]
  · simp only [M9.upperMatrix, dite_eq_right hij, entries]
    exact congrFun (congrFun hM i) j

theorem upperMatrix_add (v w : M9.Upper3 → R) :
    M9.upperMatrix (v+w) = M9.upperMatrix v + M9.upperMatrix w := by
  ext i j
  change M9.upperMatrix (v+w) i j = M9.upperMatrix v i j + M9.upperMatrix w i j
  simp only [M9.upperMatrix]
  split_ifs <;> rfl

theorem upperMatrix_smul (c : R) (v : M9.Upper3 → R) :
    M9.upperMatrix (c • v) = c • M9.upperMatrix v := by
  ext i j
  change M9.upperMatrix (c • v) i j = c * M9.upperMatrix v i j
  simp only [M9.upperMatrix]
  split_ifs <;> rfl

def congruence (g : Matrix (Fin 3) (Fin 3) R) :
    (M9.Upper3 → R) →ₗ[R] (M9.Upper3 → R) where
  toFun v := entries R (g * M9.upperMatrix v * g.transpose)
  map_add' v w := by
    rw [upperMatrix_add, Matrix.mul_add, Matrix.add_mul]
    rfl
  map_smul' c v := by
    rw [upperMatrix_smul, Matrix.mul_smul, Matrix.smul_mul]
    rfl

theorem congruence_reconstruct (g : Matrix (Fin 3) (Fin 3) R) (v : M9.Upper3 → R) :
    M9.upperMatrix (congruence R g v) = g * M9.upperMatrix v * g.transpose := by
  change M9.upperMatrix (entries R (g * M9.upperMatrix v * g.transpose)) = _
  apply upperMatrix_entries R
  rw [Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose,
    M9.upperMatrix_transpose, Matrix.mul_assoc]

theorem congruence_one (v : M9.Upper3 → R) : congruence R 1 v = v := by
  change entries R (1 * M9.upperMatrix v * (1 : Matrix (Fin 3) (Fin 3) R).transpose) = v
  rw [Matrix.transpose_one, Matrix.one_mul, Matrix.mul_one, entries_upperMatrix]

theorem congruence_mul (g h : Matrix (Fin 3) (Fin 3) R) (v : M9.Upper3 → R) :
    congruence R (g*h) v = congruence R g (congruence R h v) := by
  change entries R ((g*h) * M9.upperMatrix v * (g*h).transpose) =
    entries R (g * M9.upperMatrix (congruence R h v) * g.transpose)
  rw [congruence_reconstruct, Matrix.transpose_mul]
  simp only [Matrix.mul_assoc]

def matrix (g : Matrix (Fin 3) (Fin 3) R) : Matrix M9.Upper3 M9.Upper3 R :=
  LinearMap.toMatrix' (congruence R g)

theorem matrix_mulVec (g : Matrix (Fin 3) (Fin 3) R) (v : M9.Upper3 → R) :
    matrix R g *ᵥ v = congruence R g v := LinearMap.toMatrix'_mulVec _ _

theorem matrix_one : matrix R 1 = 1 := by
  have h : congruence R 1 = LinearMap.id := LinearMap.ext (congruence_one R)
  rw [matrix, h, LinearMap.toMatrix'_id]

theorem matrix_mul (g h : Matrix (Fin 3) (Fin 3) R) :
    matrix R (g*h) = matrix R g * matrix R h := by
  rw [matrix, matrix, matrix, ← LinearMap.toMatrix'_comp]
  congr 1
  exact LinearMap.ext (congruence_mul R g h)

def linearEquiv (g : Matrix.SpecialLinearGroup (Fin 3) R) :
    (M9.Upper3 → R) ≃ₗ[R] (M9.Upper3 → R) where
  __ := congruence R g.val
  invFun := congruence R (g⁻¹).val
  left_inv v := by
    change congruence R (g⁻¹).val (congruence R g.val v) = v
    exact (congruence_mul R (g⁻¹).val g.val v).symm.trans (by
      rw [show (g⁻¹).val * g.val = 1 from congrArg Subtype.val (inv_mul_cancel g), congruence_one])
  right_inv v := by
    change congruence R g.val (congruence R (g⁻¹).val v) = v
    exact (congruence_mul R g.val (g⁻¹).val v).symm.trans (by
      rw [show g.val * (g⁻¹).val = 1 from congrArg Subtype.val (mul_inv_cancel g), congruence_one])

def matrixGL (g : Matrix.SpecialLinearGroup (Fin 3) R) :
    Matrix.GeneralLinearGroup M9.Upper3 R where
  val := matrix R g.val
  inv := matrix R (g⁻¹).val
  val_inv := by
    rw [← matrix_mul, show g.val * (g⁻¹).val = 1 from congrArg Subtype.val (mul_inv_cancel g),
      matrix_one]
  inv_val := by
    rw [← matrix_mul, show (g⁻¹).val * g.val = 1 from congrArg Subtype.val (inv_mul_cancel g),
      matrix_one]

variable {S : Type} [CommRing S]

theorem upperMatrix_map (ρ : R →+* S) (v : M9.Upper3 → R) :
    (M9.upperMatrix v).map ρ = M9.upperMatrix (fun ij => ρ (v ij)) := by
  ext i j
  simp only [M9.upperMatrix, Matrix.map_apply]
  split_ifs <;> rfl

theorem congruence_map (ρ : R →+* S) (g : Matrix (Fin 3) (Fin 3) R) (v : M9.Upper3 → R) :
    (fun ij => ρ (congruence R g v ij)) =
      congruence S (g.map ρ) (fun ij => ρ (v ij)) := by
  have h : (g * M9.upperMatrix v * g.transpose).map ρ =
      g.map ρ * M9.upperMatrix (fun ij => ρ (v ij)) * (g.map ρ).transpose := by
    rw [Matrix.map_mul, Matrix.map_mul, upperMatrix_map, Matrix.transpose_map]
  funext ij
  exact congrFun (congrFun h ij.val.1) ij.val.2

theorem matrix_map (ρ : R →+* S) (g : Matrix (Fin 3) (Fin 3) R) :
    (matrix R g).map ρ = matrix S (g.map ρ) := by
  ext i j
  have h := congrFun (congruence_map R ρ g (Pi.single j 1)) i
  have hs : (fun ij : M9.Upper3 => ρ ((Pi.single j (1 : R) : M9.Upper3 → R) ij)) =
      (Pi.single j (1 : S) : M9.Upper3 → S) := by
    funext ij
    by_cases hij : ij = j <;> simp [hij]
  rw [hs] at h
  simpa only [matrix, LinearMap.toMatrix'_apply, Matrix.map_apply] using h

/-- Over a field these are the actual original six symmetric-matrix coordinates. -/
theorem matrix_fieldCoordinates (K : Type) [Field K]
    (g : Matrix (Fin 3) (Fin 3) K) (X : M9.Symmetric3 K) :
    matrix K g *ᵥ M9.symmetric3Coordinates K X =
      M9.symmetric3Coordinates K (M9.PrimitiveRepresentation.congruence K g X) := by
  rw [matrix_mulVec]
  have hX : M9.upperMatrix (M9.symmetric3Coordinates K X) = X.val :=
    congrArg Subtype.val ((M9.symmetric3Coordinates K).symm_apply_apply X)
  change entries K (g * M9.upperMatrix (M9.symmetric3Coordinates K X) * g.transpose) = _
  rw [hX]
  rfl

theorem linearEquiv_fieldCoordinates (K : Type) [Field K]
    (g : Matrix.SpecialLinearGroup (Fin 3) K) (X : M9.Symmetric3 K) :
    linearEquiv K g (M9.symmetric3Coordinates K X) =
      M9.symmetric3Coordinates K (M9.PrimitiveRepresentation.congruence K g.val X) := by
  exact (matrix_mulVec K g.val _).symm.trans (matrix_fieldCoordinates K g.val X)

end M9Native.SL3SymmetricCoordinates
