module

public import Mathlib.LinearAlgebra.Matrix.Trace
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.Analysis.Complex.Basic

@[expose] public section
noncomputable section

namespace M9

/-- Rational functions in `n` genuinely independent coordinates. -/
abbrev RationalField (K : Type*) [Field K] (n : ℕ) :=
  FractionRing (MvPolynomial (Fin n) K)

/-- A concrete field is rational of the specified dimension over its base. -/
def RationalOfDimension (K F : Type*) [Field K] [Field F] [Algebra K F] (n : ℕ) : Prop :=
  Nonempty (F ≃ₐ[K] RationalField K n)

/-- The actual space of symmetric ternary matrices. -/
def Symmetric3 (K : Type*) [Field K] : Submodule K (Matrix (Fin 3) (Fin 3) K) where
  carrier := {M | M.transpose = M}
  zero_mem' := rfl
  add_mem' := by
    intro X Y hX hY
    change X.transpose = X at hX
    change Y.transpose = Y at hY
    change (X + Y).transpose = X + Y
    rw [Matrix.transpose_add, hX, hY]
  smul_mem' := by
    intro c X hX
    change X.transpose = X at hX
    change (c • X).transpose = c • X
    rw [Matrix.transpose_smul, hX]

abbrev Upper3 := {ij : Fin 3 × Fin 3 // ij.1 ≤ ij.2}

@[simp] theorem card_upper3 : Fintype.card Upper3 = 6 := by decide

/-- Reconstruct a symmetric matrix from its six upper-triangular entries. -/
def upperMatrix {K : Type*} (v : Upper3 → K) : Matrix (Fin 3) (Fin 3) K :=
  fun i j => if hij : i ≤ j then v ⟨(i,j),hij⟩ else v ⟨(j,i), le_of_not_ge hij⟩

theorem upperMatrix_transpose {K : Type*} (v : Upper3 → K) :
    (upperMatrix v).transpose = upperMatrix v := by
  funext i j
  change upperMatrix v j i = upperMatrix v i j
  by_cases hij : i ≤ j
  · by_cases hji : j ≤ i
    · have heq := le_antisymm hij hji
      subst j
      rfl
    · simp only [upperMatrix, dite_eq_right hji, dite_eq_left hij]
  · have hji : j ≤ i := le_of_not_ge hij
    simp only [upperMatrix, dite_eq_left hji, dite_eq_right hij]

/-- The six-entry coordinate equivalence, preserving the actual matrix carrier. -/
def symmetric3Coordinates (K : Type*) [Field K] : Symmetric3 K ≃ₗ[K] (Upper3 → K) where
  toFun X ij := X.val ij.val.1 ij.val.2
  invFun v := ⟨upperMatrix v, upperMatrix_transpose v⟩
  left_inv X := by
    apply Subtype.ext
    funext i j
    change upperMatrix (fun ij : Upper3 => X.val ij.val.1 ij.val.2) i j = X.val i j
    by_cases hij : i ≤ j
    · simp only [upperMatrix, dite_eq_left hij]
    · simp only [upperMatrix, dite_eq_right hij]
      exact congrFun (congrFun X.property i) j
  right_inv v := by
    funext ij
    exact dite_eq_left ij.property
  map_add' X Y := rfl
  map_smul' c X := rfl

@[simp] theorem finrank_symmetric3 (K : Type*) [Field K] :
    Module.finrank K (Symmetric3 K) = 6 := by
  rw [(symmetric3Coordinates K).finrank_eq, Module.finrank_pi]
  simp

end M9
