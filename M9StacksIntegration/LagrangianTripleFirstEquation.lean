module

public import M9StacksIntegration.PrimitiveDecomposableNonzero
public import M9StacksIntegration.LagrangianPrimitiveIndependence
public import M9StacksIntegration.LagrangianTripleDeterminantSection
public import M9StacksIntegration.LagrangianModelRestriction
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs

/-!
# An independent determinant-zero triple as the first actual equation

The actual primitive coefficients are the frozen original coefficients
of the independent triple. Their nonvanishing follows from the actual
Plücker quadratic proof. Genuine global independence of the original
fourteen LG sections makes their actual determinant section nonzero.
On an actual smooth integral five-section model, determinant vanishing
produces a nonzero original row relation. An explicit invertible change
of the five equations puts that relation first.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Module Matrix
open scoped BigOperators

universe u

namespace M9Native.LagrangianTripleFirstEquation

variable (K : Type u) [Field K]

/-- A nonzero five-vector is the literal first row of a genuinely
invertible five-by-five matrix. -/
theorem exists_firstRow (a : Fin 5 → K) (ha : a ≠ 0) :
    ∃ A : GL (Fin 5) K, A.val 0 = a := by
  classical
  obtain ⟨j, hj⟩ := Function.ne_iff.mp ha
  have hj' : a j ≠ 0 := hj
  let B : Matrix (Fin 5) (Fin 5) K := (1 : Matrix (Fin 5) (Fin 5) K).updateRow j a
  have hsum : (∑ k : Fin 5, a k • (1 : Matrix (Fin 5) (Fin 5) K) k) = a := by
    funext l
    simp [Finset.sum_apply, Matrix.one_apply, Pi.smul_apply]
  have hB : B.det = a j := by
    simpa only [hsum, Matrix.det_one, smul_eq_mul, mul_one] using
      (Matrix.det_updateRow_sum (1 : Matrix (Fin 5) (Fin 5) K) j a)
  let σ : Equiv.Perm (Fin 5) := Equiv.swap 0 j
  let C : Matrix (Fin 5) (Fin 5) K := B.submatrix σ id
  have hC : IsUnit C.det := by
    change IsUnit (B.submatrix σ id).det
    rw [Matrix.det_permute, hB]
    exact ((Units.isUnit (Equiv.Perm.sign σ)).map (Int.castRingHom K)).mul
      (isUnit_iff_ne_zero.mpr hj')
  refine ⟨Matrix.GeneralLinearGroup.mk'' C hC, ?_⟩
  change C 0 = a
  funext l
  simp [C, σ, B, Matrix.updateRow]

/-- Left multiplication by a genuine invertible equation change
preserves the actual surjectivity of the five-row quotient map. -/
theorem mul_surjective (A : GL (Fin 5) K) (M : Matrix (Fin 5) (Fin 14) K)
    (hM : Function.Surjective M.mulVec) : Function.Surjective (A.val * M).mulVec := by
  intro y
  obtain ⟨x, hx⟩ := hM ((A⁻¹).val *ᵥ y)
  refine ⟨x, ?_⟩
  have hA : A.val * (A⁻¹).val = 1 := congrArg Units.val (mul_inv_cancel A)
  calc
    (A.val * M) *ᵥ x = A.val *ᵥ (M *ᵥ x) := (Matrix.mulVec_mulVec x A.val M).symm
    _ = A.val *ᵥ ((A⁻¹).val *ᵥ y) := congrArg (fun z => A.val *ᵥ z) hx
    _ = y := by rw [Matrix.mulVec_mulVec, hA, Matrix.one_mulVec]

/-- The first original row after equation change is exactly its
original linear combination, retaining all fourteen coefficients. -/
theorem firstRow_mul (A : GL (Fin 5) K) (M : Matrix (Fin 5) (Fin 14) K) :
    (A.val * M) 0 = Matrix.vecMul (A.val 0) M := by
  funext j
  rfl

variable [CharZero K]

/-- An independent original triple defines a nonzero actual global
determinant section on the original native LG. -/
theorem determinantSection_ne_zero (s : Fin 3 → (Fin 6 → K))
    (hs : LinearIndependent K s) :
    LagrangianHyperplaneCoordinates.determinantSection K
      (PrimitiveDecomposableNonzero.coefficients K s) ≠ 0 := by
  intro hz
  exact PrimitiveDecomposableNonzero.coefficients_ne_zero K s hs
    (LagrangianPrimitiveIndependence.coefficients_eq_zero_of_determinantSection K _ hz)

open LagrangianOrderedFibre

variable [IsAlgClosed K] (M : Matrix (Fin 5) (Fin 14) K)
  (hM : Function.Surjective M.mulVec)
  [IsIntegral (model K M hM)]
  [SmoothOfRelativeDimension 1 (modelProjection K M hM)]

/-- Actual determinant vanishing gives a nonzero actual relation in
the five original equations, with a nonzero original LG section. -/
theorem exists_nonzero_relation (s : Fin 3 → (Fin 6 → K))
    (hs : LinearIndependent K s)
    (hdet : LagrangianTripleDeterminantSection.determinantValue K
      (modelProjection K M hM) (modelInclusion K M hM) s = 0) :
    ∃ a : Fin 5 → K, a ≠ 0 ∧
      PrimitiveDecomposableNonzero.coefficients K s = Matrix.vecMul a M ∧
      LagrangianHyperplaneCoordinates.determinantSection K
        (Matrix.vecMul a M) ≠ 0 := by
  have hc := (LagrangianTripleDeterminantSection.determinantValue_eq_zero_iff K
    (modelProjection K M hM) (modelInclusion K M hM) rfl s).mp hdet
  obtain ⟨a, ha, hca⟩ := LagrangianModelRestriction.exists_nonzero_vecMul_of_restriction_eq_zero
    K M hM (PrimitiveDecomposableNonzero.coefficients K s) hc
      (PrimitiveDecomposableNonzero.coefficients_ne_zero K s hs)
  exact ⟨a, ha, hca, hca ▸ determinantSection_ne_zero K s hs⟩

/-- The same original model equations can be changed by a genuine GL5
matrix so the independent determinant-zero triple is their first row.
Both its actual nonzero LG section and the full five-row surjectivity
are derived, rather than supplied. -/
theorem exists_first_equation (s : Fin 3 → (Fin 6 → K))
    (hs : LinearIndependent K s)
    (hdet : LagrangianTripleDeterminantSection.determinantValue K
      (modelProjection K M hM) (modelInclusion K M hM) s = 0) :
    ∃ A : GL (Fin 5) K, Function.Surjective (A.val * M).mulVec ∧
      (A.val * M) 0 = PrimitiveDecomposableNonzero.coefficients K s ∧
      LagrangianHyperplaneCoordinates.determinantSection K ((A.val * M) 0) ≠ 0 := by
  obtain ⟨a, ha, hca, hsection⟩ := exists_nonzero_relation K M hM s hs hdet
  obtain ⟨A, hA⟩ := exists_firstRow K a ha
  have hfirst : (A.val * M) 0 = PrimitiveDecomposableNonzero.coefficients K s := by
    rw [firstRow_mul, hA]
    exact hca.symm
  exact ⟨A, mul_surjective K A M hM, hfirst,
    hfirst ▸ determinantSection_ne_zero K s hs⟩

end M9Native.LagrangianTripleFirstEquation
