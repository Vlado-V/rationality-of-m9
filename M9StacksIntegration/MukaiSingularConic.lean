module

public import M9StacksIntegration.MukaiConormalPencil
public import Mathlib.LinearAlgebra.QuadraticForm.Basic
public import Mathlib.LinearAlgebra.Matrix.BilinearForm

/-!
# The actual ternary discriminant is the product-of-two-lines locus

The singular ternary form is diagonalized by the proved orthogonal-basis
theorem. Its actual determinant forces one diagonal coefficient to
vanish; algebraic closure factors the remaining binary form. Thus no
factorization or Schubert-image equality is a premise.
-/

@[expose] public noncomputable section

set_option maxHeartbeats 1600000

open Matrix Module
open scoped BigOperators

namespace M9Native.MukaiSingularConic

variable {K : Type*} [Field K] [IsAlgClosed K]

private theorem binary_factor (a b : K) :
    ∃ u v : K, ∀ x y : K, a*x^2+b*y^2 = (u*x+v*y)*(u*x-v*y) := by
  obtain ⟨u, hu⟩ := IsAlgClosed.exists_pow_nat_eq a (n := 2) (by decide)
  obtain ⟨v, hv⟩ := IsAlgClosed.exists_pow_nat_eq (-b) (n := 2) (by decide)
  have hb : b = -v^2 := by
    simpa only [neg_neg] using (congrArg (fun z : K => -z) hv).symm
  refine ⟨u, v, fun x y => ?_⟩
  rw [← hu, hb]
  ring

/-- The actual degenerate weighted ternary quadratic factors into two
actual linear forms; the zero polynomial is included. -/
theorem weighted_ternary_factor (w : Fin 3 → K) (hw : ∏ i, w i = 0) :
    ∃ l m : (Fin 3 → K) →ₗ[K] K,
      ∀ x, (∑ i, w i * (x i)^2) = l x * m x := by
  obtain ⟨j, _, hj⟩ := (Finset.prod_eq_zero_iff).mp hw
  fin_cases j
  · change w 0 = 0 at hj
    obtain ⟨u, v, huv⟩ := binary_factor (w 1) (w 2)
    refine ⟨u • LinearMap.proj 1 + v • LinearMap.proj 2,
      u • LinearMap.proj 1 - v • LinearMap.proj 2, ?_⟩
    intro x
    simpa [Fin.sum_univ_succ, hj] using huv (x 1) (x 2)
  · change w 1 = 0 at hj
    obtain ⟨u, v, huv⟩ := binary_factor (w 0) (w 2)
    refine ⟨u • LinearMap.proj 0 + v • LinearMap.proj 2,
      u • LinearMap.proj 0 - v • LinearMap.proj 2, ?_⟩
    intro x
    simpa [Fin.sum_univ_succ, hj] using huv (x 0) (x 2)
  · change w 2 = 0 at hj
    obtain ⟨u, v, huv⟩ := binary_factor (w 0) (w 1)
    refine ⟨u • LinearMap.proj 0 + v • LinearMap.proj 1,
      u • LinearMap.proj 0 - v • LinearMap.proj 1, ?_⟩
    intro x
    simpa [Fin.sum_univ_succ, hj] using huv (x 0) (x 1)

variable [CharZero K]

/-- An actual singular symmetric ternary matrix defines a quadratic form
which factors into actual linear forms. -/
theorem exists_linear_factors (S : Matrix (Fin 3) (Fin 3) K)
    (hS : S.IsSymm) (hdet : S.det = 0) :
    ∃ l m : (Fin 3 → K) →ₗ[K] K, ∀ x, S.toBilin' x x = l x * m x := by
  let B := S.toBilin'
  let : Invertible (2 : K) := invertibleOfNonzero (by norm_num)
  have hB : B.IsSymm := Matrix.isSymm_toBilin'_iff_isSymm.mpr hS
  obtain ⟨b, hb⟩ : ∃ b : Basis (Fin 3) K (Fin 3 → K), B.IsOrthoᵢ b := by
    have hr : Module.finrank K (Fin 3 → K) = 3 := by simp
    have h := LinearMap.BilinForm.exists_orthogonal_basis
      (K := K) (V := Fin 3 → K) (B := B) (LinearMap.BilinForm.isSymm_iff.mp hB)
    rw [hr] at h
    exact h
  let w : Fin 3 → K := fun i => B (b i) (b i)
  have hm : B.toMatrix b = Matrix.diagonal w := by
    ext i j
    rw [LinearMap.BilinForm.toMatrix_apply]
    by_cases hij : i = j
    · subst j
      simp [w]
    · simp [hij, hb hij]
  have hcongr : ((Pi.basisFun K (Fin 3)).toMatrix b).transpose * S *
      (Pi.basisFun K (Fin 3)).toMatrix b = B.toMatrix b := by
    simpa only [B, LinearMap.BilinForm.toMatrix_basisFun,
      LinearMap.BilinForm.toMatrix'_toBilin'] using
      LinearMap.BilinForm.toMatrix_mul_basis_toMatrix (Pi.basisFun K (Fin 3)) b B
  have hw : ∏ i, w i = 0 := by
    calc
      _ = (Matrix.diagonal w).det := Matrix.det_diagonal.symm
      _ = (B.toMatrix b).det := congrArg Matrix.det hm.symm
      _ = (((Pi.basisFun K (Fin 3)).toMatrix b).transpose * S *
          (Pi.basisFun K (Fin 3)).toMatrix b).det := congrArg Matrix.det hcongr.symm
      _ = 0 := by simp [Matrix.det_mul, hdet]
  have hq (x : Fin 3 → K) : B x x = ∑ i, w i * (b.coord i x)^2 := by
    rw [B.apply_eq_dotProduct_toMatrix_mulVec b, hm]
    simp only [dotProduct, Basis.coord_apply]
    apply Finset.sum_congr rfl
    intro i _
    rw [Matrix.mulVec_diagonal]
    ring
  obtain ⟨l, m, hlm⟩ := weighted_ternary_factor w hw
  refine ⟨l.comp b.equivFun.toLinearMap, m.comp b.equivFun.toLinearMap, ?_⟩
  intro x
  exact (hq x).trans (hlm (b.equivFun x))

/-- Polarization identifies the ACTUAL matrix as a symmetrized rank-one
product, with the exact factor of two derived from the actual pairing. -/
theorem exists_symmetrized_product (S : Matrix (Fin 3) (Fin 3) K)
    (hS : S.IsSymm) (hdet : S.det = 0) :
    ∃ a b : Fin 3 → K, S = Matrix.vecMulVec a b + Matrix.vecMulVec b a := by
  obtain ⟨l, m, hlm⟩ := exists_linear_factors S hS hdet
  let e : Fin 3 → (Fin 3 → K) := fun i => Pi.single i 1
  refine ⟨fun i => l (e i), fun i => m (e i) / 2, ?_⟩
  ext i j
  have hi := hlm (e i)
  have hj := hlm (e j)
  have hij := hlm (e i + e j)
  have hsym : S j i = S i j := hS.apply i j
  simp only [map_add, LinearMap.add_apply] at hij
  simp only [e, Matrix.toBilin'_single] at hi hj hij
  have hc : 2 * S i j = l (e i) * m (e j) + l (e j) * m (e i) := by
    dsimp only [e]
    rw [hsym] at hij
    linear_combination hij - hi - hj
  change S i j = l (e i) * (m (e j) / 2) + (m (e i) / 2) * l (e j)
  field_simp
  linear_combination hc

end M9Native.MukaiSingularConic
