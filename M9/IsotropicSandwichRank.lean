module

public import Mathlib.LinearAlgebra.Matrix.Rank
public import Mathlib.LinearAlgebra.Matrix.ToLin

/-!
# A rank bound on the support of a degenerate alternating form

For literal matrices with `A B C = 0`, restricting `A` to the actual image of
`B` gives `rank(A B) + rank(B C) ≤ rank(B)`. If `B` is skew and `C = Aᵀ`,
the two product ranks agree. Thus `2 rank(A B) ≤ rank(B)`.

The rank-four case bounds evaluation on the support of a rank-four bivector
by two, without requiring a chosen normal-form basis for that bivector.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace M9.IsotropicSandwichRank

open Matrix Module

variable {K m n p q : Type*} [Field K]
variable [Fintype n] [Fintype p] [Fintype q]

/-- In a matrix complex whose middle factor is `B`, both images fit in the
actual range of `B`, and their ranks sum to at most its dimension. -/
theorem rank_products_add_le_of_triple_eq_zero
    (A : Matrix m n K) (B : Matrix n p K) (C : Matrix p q K)
    (hABC : A * B * C = 0) :
    (A * B).rank + (B * C).rank ≤ B.rank := by
  let R := LinearMap.range B.mulVecLin
  let f : R →ₗ[K] (m → K) := A.mulVecLin.comp R.subtype
  let g : (q → K) →ₗ[K] R := B.mulVecLin.rangeRestrict.comp C.mulVecLin
  have hf : LinearMap.range f = LinearMap.range (A * B).mulVecLin := by
    simp only [f, Matrix.mulVecLin_mul, LinearMap.range_comp, Submodule.range_subtype]
    rfl
  have hg : finrank K (LinearMap.range g) = (B * C).rank := by
    have heq : (B * C).mulVecLin = R.subtype.comp g := by
      rw [Matrix.mulVecLin_mul]
      ext x i
      rfl
    calc
      finrank K (LinearMap.range g) =
          finrank K ((LinearMap.range g).map R.subtype) :=
        (Submodule.finrank_map_subtype_eq R _).symm
      _ = (B * C).rank := by
        rw [Matrix.rank, heq]
        exact congrArg (fun S : Submodule K (n → K) => finrank K S)
          (LinearMap.range_comp g R.subtype).symm
  have hfg : f.comp g = 0 := by
    ext x i
    change A.mulVecLin (B.mulVecLin (C.mulVecLin x)) i = 0
    have hz := congrArg (fun M : Matrix m q K => M.mulVecLin x i) hABC
    simpa only [Matrix.mulVecLin_mul, LinearMap.comp_apply, Matrix.mulVecLin_zero,
      LinearMap.zero_apply, Pi.zero_apply] using hz
  have hle : LinearMap.range g ≤ LinearMap.ker f :=
    LinearMap.range_le_ker_iff.mpr hfg
  have hdim := f.finrank_range_add_finrank_ker
  have hmono := Submodule.finrank_mono hle
  rw [hf, ← Matrix.rank] at hdim
  rw [hg] at hmono
  calc
    (A * B).rank + (B * C).rank ≤ (A * B).rank + finrank K (LinearMap.ker f) :=
      Nat.add_le_add_left hmono _
    _ = finrank K R := hdim
    _ = B.rank := rfl

variable [Fintype m]

/-- Skewness identifies the ranks of the two products around an isotropic
sandwich, so the image of `A B` uses at most half the rank of `B`. -/
theorem two_mul_rank_product_le_of_skew_sandwich_zero
    (A : Matrix m n K) (B : Matrix n n K) (hB : Bᵀ = -B)
    (hA : A * B * Aᵀ = 0) :
    2 * (A * B).rank ≤ B.rank := by
  have hrank : (B * Aᵀ).rank = (A * B).rank := by
    calc
      (B * Aᵀ).rank = (B * Aᵀ)ᵀ.rank := (Matrix.rank_transpose _).symm
      _ = (-(A * B)).rank := by rw [Matrix.transpose_mul, Matrix.transpose_transpose,
        hB, Matrix.mul_neg]
      _ = (A * B).rank := by
        simpa only [neg_one_smul] using Matrix.rank_smul_of_mem_nonZeroDivisors
          (A * B) (mem_nonZeroDivisors_of_ne_zero (neg_ne_zero.mpr (one_ne_zero : (1 : K) ≠ 0)))
  have h := rank_products_add_le_of_triple_eq_zero A B Aᵀ hA
  rw [hrank] at h
  simpa only [two_mul] using h

/-- Evaluation on the support of any actual rank-four skew matrix has rank
at most two when the exterior-evaluation sandwich vanishes. -/
theorem rank_product_le_two_of_skew_rank_four
    (A : Matrix m n K) (B : Matrix n n K) (hB : Bᵀ = -B)
    (hrank : B.rank = 4) (hA : A * B * Aᵀ = 0) :
    (A * B).rank ≤ 2 := by
  have h := two_mul_rank_product_le_of_skew_sandwich_zero A B hB hA
  rw [hrank] at h
  omega

end M9.IsotropicSandwichRank
