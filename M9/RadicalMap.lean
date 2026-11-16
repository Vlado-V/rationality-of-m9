module

public import M9.RadicalFiber
public import Mathlib.LinearAlgebra.Matrix.Adjugate
public import Mathlib.LinearAlgebra.Matrix.Rank
public import Mathlib.LinearAlgebra.LinearIndependent.Defs
public import Mathlib.Tactic

/-!
# Polynomial kernel charts for the actual radical of an odd-dimensional frame

The vectors are actual adjugate columns of the Gram matrix, mapped through the
actual frame. They are not definitions of the desired radical: membership and
line equality are proved against `RadicalFiber.radical`.
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace M9.RadicalMap

open Module Matrix
open scoped BigOperators

section OddAdjugate

variable {R : Type*} [CommRing R] [IsDomain R] [CharZero R]

/-- An actual odd skew matrix has zero determinant. -/
theorem det_nine_eq_zero (M : Matrix (Fin 9) (Fin 9) R) (hM : M.transpose = -M) : M.det = 0 := by
  have h : M.det = -M.det := by
    calc
      M.det = M.transpose.det := (Matrix.det_transpose M).symm
      _ = (-M).det := congrArg Matrix.det hM
      _ = -M.det := by rw [Matrix.det_neg]; norm_num
  have hs : M.det + M.det = 0 := by
    nth_rw 1 [h]
    exact neg_add_cancel _
  have htwo : (2 : R) * M.det = 0 := by simpa only [two_mul] using hs
  exact (mul_eq_zero.mp htwo).resolve_left two_ne_zero

/-- The column is literally polynomial in the entries of the given matrix. -/
def kernelVector (M : Matrix (Fin 9) (Fin 9) R) (j : Fin 9) : Fin 9 → R :=
  fun i => M.adjugate i j

/-- The adjugate identity proves the polynomial kernel equation. -/
theorem mulVec_kernelVector (M : Matrix (Fin 9) (Fin 9) R) (hM : M.transpose = -M) (j : Fin 9) :
    M *ᵥ kernelVector M j = 0 := by
  have hm : M * M.adjugate = 0 := by rw [Matrix.mul_adjugate,det_nine_eq_zero M hM,zero_smul]
  funext i
  have h := congrArg (fun A : Matrix (Fin 9) (Fin 9) R => A i j) hm
  simpa only [Matrix.mul_apply,Matrix.zero_apply,Matrix.mulVec,dotProduct,kernelVector,
    Pi.zero_apply] using h

omit [IsDomain R] [CharZero R] in
theorem kernelVector_ne_zero (M : Matrix (Fin 9) (Fin 9) R) (i j : Fin 9)
    (hij : M.adjugate i j ≠ 0) : kernelVector M j ≠ 0 := by
  intro hz
  apply hij
  exact congrFun hz i

end OddAdjugate

section Frames

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

/-- The actual linear map specified by the nine frame vectors. -/
def frameMap (u : Fin 9 → V) : (Fin 9 → K) →ₗ[K] V := Fintype.linearCombination K u

/-- The actual nine-plane when the frame is independent. -/
def plane (u : Fin 9 → V) : Submodule K V := LinearMap.range (frameMap u)

/-- The actual restricted form in frame coordinates. -/
def gram (B : LinearMap.BilinForm K V) (u : Fin 9 → V) : Matrix (Fin 9) (Fin 9) K :=
  fun i j => B (u i) (u j)

@[simp] theorem frameVector_mem_plane (u : Fin 9 → V) (i : Fin 9) : u i ∈ plane (K := K) u := by
  refine ⟨Pi.single i 1,?_⟩
  simp [frameMap]

theorem gram_transpose (B : LinearMap.BilinForm K V) (hB : B.IsAlt) (u : Fin 9 → V) :
    (gram B u).transpose = -gram B u := by
  ext i j
  exact (hB.neg_eq (u i) (u j)).symm

@[simp] theorem gram_mulVec (B : LinearMap.BilinForm K V) (u : Fin 9 → V) (x : Fin 9 → K) :
    gram B u *ᵥ x = fun i => B (u i) (frameMap u x) := by
  funext i
  simp [gram,frameMap,Fintype.linearCombination_apply,Matrix.mulVec,dotProduct,mul_comm]

theorem form_frame_left (B : LinearMap.BilinForm K V) (u : Fin 9 → V) (x : Fin 9 → K) (y : V) :
    B (frameMap u x) y = ∑ i, x i * B (u i) y := by
  simp [frameMap,Fintype.linearCombination_apply,smul_eq_mul]

/-- Kernel coordinates describe membership in the actual ambient radical. -/
theorem frame_mem_radical_iff (B : LinearMap.BilinForm K V) (hB : B.IsAlt)
    (u : Fin 9 → V) (x : Fin 9 → K) :
    frameMap u x ∈ RadicalFiber.radical B (plane u) ↔
      x ∈ LinearMap.ker (gram B u).mulVecLin := by
  constructor
  · intro hx
    change gram B u *ᵥ x = 0
    rw [gram_mulVec]
    funext i
    exact hB.isRefl _ _
      (((RadicalFiber.mem_radical_iff B hB.isRefl (plane u) _).mp hx).2
        (u i) (frameVector_mem_plane u i))
  · intro hx
    change gram B u *ᵥ x = 0 at hx
    have hzero (i : Fin 9) : B (u i) (frameMap u x) = 0 := by
      have h := congrFun hx i
      simpa only [gram_mulVec,Pi.zero_apply] using h
    apply (RadicalFiber.mem_radical_iff B hB.isRefl (plane u) _).mpr
    refine ⟨⟨x,rfl⟩,?_⟩
    intro y hy
    obtain ⟨z,rfl⟩ := hy
    apply hB.isRefl
    rw [form_frame_left]
    simp only [hzero,mul_zero,Finset.sum_const_zero]

/-- The whole intrinsic radical is the image of the actual Gram kernel. -/
theorem map_kernel_eq_radical (B : LinearMap.BilinForm K V) (hB : B.IsAlt) (u : Fin 9 → V) :
    (LinearMap.ker (gram B u).mulVecLin).map (frameMap u) = RadicalFiber.radical B (plane u) := by
  apply le_antisymm
  · rintro y ⟨x,hx,rfl⟩
    exact (frame_mem_radical_iff B hB u x).mpr hx
  · intro y hy
    obtain ⟨x,hx⟩ := hy.1
    refine ⟨x,?_,hx⟩
    exact (frame_mem_radical_iff B hB u x).mp (hx.symm ▸ hy)

/-- An actual independent frame gives an actual nine-dimensional subspace. -/
theorem finrank_plane (u : Fin 9 → V) (hu : LinearIndependent K u) :
    finrank K (plane (K := K) u) = 9 := by
  simpa only [plane,frameMap,Module.finrank_pi,Fintype.card_fin] using
    LinearMap.finrank_range_of_inj hu.fintypeLinearCombination_injective

end Frames

section RadicalColumns

variable {K V : Type*} [Field K] [CharZero K] [AddCommGroup V] [Module K V]

/-- A polynomial actual ambient radical vector on a cofactor chart. -/
def radicalVector (B : LinearMap.BilinForm K V) (u : Fin 9 → V) (j : Fin 9) : V :=
  frameMap u (kernelVector (gram B u) j)

theorem radicalVector_mem (B : LinearMap.BilinForm K V) (hB : B.IsAlt)
    (u : Fin 9 → V) (j : Fin 9) : radicalVector B u j ∈ RadicalFiber.radical B (plane u) := by
  apply (frame_mem_radical_iff B hB u _).mpr
  exact mulVec_kernelVector (gram B u) (gram_transpose B hB u) j

omit [CharZero K] in
theorem radicalVector_ne_zero (B : LinearMap.BilinForm K V) (u : Fin 9 → V)
    (hu : LinearIndependent K u) (i j : Fin 9) (hij : (gram B u).adjugate i j ≠ 0) :
    radicalVector B u j ≠ 0 := by
  intro hz
  apply kernelVector_ne_zero (gram B u) i j hij
  apply hu.fintypeLinearCombination_injective
  simpa only [radicalVector,frameMap,map_zero] using hz

omit [CharZero K] in
/-- On the rank-eight locus the actual Gram kernel has dimension one. -/
theorem finrank_kernel_of_rank_eight (B : LinearMap.BilinForm K V) (u : Fin 9 → V)
    (hr : (gram B u).rank = 8) : finrank K (LinearMap.ker (gram B u).mulVecLin) = 1 := by
  have h := (gram B u).mulVecLin.finrank_range_add_finrank_ker
  change (gram B u).rank + finrank K (LinearMap.ker (gram B u).mulVecLin) =
    finrank K (Fin 9 → K) at h
  simp only [Module.finrank_pi, Fintype.card_fin, hr] at h
  omega

/-- A nonzero actual cofactor column spans the whole rank-eight kernel. -/
theorem kernel_eq_span_kernelVector (B : LinearMap.BilinForm K V) (hB : B.IsAlt)
    (u : Fin 9 → V) (hr : (gram B u).rank = 8) (i j : Fin 9)
    (hij : (gram B u).adjugate i j ≠ 0) :
    LinearMap.ker (gram B u).mulVecLin = K ∙ kernelVector (gram B u) j := by
  have hle : K ∙ kernelVector (gram B u) j ≤ LinearMap.ker (gram B u).mulVecLin :=
    (Submodule.span_singleton_le_iff_mem _ _).mpr
      (mulVec_kernelVector (gram B u) (gram_transpose B hB u) j)
  apply Eq.symm
  apply Submodule.eq_of_le_of_finrank_eq hle
  rw [finrank_span_singleton (kernelVector_ne_zero (gram B u) i j hij),
    finrank_kernel_of_rank_eight B u hr]

/-- On each nonzero cofactor chart, the line is proved equal to the intrinsic radical. -/
theorem radical_eq_span_radicalVector (B : LinearMap.BilinForm K V) (hB : B.IsAlt)
    (u : Fin 9 → V) (hr : (gram B u).rank = 8) (i j : Fin 9)
    (hij : (gram B u).adjugate i j ≠ 0) :
    RadicalFiber.radical B (plane u) = K ∙ radicalVector B u j := by
  rw [← map_kernel_eq_radical B hB u,kernel_eq_span_kernelVector B hB u hr i j hij,
    Submodule.map_span,Set.image_singleton]
  rfl

end RadicalColumns

end M9.RadicalMap
