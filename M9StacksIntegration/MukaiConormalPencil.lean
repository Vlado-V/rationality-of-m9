module

public import M9StacksIntegration.LagrangianGrassmannian
public import Mathlib.LinearAlgebra.Eigenspace.Triangularizable
public import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv

/-!
# Linear spaces avoiding the actual ternary discriminant cone

Over an algebraically closed field a pencil through an invertible matrix
contains a singular matrix. Consequently a linear space whose every
nonzero member has invertible ternary-matrix projection has dimension at
most one. This is the linear-algebra step used after identifying Mukai's
projected Schubert cone with the actual determinant-zero locus.

No identification with a native conormal sheaf is assumed or asserted in
this helper. That geometric identification is a separate construction.
-/

@[expose] public noncomputable section

set_option maxHeartbeats 800000

open Matrix Module
open scoped BigOperators

namespace M9Native.MukaiConormalPencil

variable {K : Type*} [Field K] [IsAlgClosed K]

/-- The singular member is derived from an actual eigenvector of the
matrix pencil; it is not a supplied discriminant-root assumption. -/
theorem exists_singular_pencil (A B : Matrix (Fin 3) (Fin 3) K)
    (hB : B.det ≠ 0) : ∃ t : K, (A - t • B).det = 0 := by
  let C := B⁻¹ * A
  obtain ⟨t, ht⟩ := Module.End.exists_eigenvalue (Matrix.toLin' C)
  obtain ⟨v, hv⟩ := ht.exists_hasEigenvector
  have he : C *ᵥ v = t • v := hv.apply_eq_smul
  have hA : A *ᵥ v = t • (B *ᵥ v) := by
    calc
      A *ᵥ v = (B * C) *ᵥ v := by
        change A *ᵥ v = (B * (B⁻¹ * A)) *ᵥ v
        rw [Matrix.mul_nonsing_inv_cancel_left B A (isUnit_iff_ne_zero.mpr hB)]
      _ = B *ᵥ (C *ᵥ v) := (Matrix.mulVec_mulVec v B C).symm
      _ = t • (B *ᵥ v) := by rw [he, Matrix.mulVec_smul]
  refine ⟨t, (Matrix.exists_mulVec_eq_zero_iff).mp ?_⟩
  refine ⟨v, hv.2, ?_⟩
  rw [Matrix.sub_mulVec, Matrix.smul_mulVec, hA, sub_self]

variable {V : Type*} [AddCommGroup V] [Module K V]

/-- An actual linear subspace avoiding the determinant-zero cone has
dimension at most one. The projected matrices need not be symmetric. -/
theorem finrank_le_one_of_det_ne_zero (T : Submodule K V)
    (π : V →ₗ[K] Matrix (Fin 3) (Fin 3) K)
    (hT : ∀ v ∈ T, v ≠ 0 → (π v).det ≠ 0) : Module.finrank K T ≤ 1 := by
  by_cases hzero : T = ⊥
  · rw [hzero, finrank_bot]
    omega
  obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hzero
  have hspan : T ≤ Submodule.span K {v} := by
    intro w hw
    obtain ⟨t, ht⟩ := exists_singular_pencil (π w) (π v) (hT v hv hv0)
    have hz : w - t • v = 0 := by
      by_contra hne
      apply hT (w - t • v) (T.sub_mem hw (T.smul_mem t hv)) hne
      simpa only [map_sub, map_smul] using ht
    rw [sub_eq_zero] at hz
    rw [hz]
    exact Submodule.smul_mem _ t (Submodule.subset_span (by simp))
  calc
    Module.finrank K T ≤ Module.finrank K (Submodule.span K {v}) :=
      Submodule.finrank_mono hspan
    _ = 1 := finrank_span_singleton hv0

/-- The actual split rank-seven local model of Mukai's conormal
extension. The second summand is the literal symmetric-matrix carrier. -/
abbrev ConormalCoordinates (K : Type*) [Field K] := K × LagrangianField.Symmetric3 K

def matrixProjection : ConormalCoordinates K →ₗ[K] Matrix (Fin 3) (Fin 3) K :=
  (LagrangianField.Symmetric3 K).subtype.comp (LinearMap.snd K K _)

def discriminant (v : ConormalCoordinates K) : K := (matrixProjection v).det

theorem finrank_conormalCoordinates : Module.finrank K (ConormalCoordinates K) = 7 := by
  simp [ConormalCoordinates, Module.finrank_prod]

/-- The nonempty linear intersection is a line once the ACTUAL cubic
cone has been excluded. No line is provided to the theorem. -/
theorem finrank_eq_one_of_avoids_discriminant (T : Submodule K (ConormalCoordinates K))
    (hT : T ≠ ⊥) (havoid : ∀ v ∈ T, v ≠ 0 → discriminant v ≠ 0) :
    Module.finrank K T = 1 := by
  have hle := finrank_le_one_of_det_ne_zero T matrixProjection havoid
  obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hT
  have hspan : Submodule.span K {v} ≤ T :=
    Submodule.span_le.mpr (by simpa using hv)
  have hpos := Submodule.finrank_mono hspan
  rw [finrank_span_singleton hv0] at hpos
  omega

end M9Native.MukaiConormalPencil
