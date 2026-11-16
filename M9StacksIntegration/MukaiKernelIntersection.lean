module

public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-! The exact finite-dimensional intersection estimate used after the
actual value-and-curve-jet comparison. It does not assume or construct a
geometric conormal identification. -/

@[expose] public section

open Module

namespace M9Native.MukaiKernelIntersection

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V]

theorem inf_ne_bot (A B J : Submodule K V)
    (hAJ : A ≤ J) (hBJ : B ≤ J)
    (hA : 6 ≤ finrank K A) (hB : finrank K B = 7) (hJ : finrank K J ≤ 12) :
    A ⊓ B ≠ ⊥ := by
  intro hz
  have hsum := Submodule.finrank_sup_add_finrank_inf_eq A B
  have hle := Submodule.finrank_mono (sup_le hAJ hBJ)
  rw [hz, finrank_bot, add_zero, hB] at hsum
  omega

/-- The actual restriction estimate after the value-and-curve-jet map
has been proved onto. Non-surjectivity of the original fourteen-to-nine
evaluation is converted to its real kernel dimension. -/
theorem restriction_rank_le_six {H : Type*} [AddCommGroup H] [Module K H]
    [FiniteDimensional K H] (D : V →ₗ[K] H) (J : V →ₗ[K] K × K)
    (hV : finrank K V = 14) (hH : finrank K H = 9)
    (hD : ¬ Function.Surjective D) (hJ : Function.Surjective J)
    (A : Submodule K V) (hA : finrank K A = 7)
    (hAJ : A ≤ LinearMap.ker J) (hDJ : LinearMap.ker D ≤ LinearMap.ker J) :
    finrank K (LinearMap.range (D.comp A.subtype)) ≤ 6 := by
  classical
  have hproper : LinearMap.range D ≠ ⊤ := by
    intro h
    exact hD (LinearMap.range_eq_top.mp h)
  have hrange : finrank K (LinearMap.range D) < 9 := by
    simpa only [hH] using Submodule.finrank_lt hproper
  have hker : 6 ≤ finrank K (LinearMap.ker D) := by
    have h := D.finrank_range_add_finrank_ker
    rw [hV] at h
    omega
  have hJrange : finrank K (LinearMap.range J) = 2 := by
    rw [LinearMap.range_eq_top.mpr hJ, finrank_top]
    simp [Module.finrank_prod]
  have hJker : finrank K (LinearMap.ker J) ≤ 12 := by
    have h := J.finrank_range_add_finrank_ker
    rw [hV, hJrange] at h
    omega
  have hinter := inf_ne_bot (LinearMap.ker D) A (LinearMap.ker J) hDJ hAJ hker hA hJker
  obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hinter
  let va : A := ⟨v, hv.2⟩
  have hva : va ≠ 0 := by
    intro h
    exact hv0 (congrArg Subtype.val h)
  have hmem : va ∈ LinearMap.ker (D.comp A.subtype) := hv.1
  have hspan : Submodule.span K {va} ≤ LinearMap.ker (D.comp A.subtype) :=
    Submodule.span_le.mpr (by simpa using hmem)
  have hpos := Submodule.finrank_mono hspan
  rw [finrank_span_singleton hva] at hpos
  have hdim := (D.comp A.subtype).finrank_range_add_finrank_ker
  rw [hA] at hdim
  omega

end M9Native.MukaiKernelIntersection
