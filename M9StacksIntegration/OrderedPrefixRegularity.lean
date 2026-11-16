module

public import StacksFrontier.RingTheory.RegularLocalRing.RegularParameterFactorization

/-!
# Regularity of the actual ordered prefixes at a transverse final intersection

A regular quotient of a regular local ring with dimension drop equal to the
number of original equations makes that very ordered list an initial segment
of a regular system of parameters. Thus every actual prefix quotient is regular.
No regularity premise on the prefix quotients is used.
-/

set_option autoImplicit false
@[expose] public noncomputable section

open IsLocalRing
universe u
namespace M9Native.OrderedPrefixRegularity

variable (R : Type u) [CommRing R] [IsRegularLocalRing R]

/-- Every actual ordered prefix of the given equations has a regular quotient
of the expected complementary local dimension. -/
theorem regular_quotients_of_regular_final
    (fs : List R) (hq : IsRegularLocalRing (R ⧸ Ideal.ofList fs))
    (hdim : ringKrullDim (R ⧸ Ideal.ofList fs) + fs.length = ringKrullDim R)
    (i : ℕ) (hi : i ≤ fs.length) :
    IsRegularLocalRing (R ⧸ Ideal.ofList (fs.take i)) ∧
      ringKrullDim (R ⧸ Ideal.ofList (fs.take i)) + i = ringKrullDim R := by
  obtain ⟨ts, hsys, hgen⟩ :=
    IsRegularLocalRing.exists_isSystemOfParameters_append_of_isRegularLocalRing_quotient hq hdim
  have hlen : (fs ++ ts).length = (maximalIdeal R).spanFinrank := by
    have h := IsRegularLocalRing.spanFinrank_maximalIdeal (R := R)
    rw [hsys.2] at h
    exact_mod_cast h.symm
  have hmain :=
    (IsRegularLocalRing.isRegular_and_isRegularLocalRing_quotient_and_isMaximalCohenMacaulay R).1
  have hx := (hmain (fs ++ ts) hgen hlen).2 i (by simp only [List.length_append]; omega)
  rw [List.take_append_of_le_length (l₂ := ts) hi] at hx
  exact hx

/-- The literal six-dimensional ambient/five-equation curve case.  The
quotient's one-dimensional regularity is the actual transverse final geometry. -/
theorem regular_five_prefixes
    (fs : List R) (hlen : fs.length = 5)
    (hq : IsRegularLocalRing (R ⧸ Ideal.ofList fs))
    (hRdim : ringKrullDim R = (6 : WithBot ℕ∞))
    (hQdim : ringKrullDim (R ⧸ Ideal.ofList fs) = (1 : WithBot ℕ∞))
    (i : ℕ) (hi : i ≤ 5) :
    IsRegularLocalRing (R ⧸ Ideal.ofList (fs.take i)) ∧
      ringKrullDim (R ⧸ Ideal.ofList (fs.take i)) + i = (6 : WithBot ℕ∞) := by
  have hd : ringKrullDim (R ⧸ Ideal.ofList fs) + fs.length = ringKrullDim R := by
    rw [hQdim, hRdim, hlen]
    norm_num
  simpa only [hRdim] using regular_quotients_of_regular_final R fs hq hd i (by omega)

end M9Native.OrderedPrefixRegularity
