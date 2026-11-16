module

public import Mathlib.LinearAlgebra.Transvection.Basic
public import Mathlib.LinearAlgebra.BilinearForm.Properties
public meta import Mathlib.Tactic.Ring
public meta import Mathlib.Tactic.Abel

/-!
# Genuine alternating transvections and nonzero-vector transitivity

Mathlib constructs the actual linear equivalence x ↦ x+f(x)u when
f(u)=0. For an actual alternating form, f=c B(u,-) has that property.
The equivalence preserves B, and one or two such genuine transvections
send any nonzero vector to any other for a nondegenerate alternating
form over any field, including characteristic two.
-/

@[expose] public noncomputable section

universe u v

namespace M9Native.AlternatingTransvections

variable {K : Type u} [Field K] {V : Type v} [AddCommGroup V] [Module K V]
  (B : LinearMap.BilinForm K V) (hAlt : B.IsAlt)

/-- The actual Mathlib transvection, with its constructed inverse. -/
def transvection (u : V) (c : K) : V ≃ₗ[K] V :=
  LinearEquiv.transvection (f := c • B u) (v := u) (by simp [hAlt u])

theorem transvection_apply (u x : V) (c : K) :
    transvection B hAlt u c x = x + (c * B u x) • u := rfl

/-- Its actual inverse is the transvection with negative parameter. -/
theorem transvection_symm (u : V) (c : K) :
    (transvection B hAlt u c).symm = transvection B hAlt u (-c) := by
  ext x
  change x + (c * B u x) • (-u) = x + ((-c) * B u x) • u
  rw [smul_neg, neg_mul, neg_smul]

/-- The actual linear equivalence preserves the actual alternating
form; no normalizer or preservation premise is supplied. -/
theorem transvection_preserves (u x y : V) (c : K) :
    B (transvection B hAlt u c x) (transvection B hAlt u c y) = B x y := by
  rw [transvection_apply, transvection_apply]
  simp only [map_add, LinearMap.add_apply, map_smul, LinearMap.smul_apply,
    smul_eq_mul, hAlt u, mul_zero, add_zero]
  rw [← hAlt.neg_eq u x]
  ring

/-- A nonzero cross pairing gives a single genuine transvection
sending the source to the target. -/
theorem transvection_send (v w : V) (h : B w v ≠ 0) :
    transvection B hAlt (w-v) (B w v)⁻¹ v = w := by
  rw [transvection_apply]
  have hp : B (w-v) v = B w v := by
    simp only [map_sub, LinearMap.sub_apply, hAlt v, sub_zero]
  rw [hp, inv_mul_cancel₀ h, one_smul]
  abel

/-- Two nonzero vectors have an actual intermediate vector with both
required cross pairings nonzero. This works even over the two-element
field: two nondegeneracy witnesses or their sum suffice. -/
theorem exists_intermediate (hND : B.Nondegenerate) (v w : V)
    (hv : v ≠ 0) (hw : w ≠ 0) :
    ∃ z : V, B z v ≠ 0 ∧ B w z ≠ 0 := by
  have hwa : ∃ a : V, B w a ≠ 0 := by
    by_contra! h
    exact hw (hND.1 w h)
  have hbv : ∃ b : V, B b v ≠ 0 := by
    by_contra! h
    exact hv (hND.2 v h)
  obtain ⟨a, ha⟩ := hwa
  obtain ⟨b, hb⟩ := hbv
  by_cases hav : B a v = 0
  · by_cases hwb : B w b = 0
    · refine ⟨a+b, ?_, ?_⟩
      · simpa only [map_add, LinearMap.add_apply, hav, zero_add] using hb
      · simpa only [map_add, hwb, add_zero] using ha
    · exact ⟨b, hb, hwb⟩
  · exact ⟨a, hav, ha⟩

include hAlt

/-- Genuine isometries of an alternating nondegenerate form act
transitively on its actual nonzero vectors, over every field. -/
theorem exists_preservingEquiv (hND : B.Nondegenerate) (v w : V)
    (hv : v ≠ 0) (hw : w ≠ 0) :
    ∃ e : V ≃ₗ[K] V, e v = w ∧ ∀ x y, B (e x) (e y) = B x y := by
  by_cases hpair : B w v = 0
  · obtain ⟨z, hzv, hwz⟩ := exists_intermediate B hND v w hv hw
    let e₁ := transvection B hAlt (z-v) (B z v)⁻¹
    let e₂ := transvection B hAlt (w-z) (B w z)⁻¹
    refine ⟨e₁.trans e₂, ?_, ?_⟩
    · exact (congrArg e₂ (transvection_send B hAlt v z hzv)).trans
        (transvection_send B hAlt z w hwz)
    · intro x y
      change B (e₂ (e₁ x)) (e₂ (e₁ y)) = B x y
      rw [transvection_preserves, transvection_preserves]
  · exact ⟨transvection B hAlt (w-v) (B w v)⁻¹,
      transvection_send B hAlt v w hpair,
      fun x y => transvection_preserves B hAlt (w-v) x y (B w v)⁻¹⟩

end M9Native.AlternatingTransvections
