module

public import M9StacksIntegration.CurvePowerTraceRadical
public import Mathlib.Data.Finsupp.Multiset
public import Mathlib.LinearAlgebra.Finsupp.LinearCombination
public import Mathlib.Algebra.MvPolynomial.Basic

/-!
# The polynomial trace of a genuine word intersection functional

A polynomial monomial is sent to its coefficient times the intersection
of its multiset of divisor factors. The trace is constructed as an
actual additive map. Permutation invariance identifies products with
concatenated factor words. Annihilating all monomial pairings is then
proved sufficient for membership in the trace radical.
-/

@[expose] public noncomputable section

namespace M9Native.CurvePowerPolynomialTrace

open MvPolynomial CurvePowerTraceRadical

variable {α M : Type*} [AddCommGroup M]

def word (e : α →₀ ℕ) : List α := (Finsupp.toMultiset e).toList

theorem word_zero : word (0 : α →₀ ℕ) = [] := by
  simp [word, Finsupp.toMultiset_zero]

theorem word_single_one (i : α) : word (Finsupp.single i 1) = [i] := by
  simp [word]

theorem word_add_perm (e f : α →₀ ℕ) : (word (e + f)).Perm (word e ++ word f) := by
  apply Multiset.coe_eq_coe.mp
  simp only [word, Finsupp.toMultiset_add, ← Multiset.coe_add, Multiset.coe_toList]

theorem word_length (e : α →₀ ℕ) : (word e).length = e.sum (fun _ n => n) := by
  rw [word, ← Multiset.coe_card, Multiset.coe_toList, Finsupp.card_toMultiset]
  rfl

def trace (F : List α → M) : MvPolynomial α ℤ →+ M :=
  (Finsupp.linearCombination ℤ (fun e => F (word e))).toAddMonoidHom.comp
    AddMonoidAlgebra.coeffAddEquiv.toAddMonoidHom

theorem trace_monomial (F : List α → M) (e : α →₀ ℕ) (c : ℤ) :
    trace F (monomial e c) = c • F (word e) := by
  change Finsupp.linearCombination ℤ (fun e => F (word e)) (Finsupp.single e c) = _
  exact Finsupp.linearCombination_single ℤ c e

theorem trace_monomial_mul_monomial (F : List α → M)
    (hF : ∀ u v : List α, u.Perm v → F u = F v)
    (e f : α →₀ ℕ) (c d : ℤ) :
    trace F (monomial e c * monomial f d) = (c * d) • F (word e ++ word f) := by
  rw [monomial_mul_monomial, trace_monomial, hF _ _ (word_add_perm e f)]

theorem trace_X_mul_monomial (F : List α → M)
    (hF : ∀ u v : List α, u.Perm v → F u = F v)
    (i : α) (e : α →₀ ℕ) (c : ℤ) :
    trace F (X i * monomial e c) = c • F (i :: word e) := by
  change trace F (monomial (Finsupp.single i 1) 1 * monomial e c) = _
  rw [trace_monomial_mul_monomial F hF, word_single_one]
  simp only [one_mul, List.singleton_append]

/-- This converts checked word pairings into genuine numerical-radical
membership, with no extra vanishing premise on arbitrary polynomials. -/
theorem mem_radical_of_monomial_pairings (τ : MvPolynomial α ℤ →+ M)
    (r : MvPolynomial α ℤ)
    (h : ∀ e : α →₀ ℕ, τ (r * monomial e 1) = 0) : r ∈ traceRadical τ := by
  intro b
  induction b using MvPolynomial.induction_on' with
  | monomial e c =>
      have he : monomial e c = c • (monomial e 1 : MvPolynomial α ℤ) := by
        rw [smul_monomial]
        simp only [smul_eq_mul, mul_one]
      rw [he, mul_smul_comm, map_zsmul, h, smul_zero]
  | add p q hp hq => rw [mul_add, map_add, hp, hq, add_zero]

theorem quotient_eq_of_monomial_pairings (τ : MvPolynomial α ℤ →+ M)
    (r s : MvPolynomial α ℤ)
    (h : ∀ e : α →₀ ℕ, τ ((r - s) * monomial e 1) = 0) :
    Ideal.Quotient.mk (traceRadical τ) r = Ideal.Quotient.mk (traceRadical τ) s := by
  apply Ideal.Quotient.eq.mpr
  exact mem_radical_of_monomial_pairings τ (r - s) h

end M9Native.CurvePowerPolynomialTrace
