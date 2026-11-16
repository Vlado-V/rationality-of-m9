module

public import Mathlib.RingTheory.Ideal.Quotient.Defs
public import Mathlib.Tactic

/-!
# The radical defined by an actual intersection trace

This construction adds no numerical relation. It takes the annihilator
of all product pairings under the given additive trace. When that trace
is the actual curve-power intersection functional, its quotient is the
restricted numerical target for the moving-graph calculation.
-/

@[expose] public section

namespace M9Native.CurvePowerTraceRadical

variable {R S M : Type*} [CommRing R] [Ring S] [AddCommGroup M]

def traceRadical (τ : R →+ M) : Ideal R where
  carrier := {a | ∀ b : R, τ (a * b) = 0}
  zero_mem' := by intro b; simp
  add_mem' := by
    intro a b ha hb c
    rw [add_mul, map_add, ha c, hb c, add_zero]
  smul_mem' := by
    intro c a ha b
    change τ ((c * a) * b) = 0
    rw [show (c * a) * b = a * (c * b) by ring]
    exact ha (c * b)

theorem mem_traceRadical_iff (τ : R →+ M) (a : R) :
    a ∈ traceRadical τ ↔ ∀ b : R, τ (a * b) = 0 := Iff.rfl

theorem trace_eq_zero_of_mem (τ : R →+ M) {a : R} (ha : a ∈ traceRadical τ) : τ a = 0 := by
  simpa only [mul_one] using ha 1

/-- The actual additive trace descends to its pairing quotient. -/
def quotientTrace (τ : R →+ M) : R ⧸ traceRadical τ →+ M :=
  QuotientAddGroup.lift (traceRadical τ).toAddSubgroup τ
    (fun _ ha => trace_eq_zero_of_mem τ ha)

theorem quotientTrace_mk (τ : R →+ M) (a : R) :
    quotientTrace τ (Ideal.Quotient.mk (traceRadical τ) a) = τ a := rfl

theorem quotientTrace_mul_mk (τ : R →+ M) (a b : R) :
    quotientTrace τ (Ideal.Quotient.mk (traceRadical τ) a *
      Ideal.Quotient.mk (traceRadical τ) b) = τ (a * b) := rfl

theorem quotient_eq_zero_iff_pairings (τ : R →+ M) (a : R) :
    Ideal.Quotient.mk (traceRadical τ) a = 0 ↔ ∀ b : R, τ (a * b) = 0 :=
  Ideal.Quotient.eq_zero_iff_mem

theorem quotient_eq_iff_pairings (τ : R →+ M) (a b : R) :
    Ideal.Quotient.mk (traceRadical τ) a = Ideal.Quotient.mk (traceRadical τ) b ↔
      ∀ c : R, τ ((a - b) * c) = 0 := by
  rw [← sub_eq_zero, ← map_sub, quotient_eq_zero_iff_pairings]

/-- A genuine cycle/cohomology realization whose actual trace defines
the pairing has its kernel in the trace radical. No faithfulness or
unproved numerical Poincare formula is required. -/
theorem realization_ker_le_traceRadical (q : R →+* S) (tr : S →+ M) :
    RingHom.ker q ≤ traceRadical (tr.comp q.toAddMonoidHom) := by
  intro a ha b
  change tr (q (a * b)) = 0
  change q a = 0 at ha
  rw [map_mul, ha, zero_mul, map_zero]

/-- Trace compatibility after an injective coefficient change suffices;
in particular an integral intersection trace can be compared with the
actual characteristic-zero de Rham trace. -/
theorem realization_ker_le_traceRadical_of_compat {N : Type*} [AddCommGroup N]
    (q : R →+* S) (tr : S →+ N) (τ : R →+ M) (ι : M →+ N)
    (hι : Function.Injective ι) (hcompat : ∀ a, ι (τ a) = tr (q a)) :
    RingHom.ker q ≤ traceRadical τ := by
  intro a ha b
  apply hι
  change q a = 0 at ha
  rw [hcompat, map_mul, ha, zero_mul, map_zero, map_zero]

theorem quotient_zero_of_realization_zero (q : R →+* S) (tr : S →+ M)
    {a : R} (ha : q a = 0) :
    Ideal.Quotient.mk (traceRadical (tr.comp q.toAddMonoidHom)) a = 0 := by
  apply Ideal.Quotient.eq_zero_iff_mem.mpr
  exact realization_ker_le_traceRadical q tr ha

theorem quotient_zero_of_realization_zero_of_compat {N : Type*} [AddCommGroup N]
    (q : R →+* S) (tr : S →+ N) (τ : R →+ M) (ι : M →+ N)
    (hι : Function.Injective ι) (hcompat : ∀ a, ι (τ a) = tr (q a))
    {a : R} (ha : q a = 0) : Ideal.Quotient.mk (traceRadical τ) a = 0 := by
  apply Ideal.Quotient.eq_zero_iff_mem.mpr
  exact realization_ker_le_traceRadical_of_compat q tr τ ι hι hcompat ha

theorem quotient_ne_zero_of_trace_ne_zero (τ : R →+ M) {a : R} (ha : τ a ≠ 0) :
    Ideal.Quotient.mk (traceRadical τ) a ≠ 0 := by
  intro he
  apply ha
  have h := congrArg (quotientTrace τ) he
  simpa only [quotientTrace_mk, map_zero] using h

theorem realization_ne_zero_of_quotient_ne_zero_of_compat {N : Type*} [AddCommGroup N]
    (q : R →+* S) (tr : S →+ N) (τ : R →+ M) (ι : M →+ N)
    (hι : Function.Injective ι) (hcompat : ∀ a, ι (τ a) = tr (q a))
    {a : R} (ha : Ideal.Quotient.mk (traceRadical τ) a ≠ 0) : q a ≠ 0 := by
  intro he
  exact ha (quotient_zero_of_realization_zero_of_compat q tr τ ι hι hcompat he)

end M9Native.CurvePowerTraceRadical
