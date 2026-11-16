module

public import M9StacksIntegration.GradedCapTopTrace

/-! A nonzero actual top trace detects nonvanishing on the actual
fundamental Chow class, rather than merely a nonzero abstract operator. -/

@[expose] public noncomputable section
set_option autoImplicit false

open AlgebraicGeometry CategoryTheory

universe u
namespace M9Native.GradedCapTopTraceNonvanishing

open Stacks.Chow CurveTopChowClass GradedCapTopTrace

variable (k : Type u) [Field k] {X : Scheme.{u}}
  (f : X ⟶ Spec (.of k)) [IsProper f]
  (N : ℕ) (A : GradedCapFamily (chowGroup (fieldChowSituation k) f))

theorem topTrace_eq_zero_of_fundamental_component_eq_zero
    (h : A (N : ℤ) N
      (identityChowClass (fieldChowSituation k) f (N : ℤ)) = 0) :
    topTrace k f N A = 0 := by
  rw [topTrace_apply, h]
  simp only [map_zero]

theorem fundamental_component_ne_zero_of_topTrace_ne_zero
    (h : topTrace k f N A ≠ 0) :
    A (N : ℤ) N
      (identityChowClass (fieldChowSituation k) f (N : ℤ)) ≠ 0 := by
  intro hz
  exact h (topTrace_eq_zero_of_fundamental_component_eq_zero k f N A hz)

end M9Native.GradedCapTopTraceNonvanishing
