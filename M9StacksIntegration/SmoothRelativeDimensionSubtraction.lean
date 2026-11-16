module

public import StacksFrontier.AlgebraicGeometry.Picard.HilbertSchemeSmoothness
public import Mathlib.Tactic

/-! Subtracting genuine smooth relative dimensions along a smooth composition. -/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open AlgebraicGeometry CategoryTheory TopologicalSpace
universe u
namespace M9Native.SmoothRelativeDimensionSubtraction

theorem withBotENat_add_nat_injective (m : ℕ) :
    Function.Injective (fun a : WithBot ℕ∞ => a+(m : WithBot ℕ∞)) := by
  intro a b h
  cases a with
  | bot =>
    cases b with
    | bot => rfl
    | coe b =>
      have h' := h.symm
      simp at h'
  | coe a =>
    cases b with
    | bot => simp at h
    | coe b =>
      exact congrArg (fun x : ℕ∞ => (x : WithBot ℕ∞))
        (ENat.add_left_injective_of_ne_top (by simp) (WithBot.coe_injective h))

/-- Smoothness and the two actual composite dimensions determine the actual relative dimension. -/
theorem smoothOfRelativeDimension_of_comp {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (n m : ℕ) [Smooth f] [SmoothOfRelativeDimension (n+m) (f ≫ g)]
    [SmoothOfRelativeDimension m g] : SmoothOfRelativeDimension n f := by
  let : Smooth g := SmoothOfRelativeDimension.smooth m g
  apply Stacks.Smooth.smoothOfRelativeDimension_of_fiberDimensionAt_eq f n
  intro x
  have h := topologicalKrullDimAt_fiber_comp_eq_add_of_isFlatAt f g x (Flat.stalkMap f x)
  rw [fiberDimensionAt_eq_of_smoothOfRelativeDimension (f ≫ g) (n+m) x,
    fiberDimensionAt_eq_of_smoothOfRelativeDimension g m (f x)] at h
  apply withBotENat_add_nat_injective m
  exact h.symm.trans (Nat.cast_add n m)

end M9Native.SmoothRelativeDimensionSubtraction
end
