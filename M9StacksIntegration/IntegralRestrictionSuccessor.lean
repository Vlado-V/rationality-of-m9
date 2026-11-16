module

public import M9StacksIntegration.IntegralRestrictionLadder
public import Mathlib.LinearAlgebra.LinearIndependent.Lemmas

/-! The nonzero next section in an integrality/kernel induction is
derived from the previous computed kernel and the original coefficient
independence. No nonzero-next premise is required in that induction. -/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

open AlgebraicGeometry CategoryTheory
open Stacks.Bertini

universe u

namespace M9Native.IntegralRestrictionSuccessor

open IntegralRestrictionLadder

variable (D : FamilyDivisors.{u,u}) {X : Scheme.{u}} (g : X ⟶ D.X)

theorem next_section_ne_zero {r : ℕ} (previous : Fin r → D.V) (w : D.V)
    (hk : LinearMap.ker (restrictionMap D g) ≤ Submodule.span D.k (Set.range previous))
    (hw : w ∉ Submodule.span D.k (Set.range previous)) :
    (D.pullbackAlong g).sectionOf w ≠ 0 := by
  intro hz
  exact hw (hk hz)

theorem next_section_ne_zero_of_independent {r : ℕ}
    (previous : Fin r → D.V) (w : D.V)
    (hk : LinearMap.ker (restrictionMap D g) = Submodule.span D.k (Set.range previous))
    (hLI : LinearIndependent D.k (Fin.snoc previous w)) :
    (D.pullbackAlong g).sectionOf w ≠ 0 :=
  next_section_ne_zero D g previous w hk.le (linearIndependent_finSnoc.mp hLI).2

end M9Native.IntegralRestrictionSuccessor
end
