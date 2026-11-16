module

public import M9StacksIntegration.LagrangianGenericRegularStalk
public import StacksFrontier.AlgebraicGeometry.Chow.ChernClassOfSection

/-!
# The original LG is a genuine regular zero scheme for Stacks0FA9

The zero ideal is literally the existing dual-evaluation ideal. Every
original generic LG point has actual regular generators of length3
in its original ambient stalk. This discharges the actual native
regular-section predicate on every relevant Chow dimension stratum.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false

open AlgebraicGeometry CategoryTheory TopologicalSpace
open Stacks.Chow

universe u

namespace M9Native.LagrangianDegree

open M9Native.LagrangianGrassmannian

variable (K : Type u) [Field K]

theorem zeroSchemeOfSection_eq_ideal :
    zeroSchemeOfSection (grassmannian K) (equationBundle K) (equationSection K) = ideal K := rfl

/-- The genuine native regular-sequence predicate is derived for
every Chow base situation and every dimension stratum. -/
theorem equation_regular_sequence (C : ChowSituation.{u})
    (q : grassmannian K ⟶ C.S) [LocallyOfFiniteType q] (m : ℤ) :
    IsRegularZeroSchemeSequence C q (equationBundle K) (equationSection K) 3 m := by
  unfold IsRegularZeroSchemeSequence
  intro xi _
  exact generic_stalk_regular_three K xi

end M9Native.LagrangianDegree
