module

public import StacksFrontier.AlgebraicGeometry.Divisors.RegularSectionIntegral
public import StacksFrontier.AlgebraicGeometry.Divisors.ZeroSchemeIdealSheaf

/-! The actual Cartier divisor and actual divisor-line isomorphism of a
nonzero section on an integral scheme. These retain the defining section
and are used for numerical descent along the genuine hyperplane flag. -/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open AlgebraicGeometry CategoryTheory Opposite

universe u

namespace M9Native.IntegralLineSectionCartier

variable {X : Scheme.{u}} [IsIntegral X] (L : X.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible
      X.sheaf.obj X.ringCatSheaf.property L]
    (s : Γ(L, ⊤)) (hs : s ≠ 0)

include hs

/-- Nonzero-section multiplication is genuinely injective on every
open of the actual integral scheme. -/
theorem multiplication_injective (U : X.Opens) :
    Function.Injective (fun r : Γ(X, U) =>
      r • L.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op s) :=
  fun _ _ h => eq_of_smul_map_le_top_eq_of_isIntegral L s hs U h

/-- The actual section zero scheme is an actual effective Cartier divisor. -/
theorem cartier : Stacks.Divisors.IsEffectiveCartierDivisor (AlgebraicGeometry.zeroScheme X L s) :=
  isEffectiveCartierDivisor_zeroScheme_of_ne_zero L s hs

/-- The original line is the actual divisor line of its actual zero scheme. -/
def lineIso : L ≅ Stacks.Divisors.invertibleSheaf' (AlgebraicGeometry.zeroScheme X L s) :=
  invertibleSheafIsoZeroScheme L s (multiplication_injective L s hs)

/-- The actual line isomorphism carries the defining original section
to the actual canonical section of its Cartier divisor. -/
theorem lineIso_section : (lineIso L s hs).hom.app ⊤ s =
    (Stacks.Divisors.canonicalSection' (AlgebraicGeometry.zeroScheme X L s)).val (op ⊤) :=
  invertibleSheafIsoZeroScheme_section L s (multiplication_injective L s hs)

end M9Native.IntegralLineSectionCartier
