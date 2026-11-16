module

public import M9StacksIntegration.CurveTopChowClass
public import StacksFrontier.AlgebraicGeometry.Chow.ChernCap42.DivisorOfSectionCycle
public import StacksFrontier.AlgebraicGeometry.Chow.ProjectiveBundleFormula.TowerChow
public import StacksFrontier.AlgebraicGeometry.Divisors.DivisorPicardClass
public import StacksFrontier.AlgebraicGeometry.Divisors.ZeroSchemeCanonicalSection
public import StacksFrontier.AlgebraicGeometry.Divisors.CanonicalSectionNonvanishing
public import StacksFrontier.AlgebraicGeometry.Divisors.WeilDivisorClass.CanonicalSectionOrder

/-!
# Capping the actual fundamental class with an actual Cartier divisor

The positive divisor module and its canonical section come from the
original effective Cartier ideal. Its canonical zero scheme is that
same divisor. The native first-Chern theorem for a nonzero section
therefore gives the divisor's actual cycle in the native Chow group.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false

open AlgebraicGeometry CategoryTheory

universe u

namespace M9Native.CartierDivisorChernCap

open Stacks.Chow CurveTopChowClass

variable (C : ChowSituation.{u}) {X : Scheme.{u}} (f : X ⟶ C.S)
  [LocallyOfFiniteType f] [IsIntegral X] (n : ℤ)
  (hn : schemeDeltaDimension C f = (n : EInt)) (D : X.IdealSheafData)
  [hD : Stacks.Divisors.IsEffectiveCartierDivisor D]

include hn

theorem firstChern_cap_fundamental_divisor :
    letI := Stacks.Divisors.isInvertible_invertibleSheaf_picard D
    firstChernClassCapOfInvertible C f (n - 1) (Stacks.Divisors.modulesInvertibleSheaf D)
        (cycleAssociatedToClosedSubscheme C f (𝟙 X) (n - 1 + 1)) =
      QuotientAddGroup.mk (cycleAssociatedToClosedSubscheme C f D.subschemeι (n - 1)) := by
  let := Stacks.Divisors.isInvertible_invertibleSheaf_picard D
  have hs : Stacks.Divisors.canonicalSection D ≠ 0 := by
    rw [← Stacks.Divisors.canonicalSections_eval_top D]
    exact canonicalSections_eval_top_ne_zero D hD
  have h := Stacks.ChernCap42.firstChernClassCapOfInvertible_fundamentalCycle
    C f n hn (Stacks.Divisors.modulesInvertibleSheaf D) (Stacks.Divisors.canonicalSection D) hs
  have hz : Stacks.Divisors.zeroScheme X (Stacks.Divisors.modulesInvertibleSheaf D)
      (Stacks.Divisors.canonicalSection D) = D :=
    Stacks.Divisors.zeroScheme_canonicalSection' D
  rwa [hz] at h

theorem invCap_fundamental_divisor :
    letI := Stacks.Divisors.isInvertible_invertibleSheaf_picard D
    (invCap C f (Stacks.Divisors.modulesInvertibleSheaf D)).capOnChow C f (n - 1)
        (identityChowClass C f (n - 1 + 1)) =
      QuotientAddGroup.mk (cycleAssociatedToClosedSubscheme C f D.subschemeι (n - 1)) :=
  firstChern_cap_fundamental_divisor C f n hn D

end M9Native.CartierDivisorChernCap
