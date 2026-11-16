module

public import M9StacksIntegration.LagrangianChowDimensions
public import StacksFrontier.AlgebraicGeometry.Chow.ProperPushforwardClosedSubscheme
public import StacksFrontier.AlgebraicGeometry.Chow.ProperPushforwardPrincipal.GenericFibre

/-!
# The original ambient and LG fundamental Chow classes

All classes below use the actual original native schemes. Proper
pushforward of the original LG fundamental class is proved to be its
actual closed-subscheme cycle class in the original Grassmannian.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false

open AlgebraicGeometry CategoryTheory
open Stacks.Chow

universe u

namespace M9Native.LagrangianDegree

open M9Native.LagrangianGrassmannian

variable (K : Type u) [Field K]

/-- The original ambient native fundamental Chow class in dimension9. -/
def ambientFundamental : chowGroup (fieldChowSituation K) (grassmannianProjection K) 9 :=
  QuotientAddGroup.mk' (rationalEquivalences (fieldChowSituation K) (grassmannianProjection K) 9)
    (cycleAssociatedToClosedSubscheme (fieldChowSituation K) (grassmannianProjection K)
      (𝟙 (grassmannian K)) 9)

/-- The actual original LG cycle, as a closed subscheme of the original Gr. -/
def lagrangianFundamental : chowGroup (fieldChowSituation K) (grassmannianProjection K) 6 :=
  QuotientAddGroup.mk' (rationalEquivalences (fieldChowSituation K) (grassmannianProjection K) 6)
    (cycleAssociatedToClosedSubscheme (fieldChowSituation K) (grassmannianProjection K)
      (inclusion K) 6)

/-- The actual original LG fundamental class on LG itself. -/
def lagrangianOwnFundamental : chowGroup (fieldChowSituation K) (projection K) 6 :=
  QuotientAddGroup.mk' (rationalEquivalences (fieldChowSituation K) (projection K) 6)
    (cycleAssociatedToClosedSubscheme (fieldChowSituation K) (projection K) (𝟙 (space K)) 6)

/-- Genuine proper pushforward along the literal original inclusion;
preservation of rational equivalence is proved by the native theorem. -/
def inclusionChowPush (k : ℤ) :
    chowGroup (fieldChowSituation K) (projection K) k →+
      chowGroup (fieldChowSituation K) (grassmannianProjection K) k :=
  properChowPushforward (fieldChowSituation K) (projection K) (grassmannianProjection K)
    (inclusion K) rfl k
    (properPushforwardFactorsThroughRationalEquivalence_of_isProper
      (fieldChowSituation K) (projection K) (grassmannianProjection K) (inclusion K) rfl k)

/-- The two actual fundamental classes agree under actual proper pushforward. -/
theorem inclusionChowPush_fundamental :
    inclusionChowPush K 6 (lagrangianOwnFundamental K) = lagrangianFundamental K := by
  unfold inclusionChowPush lagrangianOwnFundamental lagrangianFundamental
  rw [properChowPushforward_mk,
    properPushforward_cycleAssociatedToClosedSubscheme_of_isClosedImmersion_comp]
  simp only [Category.id_comp]

end M9Native.LagrangianDegree
