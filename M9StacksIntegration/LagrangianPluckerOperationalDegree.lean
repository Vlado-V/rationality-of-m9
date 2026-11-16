module

public import M9StacksIntegration.LagrangianSecondChernDegree

/-!
# The actual Plucker cap degree in operational Chern notation

This is a direct context corollary of the already proved comparison between
six operational first-Chern caps and the original native iterated cap.  It
uses the original LG fundamental class and structural degree map, and has
no numerical degree premise.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false

open AlgebraicGeometry CategoryTheory Stacks.Chow

universe u

namespace M9Native.LagrangianActualDegree

open LagrangianGrassmannian LagrangianDegree LagrangianQuotientChernRelation

variable (K : Type u) [Field K] [CharZero K]

/-- The literal native Plucker cap degree is the degree of the sixth
operational power on the original fundamental class. -/
theorem pluckerCapDegree_eq_operationalDegree :
    pluckerCapDegree K =
      chowDegree (fieldChowSituation K) (fieldChowSituation_dimensionFunction_eq_zero K)
        (projection K) (IsLocalRing.closedPoint K)
        ((H K (fieldChowSituation K) (projection K) ^ 6) 6 6
          (lagrangianOwnFundamental K)) := by
  exact congrArg
    (chowDegree (fieldChowSituation K) (fieldChowSituation_dimensionFunction_eq_zero K)
      (projection K) (IsLocalRing.closedPoint K))
    (LagrangianSecondChernDegree.H_sixth_cap_eq_iterated K).symm

end M9Native.LagrangianActualDegree
