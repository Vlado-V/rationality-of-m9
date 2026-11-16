module

public import M9StacksIntegration.LagrangianSecondChernDegree
public import M9StacksIntegration.LagrangianDegreeSixteen

/-! The literal integral second-Chern mixed cap degree on the original LG.
Both the Chern relation and degree sixteen are genuine checked producers.
No identification of a separately defined Schubert subscheme is asserted.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false

open AlgebraicGeometry CategoryTheory Stacks.Chow

universe u

namespace M9Native.LagrangianMixedDegreeEight

open LagrangianGrassmannian LagrangianQuotientChernRelation LagrangianDegree

variable (K : Type u) [Field K] [CharZero K]

/-- Integer cancellation uses the actual degree sixteen, with no division
in the operational Chow ring or any Chow group. -/
theorem mixedDegree_eq_eight : LagrangianSecondChernDegree.mixedDegree K = 8 := by
  have h := LagrangianSecondChernDegree.two_mul_mixedDegree_eq_pluckerCapDegree K
  rw [LagrangianActualDegree.pluckerCapDegree_eq_sixteen K] at h
  omega

/-- Fully expanded original c2(Q) times H to the fourth, on the genuine
six-dimensional fundamental class and original structural proper map. -/
theorem secondChern_H_fourth_cap_degree_eq_eight :
    chowDegree (fieldChowSituation K) (fieldChowSituation_dimensionFunction_eq_zero K)
      (projection K) (IsLocalRing.closedPoint K)
      ((secondChern K (fieldChowSituation K) (projection K) *
        H K (fieldChowSituation K) (projection K) ^ 4) 6 6
          (lagrangianOwnFundamental K)) = 8 :=
  mixedDegree_eq_eight K

end M9Native.LagrangianMixedDegreeEight
