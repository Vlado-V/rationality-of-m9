module

public import M9StacksIntegration.LagrangianFlagFundamentalTransport
public import StacksFrontier.AlgebraicGeometry.Chow.DominantPrimeCycle
public import StacksFrontier.AlgebraicGeometry.Chow.Degrees.DegreeHomomorphism

/-! The actual degree of the original field-base fundamental class is one. -/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1000000
set_option maxRecDepth 4096

open AlgebraicGeometry CategoryTheory Stacks.Chow

universe u

namespace M9Native.LagrangianActualDegree

theorem identityFundamental_degree (C : ChowSituation.{u})
    (hδ : ∀ s : C.S, C.dimensionFunction s = 0)
    [Subsingleton C.S] [IsIntegral C.S] (s : C.S) :
    chowDegree C hδ (𝟙 C.S) s
      (LagrangianFlagFundamentalTransport.fundamentalClass C (𝟙 C.S) 0) = 1 := by
  classical
  rw [LagrangianFlagFundamentalTransport.fundamentalClass,chowDegree_mk,cycleDegree_id]
  have hdim : relativeDimension C.dimensionFunction (𝟙 C.S) (genericPoint C.S) = 0 := by
    rw [relativeDimension_id]
    exact hδ _
  rw [cycleAssociatedToClosedSubscheme_eq_single C (𝟙 C.S) (𝟙 C.S) 0 hdim]
  have hp : s = (𝟙 C.S) (genericPoint C.S) := Subsingleton.elim _ _
  simp only [hp,Function.locallyFinsuppWithin.single_apply,ite_true]

theorem baseFundamental_degree (K : Type u) [Field K] :
    chowDegree (fieldChowSituation K) (fieldChowSituation_dimensionFunction_eq_zero K)
      (𝟙 (Spec (.of K))) (IsLocalRing.closedPoint K)
      (LagrangianFlagFundamentalTransport.baseFundamental K) = 1 :=
  identityFundamental_degree (fieldChowSituation K)
    (fieldChowSituation_dimensionFunction_eq_zero K) (IsLocalRing.closedPoint K)

end M9Native.LagrangianActualDegree
