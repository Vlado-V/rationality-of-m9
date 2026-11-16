module

public import M9StacksIntegration.LagrangianRegularSection
public import M9StacksIntegration.LagrangianFundamentalClasses
public import StacksFrontier.AlgebraicGeometry.Chow.SectionZeroScheme.Induction

/-!
# The genuine top-Chern fundamental class of the actual LG

The actual dimension-nine ambient scheme, actual rank-three equation
bundle, actual dimension-six zero scheme and actual length-three native
regular stalk generators discharge every hypothesis of Stacks 0FA9.
The cycle classes are the original native Chow classes of the original
schemes and inclusion. No expected codimension or Chern identity is
supplied as a premise.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false

open AlgebraicGeometry CategoryTheory TopologicalSpace
open Stacks.Chow Stacks.Chow.SectionZeroScheme

universe u

namespace M9Native.LagrangianDegree

open M9Native.LagrangianGrassmannian

variable (K : Type u) [Field K]

/-- Stacks 0FA9 on the actual original LG section: c3(Lambda2 Q)
capped with the actual ambient class equals the actual LG class. -/
theorem topChern_cap_ambient_eq_lagrangian :
    GenuineChern.chernCap (fieldChowSituation K) 3 (grassmannianProjection K)
      (equationBundle K) 9 (Fin.last 3) (ambientFundamental K) = lagrangianFundamental K := by
  have hX := ambient_delta_dimension K
  have hZ : schemeDeltaDimension (fieldChowSituation K)
      ((zeroSchemeOfSection (grassmannian K) (equationBundle K)
        (equationSection K)).subschemeι ≫ grassmannianProjection K) ≤ (6 : EInt) := by
    rw [zeroSchemeOfSection_eq_ideal]
    exact (lagrangian_delta_dimension K).le
  have h := reducedTopChernCap (fieldChowSituation K) 3 (grassmannianProjection K)
    (equationBundle K) (equationSection K) 9 hX.le hZ
      (equation_regular_sequence K (fieldChowSituation K) (grassmannianProjection K) 6)
  simpa [ambientFundamental, lagrangianFundamental, zeroSchemeOfSection_eq_ideal] using h

end M9Native.LagrangianDegree
