module

public import M9StacksIntegration.LagrangianFlagPolynomialTransport
public import StacksFrontier.AlgebraicGeometry.Variety.NumericalIntersections.ChowDegree

/-! The actual integer degree of every original quotient-line polynomial
is preserved by the native isomorphism of the two flag towers. -/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1000000
set_option maxRecDepth 4096

open AlgebraicGeometry CategoryTheory Stacks.Chow
universe u
namespace M9Native.LagrangianFlagIntegralDegree
open LagrangianFlagFundamentalTransport LagrangianFlagPolynomialTransport

variable (K : Type u) [Field K]

/-- The original source flag is proper, by its actual isomorphism over
the field with the proper free-six flag. -/
instance qA_isProper : IsProper (qA K) := by
  rw [← towerIso_hom_comp K]
  infer_instance

/-- The same actual polynomial cap on each original fundamental class
has the same native integer degree under the original flag isomorphism. -/
theorem polynomial_degree_eq (P : MvPolynomial (Fin 3) ℤ) :
    chowDegree (fieldChowSituation K) (fieldChowSituation_dimensionFunction_eq_zero K)
      (qA K) (IsLocalRing.closedPoint K)
      (LagrangianChowPolynomials.evaluate (fieldChowSituation K) (qA K)
        (linesA K) P 12 12 (fundamentalA K)) =
    chowDegree (fieldChowSituation K) (fieldChowSituation_dimensionFunction_eq_zero K)
      (qB K) (IsLocalRing.closedPoint K)
      (LagrangianChowPolynomials.evaluate (fieldChowSituation K) (qB K)
        (linesB K) P 12 12 (fundamentalB K)) := by
  have hDegree := chowDegree_properChowPushforward K (qB K) (qA K)
    (towerIso K).hom (towerIso_hom_comp K)
    (LagrangianChowPolynomials.evaluate (fieldChowSituation K) (qA K)
      (linesA K) P 12 12 (fundamentalA K))
  exact hDegree.trans (congrArg
    (chowDegree (fieldChowSituation K) (fieldChowSituation_dimensionFunction_eq_zero K)
      (qB K) (IsLocalRing.closedPoint K))
    (isoChowPush_evaluate_fundamental K P))

end M9Native.LagrangianFlagIntegralDegree
