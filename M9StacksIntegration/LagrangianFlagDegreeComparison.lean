module

public import M9StacksIntegration.LagrangianFlagModelComparison
public import M9StacksIntegration.LagrangianFlagNumeratorPullback
public import M9StacksIntegration.LagrangianFreeFlagDegree
public import M9StacksIntegration.LagrangianNormalizedFlagDegree
public import M9StacksIntegration.ChowFlagTriplePushDegree
public import M9StacksIntegration.LagrangianFlagPolynomialPush
public import M9StacksIntegration.LagrangianBaseDegree
public import M9StacksIntegration.LagrangianFlagIntegralDegree

/-! Actual integer-degree assembly for the two original flag models. -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1500000
set_option maxRecDepth 4096
open AlgebraicGeometry CategoryTheory Stacks.Chow
universe u
namespace M9Native.LagrangianFlagDegreeComparison
open LagrangianGrassmannian LagrangianDegree LagrangianActualDegree
open LagrangianFlagFundamentalTransport LagrangianFlagPolynomialTransport
open LagrangianChowStructureTransport LagrangianFlagModelComparison
open GradedLineCapSubring

attribute [local instance] ChowFlagThreeNormalizer.sourceFinite
  ChowFlagThreeNormalizer.kernel1Rank ChowFlagThreeNormalizer.kernel1Finite
  ChowFlagThreeNormalizer.kernel2Rank ChowFlagThreeNormalizer.kernel2Finite
  ChowFlagThreeNormalizer.projection1LFT ChowFlagThreeNormalizer.projection2LFT
  ChowFlagThreeNormalizer.projection3LFT
  LagrangianFlagPowerStages.sourceFinite LagrangianFlagPowerStages.kernel1Rank
  LagrangianFlagPowerStages.kernel1Finite LagrangianFlagPowerStages.kernel2Rank
  LagrangianFlagPowerStages.kernel2Finite LagrangianFlagPowerStages.projection1LFT
  LagrangianFlagPowerStages.projection2LFT LagrangianFlagPowerStages.projection3LFT
  LagrangianFlagModelComparison.freeRank LagrangianFlagModelComparison.freeFinite
  LagrangianFlagModelComparison.quotientFinite

variable (K : Type u) [Field K] [CharZero K]

/-- The original determinant packages represent the same original native sheaf. -/
theorem sourceNumerator_eq_ambient :
    LagrangianFlagNumeratorPullback.sourceNumerator (quotientBundle K)
      (fieldChowSituation K) (grassmannianProjection K) = ambientNumerator K :=
  LagrangianNormalizedFlagDegree.sourceNumerator_eq_ambient K

/-- The proved zero-grade native cap classes also agree. -/
theorem sourceNumeratorClass_eq_ambient :
    LagrangianFlagNumeratorPullback.sourceNumeratorClass (quotientBundle K)
      (fieldChowSituation K) (grassmannianProjection K) (ambientFundamental K) =
    ambientNumeratorClass K :=
  LagrangianNormalizedFlagDegree.sourceNumeratorClass_eq_ambient K

/-- Actual normalization and all three original proper pushes identify
its integer degree with the native quotient-flag polynomial degree. -/
theorem ambient_degree_eq_nativeA :
    chowDegree (fieldChowSituation K) (fieldChowSituation_dimensionFunction_eq_zero K)
      (grassmannianProjection K) (IsLocalRing.closedPoint K) (ambientNumeratorClass K) =
    chowDegree (fieldChowSituation K) (fieldChowSituation_dimensionFunction_eq_zero K)
      (qA K) (IsLocalRing.closedPoint K) (nativeClassA K) := by
  have hD := LagrangianNormalizedFlagDegree.degree_actualClass_eq_ambient K
  have hCast := degree_structureMapCast (fieldChowSituation K)
    (quotientMap K) (qA K) (quotientMap_eq_native K)
    (fieldChowSituation_dimensionFunction_eq_zero K) (IsLocalRing.closedPoint K)
    (LagrangianFlagNumeratorPullback.integrandClass (quotientBundle K)
      (fieldChowSituation K) (grassmannianProjection K) (ambientFundamental K))
  have hNative := (congrArg
    (chowDegree (fieldChowSituation K) (fieldChowSituation_dimensionFunction_eq_zero K)
      (qA K) (IsLocalRing.closedPoint K)) (quotientIntegrand_cast_native K)).symm.trans hCast
  exact hD.symm.trans hNative.symm

/-- The actual native flag isomorphism preserves the original polynomial degree. -/
theorem nativeA_degree_eq_nativeB :
    chowDegree (fieldChowSituation K) (fieldChowSituation_dimensionFunction_eq_zero K)
      (qA K) (IsLocalRing.closedPoint K) (nativeClassA K) =
    chowDegree (fieldChowSituation K) (fieldChowSituation_dimensionFunction_eq_zero K)
      (qB K) (IsLocalRing.closedPoint K) (nativeClassB K) := by
  unfold nativeClassA nativeClassB
  change chowDegree (fieldChowSituation K) (fieldChowSituation_dimensionFunction_eq_zero K)
      (qA K) (IsLocalRing.closedPoint K)
      (LagrangianChowPolynomials.evaluate (fieldChowSituation K) (qA K)
        (linesA K) LagrangianFlagCoefficientFunctional.integrand 12 12 (fundamentalA K)) =
    chowDegree (fieldChowSituation K) (fieldChowSituation_dimensionFunction_eq_zero K)
      (qB K) (IsLocalRing.closedPoint K)
      (LagrangianChowPolynomials.evaluate (fieldChowSituation K) (qB K)
        (linesB K) LagrangianFlagCoefficientFunctional.integrand 12 12 (fundamentalB K))
  exact LagrangianFlagIntegralDegree.polynomial_degree_eq K
    LagrangianFlagCoefficientFunctional.integrand

/-- The actual free flag uses the original checked free-six integration class. -/
theorem freeClass_triplePush :
    LagrangianFlagPowerStages.triplePush (freeSix K) (fieldChowSituation K)
      (𝟙 (Spec (.of K))) 0 (freeClass K) = 16 • baseFundamental K :=
  LagrangianFreeFlagDegree.actualClass_triplePush K

/-- The genuine free-flag proper pushes and the degree-one original base point
compute the actual native polynomial degree, with no numeric-degree premise. -/
theorem nativeB_degree_eq_sixteen :
    chowDegree (fieldChowSituation K) (fieldChowSituation_dimensionFunction_eq_zero K)
      (qB K) (IsLocalRing.closedPoint K) (nativeClassB K) = 16 := by
  have hCast := degree_structureMapCast (fieldChowSituation K) (freeMap K) (qB K)
    (freeMap_eq_native K) (fieldChowSituation_dimensionFunction_eq_zero K)
    (IsLocalRing.closedPoint K) (freeClass K)
  have hNative := (congrArg
    (chowDegree (fieldChowSituation K) (fieldChowSituation_dimensionFunction_eq_zero K)
      (qB K) (IsLocalRing.closedPoint K)) (freeIntegrand_cast_native K)).symm.trans hCast
  exact hNative.trans (LagrangianFreeFlagDegree.degree_actualClass_eq_sixteen K)

end M9Native.LagrangianFlagDegreeComparison
