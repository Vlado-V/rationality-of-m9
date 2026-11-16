module

public import M9StacksIntegration.LagrangianAmbientNumerator
public import M9StacksIntegration.LagrangianFlagNumeratorPullback
public import M9StacksIntegration.ChowFlagTriplePushDegree

/-! The actual original LG determinant degree equals the integer degree
of the actual normalized quotient-flag integrand. Every source class
and map is the original native one; no model comparison is assumed. -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1500000
set_option maxRecDepth 4096
open AlgebraicGeometry CategoryTheory Stacks.Chow
universe u
namespace M9Native.LagrangianNormalizedFlagDegree
open LagrangianGrassmannian LagrangianDegree LagrangianActualDegree
open GradedLineCapSubring

attribute [local instance] ChowFlagThreeNormalizer.sourceFinite
  ChowFlagThreeNormalizer.kernel1Rank ChowFlagThreeNormalizer.kernel1Finite
  ChowFlagThreeNormalizer.kernel2Rank ChowFlagThreeNormalizer.kernel2Finite
  ChowFlagThreeNormalizer.projection1LFT ChowFlagThreeNormalizer.projection2LFT
  ChowFlagThreeNormalizer.projection3LFT

variable (K : Type u) [Field K] [CharZero K]
local instance quotientFinite : SheafOfModules.IsFiniteLocallyFree.{u,u,u} (quotientBundle K) :=
  (quotientBundle_rank K).isFiniteLocallyFree

abbrev quotientMap := ChowFlagThreeNormalizer.baseMap3 (quotientBundle K)
  (fieldChowSituation K) (grassmannianProjection K)

/-- The literal original normalized polynomial cap on the full flat pull of Gr's fundamental. -/
def actualClass : chowGroup (fieldChowSituation K) (quotientMap K) 0 :=
  LagrangianFlagNumeratorPullback.integrandClass (quotientBundle K)
    (fieldChowSituation K) (grassmannianProjection K) (ambientFundamental K)

/-- The original determinant packages represent the same original native sheaf. -/
theorem sourceNumerator_eq_ambient :
    LagrangianFlagNumeratorPullback.sourceNumerator (quotientBundle K)
      (fieldChowSituation K) (grassmannianProjection K) = ambientNumerator K := by
  have e : (LagrangianFlagChernNumerator.originalDeterminantLine (quotientBundle K)).1 ≅
      (ambientDeterminantLine K).1 := by
    dsimp only [LagrangianFlagChernNumerator.originalDeterminantLine,
      ambientDeterminantLine,MukaiBundleDeterminant.topExterior]
    simp only [Nat.cast_ofNat]
    exact Iso.refl _
  have hLine := ChowLineFamilyComparison.lineFamily_congr (fieldChowSituation K)
    (grassmannianProjection K)
    (LagrangianFlagChernNumerator.originalDeterminantLine (quotientBundle K))
    (ambientDeterminantLine K) e
  unfold LagrangianFlagNumeratorPullback.sourceNumerator ambientNumerator
  rw [hLine]

/-- The proved zero-grade native cap classes also agree. -/
theorem sourceNumeratorClass_eq_ambient :
    LagrangianFlagNumeratorPullback.sourceNumeratorClass (quotientBundle K)
      (fieldChowSituation K) (grassmannianProjection K) (ambientFundamental K) =
    ambientNumeratorClass K := by
  unfold LagrangianFlagNumeratorPullback.sourceNumeratorClass ambientNumeratorClass
  rw [sourceNumerator_eq_ambient]

/-- The actual three proper pushes preserve the integer degree and
return the actual ambient determinant/exterior-square numerator. -/
theorem degree_actualClass_eq_ambient :
    chowDegree (fieldChowSituation K) (fieldChowSituation_dimensionFunction_eq_zero K)
      (quotientMap K) (IsLocalRing.closedPoint K) (actualClass K) =
    chowDegree (fieldChowSituation K) (fieldChowSituation_dimensionFunction_eq_zero K)
      (grassmannianProjection K) (IsLocalRing.closedPoint K) (ambientNumeratorClass K) := by
  have hTriple := LagrangianFlagNumeratorPullback.triplePush_integrand
    (quotientBundle K) (fieldChowSituation K) (grassmannianProjection K) (ambientFundamental K)
  have hDegree := ChowFlagTriplePushDegree.rankThree_triplePush_degree K (quotientBundle K)
    (grassmannianProjection K) (actualClass K)
  have hValue := congrArg
    (chowDegree (fieldChowSituation K) (fieldChowSituation_dimensionFunction_eq_zero K)
      (grassmannianProjection K) (IsLocalRing.closedPoint K))
    (hTriple.trans (sourceNumeratorClass_eq_ambient K))
  exact hDegree.trans hValue

/-- This is a genuine binding of the actual original LG determinant-cap degree
to the actual normalized quotient-flag class, without a class comparison premise. -/
theorem pluckerCapDegree_eq_actualDegree :
    pluckerCapDegree K =
    chowDegree (fieldChowSituation K) (fieldChowSituation_dimensionFunction_eq_zero K)
      (quotientMap K) (IsLocalRing.closedPoint K) (actualClass K) :=
  (pluckerCapDegree_eq_ambientNumerator K).trans (degree_actualClass_eq_ambient K).symm

end M9Native.LagrangianNormalizedFlagDegree
