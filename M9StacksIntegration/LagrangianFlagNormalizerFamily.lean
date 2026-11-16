module

public import M9StacksIntegration.ChowFlagThreeNormalizer

/-!
# The genuine flag normalizer as the same operational line polynomial

This is a change of the proved native capPow spelling only. The actual
normalization is the already-proved triple proper push on the actual
rank-three full flag, with its actual flat pullbacks.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1500000
set_option maxRecDepth 4096

open AlgebraicGeometry CategoryTheory Stacks.Chow

universe u

namespace M9Native.LagrangianFlagNormalizerFamily

open GradedLineCapSubring GradedCapVirtualSchur ChowCapWords

attribute [local instance] ChowFlagThreeNormalizer.sourceFinite
  ChowFlagThreeNormalizer.kernel1Rank ChowFlagThreeNormalizer.kernel1Finite
  ChowFlagThreeNormalizer.kernel2Rank ChowFlagThreeNormalizer.kernel2Finite
  ChowFlagThreeNormalizer.projection1LFT ChowFlagThreeNormalizer.projection2LFT
  ChowFlagThreeNormalizer.projection3LFT

variable {X : Scheme.{u}} (D : X.Modules)
  [SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} D 3]
  (C : ChowSituation.{u}) (q : X ⟶ C.S) [LocallyOfFiniteType q]

local notation "qF" => ChowFlagThreeNormalizer.baseMap3 D C q

/-- The literal polynomial in the two original positive flag-line caps. -/
def normalizingFamily : GradedCapFamily (chowGroup C qF) :=
  lineFamily C qF (ChowFlagThreeNormalizer.flagLine1 D) ^ 2 *
    lineFamily C qF (ChowFlagThreeNormalizer.flagLine2 D)

theorem normalizingFamily_homogeneous : (normalizingFamily D C q).IsHomogeneous 3 :=
  ((lineFamily_homogeneous C qF (ChowFlagThreeNormalizer.flagLine1 D)).pow 2).mul
    (lineFamily_homogeneous C qF (ChowFlagThreeNormalizer.flagLine2 D))

/-- The operational component is the same native positive-line normalizer. -/
theorem normalizingFamily_apply (k : ℤ) (α : chowGroup C q k) :
    gradedDegreeCast (chowGroup C qF) (show (k+3)-(3:ℤ)=k by omega)
      (normalizingFamily D C q (k+3) 3 (ChowFlagThreeNormalizer.flatPullClass D C q k α)) =
      ChowFlagThreeNormalizer.normalClass D C q k α := by
  let L1 := ChowFlagThreeNormalizer.flagLine1 D
  let L2 := ChowFlagThreeNormalizer.flagLine2 D
  let β := ChowFlagThreeNormalizer.flatPullClass D C q k α
  let γ := capPow C qF (lineCap C qF L2) 1 (k+3) (k+2) (by omega) β
  have hMul := mul_apply_of_homogeneous_right (lineFamily C qF L1 ^ 2)
    (lineFamily_homogeneous C qF L2) 2 (k+3) β
  have hSecond : lineFamily C qF L2 (k+3) 1 β ≍ γ := by
    simpa only [pow_one] using
      LineFamilyCapPower.lineFamily_pow_apply_heq C qF L2 1 (k+3) (k+2) (by omega) β
  have hFirst := LineFamilyCapPower.lineFamily_pow_apply_heq C qF L1 2
    (k+2) k (by omega) γ
  apply eq_of_heq
  refine (gradedDegreeCast_heq _ _).trans ((heq_of_eq hMul).trans ?_)
  rw [capTo_def]
  refine (gradedDegreeCast_heq _ _).trans ?_
  exact ((lineFamily C qF L1 ^ 2).apply_heq (by omega) 2 hSecond).trans hFirst

/-- All three true proper pushes of this actual polynomial normalizer
on the actual full flat pullback equal the original class. -/
theorem triplePush_normalizingFamily (k : ℤ) (α : chowGroup C q k) :
    ChowFlagThreeNormalizer.triplePush D C q k
      (gradedDegreeCast (chowGroup C qF) (show (k+3)-(3:ℤ)=k by omega)
        (normalizingFamily D C q (k+3) 3
          (ChowFlagThreeNormalizer.flatPullClass D C q k α))) = α := by
  rw [normalizingFamily_apply]
  exact ChowFlagThreeNormalizer.triplePush_normalClass D C q k α

end M9Native.LagrangianFlagNormalizerFamily
