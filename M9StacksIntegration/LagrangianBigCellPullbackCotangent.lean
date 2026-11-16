module

public import M9StacksIntegration.LagrangianBigCellIntrinsic
public import M9StacksIntegration.LagrangianCotangentQuotientFrame
public import M9StacksIntegration.LagrangianCotangentEtale

/-! Actual invertibility of the universal native LG cotangent map on its original big cell. -/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
set_option maxRecDepth 4096

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace M9Native.LagrangianBigCellPullbackCotangent

open LagrangianGrassmannian LagrangianMatrixChart LagrangianBigCellQuotient
open LagrangianPluckerQuotient LagrangianChartCotangent LagrangianIsotropicRestriction
open LagrangianCotangentMap LagrangianCotangentSections LagrangianCotangentQuotientFrame
open LagrangianBigCellIntrinsic LagrangianCotangentEtale

variable (K : Type u) [Field K]

/-- The actual pulled-back quotient has an invertible actual intrinsic
cotangent map, after the genuine original quotient-frame calculation. -/
theorem pulledIntrinsic_isIso :
    IsIso (cotangentMap (bigCell K ≫ projection K)
      (pulledQuotient (bigCell K) (quotientOnLG K).map)
      (pulledQuotient_annihilates (bigCell K) (quotientOnLG K).map
        (LagrangianSymplecticAction.lagrangianUniversal_annihilates K))) := by
  apply (cotangentMap_isIso_congr (bigCell K ≫ projection K) (chartProjection K)
    (bigCell_projection K) _ _).mpr
  exact cotangentMap_isIso_of_targetIso (chartProjection K)
    (pulledQuotient (bigCell K) (quotientOnLG K).map) _
      (bigCellQuotientIso K) (normalizedQuotient_annihilates K)
        (normalizedCotangentMap_isIso K)

/-- The original universal cotangent sheaf map is invertible after
actual pullback to the original native big cell. -/
instance universalCotangentMap_bigCell_isIso :
    IsIso ((Scheme.Modules.pullback (bigCell K)).map (universalCotangentMap K)) :=
  pullback_cotangentMap_isIso (bigCell K) (projection K) (quotientOnLG K).map
    (LagrangianSymplecticAction.lagrangianUniversal_annihilates K)
    (quotientOnLG K).finiteLocallyFree.isFiniteLocallyFree (pulledIntrinsic_isIso K)

end M9Native.LagrangianBigCellPullbackCotangent
