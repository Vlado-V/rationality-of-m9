module

public import M9StacksIntegration.FlagThreeIdentityLines
public import M9StacksIntegration.RankThreeFlagDeterminant
public import M9StacksIntegration.LagrangianGrassmannian

/-!
# The actual determinant on the original full quotient flag

The actual two flag rows determine its three named line factors. In
rank three the final quotient is the original pulled bundle, with the
original normalized quotient map. The resulting determinant isomorphism
retains those actual lines and the original bundle pullback.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
set_option maxRecDepth 4096

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace M9Native.LagrangianFlagDeterminant

open FlagThreeQuotient M9Native.MukaiBundle M9Native.MukaiBundleDeterminant

variable {X : Scheme.{u}} (D : X.Modules)
  [SheafOfModules.IsFiniteLocallyFree.{u,u,u} D]

local instance line1Rank :
    SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} (line1 D) 1 := line1_rank D
local instance line2Rank :
    SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} (line2 D) 1 := line2_rank D
local instance line3Rank :
    SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} (line3 D) 1 := line3_rank D
local instance quotient2Rank :
    SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} (quotientBundle D 1) 2 := by
  simpa using quotientBundle_rank D (1 : Fin 3)
local instance quotient3Rank :
    SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} (quotientBundle D 2) 3 := by
  simpa using quotientBundle_rank D (2 : Fin 3)

/-- The determinant of the original rank-three flag quotient has the actual three factors. -/
def quotientDeterminantIso :
    topExterior (quotientBundle D 2) 3 ≅ tensor (tensor (line1 D) (line2 D)) (line3 D) :=
  RankThreeFlagDeterminant.rankThreeDetIso
    (line1 D) (line2 D) (line3 D) (quotientBundle D 1) (quotientBundle D 2)
    (kernel.ι (step21 D)) (step21 D) (kernel.condition (step21 D)) (sequence21_shortExact D)
    (kernel.ι (step32 D)) (step32 D) (kernel.condition (step32 D)) (sequence32_shortExact D)

/-- For a full rank-three flag the original pulled determinant is the same actual tensor. -/
def pulledDeterminantIso
    [SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} D 3] :
    (Scheme.Modules.pullback (projection D)).obj (topExterior D 3) ≅
      tensor (tensor (line1 D) (line2 D)) (line3 D) :=
  LagrangianPullback.exteriorPullbackIso (projection D) D 3 ≪≫
    (Scheme.Modules.exteriorPowerFunctor (space D) 3).mapIso
      (FlagThreeTautological.fullQuotientIso D).symm ≪≫
    quotientDeterminantIso D

end M9Native.LagrangianFlagDeterminant
