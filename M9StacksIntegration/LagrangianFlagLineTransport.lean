module

public import M9StacksIntegration.LagrangianFlagCompatibility
public import M9StacksIntegration.FlagThreeQuotient
public import M9StacksIntegration.LagrangianGrassmannian

/-!
# Original named quotient lines under the actual two flag towers

The native Grassmannian/flag isomorphism carries all three original
positive quotient lines. Each comparison is the specialization of the
proved all-test quotient or kernel-line comparison; no line-isomorphism
or Chern-root identification is supplied as a premise.
-/

@[expose] public noncomputable section
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 500000
set_option maxRecDepth 4096

open AlgebraicGeometry CategoryTheory Stacks.FlagTower

universe u

namespace M9Native.LagrangianFlagLineTransport

variable (K : Type u) [Field K]

/-- The original native rank-six free sheaf. -/
abbrev freeSix : (Spec (.of K)).Modules := freeModule 6 (Spec (.of K))

local instance freeSixFinite : SheafOfModules.IsFiniteLocallyFree.{u,u,u} (freeSix K) :=
  isFiniteLocallyFree_freeModule 6 (Spec (.of K))

/-- Local freeness is derived from the original universal quotient's actual rank three. -/
local instance quotientFinite :
    SheafOfModules.IsFiniteLocallyFree.{u,u,u} (LagrangianGrassmannian.quotientBundle K) :=
  (LagrangianGrassmannian.quotientBundle_rank K).isFiniteLocallyFree

/-- The actual original two-tower scheme isomorphism. -/
def comparison : FlagThreeQuotient.space (LagrangianGrassmannian.quotientBundle K) ≅
    FlagThreeQuotient.space (freeSix K) :=
  flagTowerIso 3 6 (Spec (.of K)) (by decide)

/-- The actual structure maps commute with that genuine isomorphism. -/
theorem comparison_over :
    (comparison K).hom ≫ FlagThreeQuotient.projection (freeSix K) =
      FlagThreeQuotient.projection (LagrangianGrassmannian.quotientBundle K) ≫
        LagrangianGrassmannian.grassmannianProjection K :=
  flagTowerIso_hom_comp 3 6 (Spec (.of K)) (by decide)

/-- The literal first positive quotient line is preserved. -/
def firstLineIso :
    (Scheme.Modules.pullback (comparison K).hom).obj
      (FlagThreeQuotient.line1 (freeSix K)) ≅
        FlagThreeQuotient.line1 (LagrangianGrassmannian.quotientBundle K) :=
  LagrangianDegree.flagTowerUniversalQuotientIso 3 6 (Spec (.of K)) (by decide) 0

/-- The literal middle kernel line is preserved. -/
def secondLineIso :
    (Scheme.Modules.pullback (comparison K).hom).obj
      (FlagThreeQuotient.line2 (freeSix K)) ≅
        FlagThreeQuotient.line2 (LagrangianGrassmannian.quotientBundle K) :=
  LagrangianDegree.flagTowerUniversalKernelLineIso 3 6 (Spec (.of K)) (by decide)
    (show (0 : Fin 3) ≤ 1 by decide)

/-- The literal last kernel line is preserved. -/
def thirdLineIso :
    (Scheme.Modules.pullback (comparison K).hom).obj
      (FlagThreeQuotient.line3 (freeSix K)) ≅
        FlagThreeQuotient.line3 (LagrangianGrassmannian.quotientBundle K) :=
  LagrangianDegree.flagTowerUniversalKernelLineIso 3 6 (Spec (.of K)) (by decide)
    (show (1 : Fin 3) ≤ 2 by decide)

end M9Native.LagrangianFlagLineTransport
