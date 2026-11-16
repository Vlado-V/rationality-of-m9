module

public import M9StacksIntegration.ChowFlagThreeStages
public import M9StacksIntegration.ChowProjectiveTensorInput

/-!
# The three original normalized tensor-cap inputs on a rank-ten flag

Each class is formed by an actual top-Chern cap, an original
tautological cap power, and the actual projective flat pullback. The
exponents are two, one and zero, respectively. No pushforward identity
or flag input comparison is part of these definitions.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
set_option maxRecDepth 4096
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Stacks.Chow
universe u
namespace M9Native.ChowFlagThreeInputs
open ChowFlagThreeStages ChowProjectiveTensorInput

local instance actualHasKernels {T : Scheme.{u}} : HasKernels T.Modules := inferInstance
local instance actualHasKernel {T : Scheme.{u}} {A B : T.Modules} (f : A ⟶ B) : HasKernel f :=
  HasKernels.has_limit f

variable {X : Scheme.{u}} (D : X.Modules)
    [hD : SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} D 10]
    (F : X.Modules) [hF : SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} F 10]

local instance sourceFinite : SheafOfModules.IsFiniteLocallyFree.{u,u,u} D :=
  hD.isFiniteLocallyFree
local instance kernel1Rank : SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} (kernel1 D) 9 :=
  Stacks.Chow.isFiniteLocallyFreeOfRank_kernel_bundleTautological D 9 hD
local instance kernel1Finite : SheafOfModules.IsFiniteLocallyFree.{u,u,u} (kernel1 D) :=
  (kernel1Rank D).isFiniteLocallyFree
local instance kernel2Rank : SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} (kernel2 D) 8 :=
  Stacks.Chow.isFiniteLocallyFreeOfRank_kernel_bundleTautological (kernel1 D) 8 (kernel1Rank D)
local instance kernel2Finite : SheafOfModules.IsFiniteLocallyFree.{u,u,u} (kernel2 D) :=
  (kernel2Rank D).isFiniteLocallyFree
local instance projection1LFT : LocallyOfFiniteType (projection1 D) :=
  @Stacks.Chow.locallyOfFiniteType_bundleProj X D 9 hD
local instance projection2LFT : LocallyOfFiniteType (projection2 D) :=
  @Stacks.Chow.locallyOfFiniteType_bundleProj (space1 D) (kernel1 D) 8 (kernel1Rank D)
local instance projection3LFT : LocallyOfFiniteType (projection3 D) :=
  @Stacks.Chow.locallyOfFiniteType_bundleProj (space2 D) (kernel2 D) 7 (kernel2Rank D)
local instance originalProjectionLFT : LocallyOfFiniteType (FlagThreeQuotient.projection D) := by
  rw [ChowFlagThreeStages.originalProjection_eq]
  infer_instance
local instance target1Rank : SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} (target1 D F) 10 :=
  AlgebraicGeometry.isFiniteLocallyFreeOfRank_pullback (projection1 D) F 10
local instance target2Rank : SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} (target2 D F) 10 :=
  AlgebraicGeometry.isFiniteLocallyFreeOfRank_pullback (projection2 D) (target1 D F) 10

variable (C : ChowSituation.{u}) (q : X ⟶ C.S) [LocallyOfFiniteType q]

/-- The outer actual top-Chern input, with original exponent two. -/
def outerTensorInput (k : ℤ) (α : chowGroup C q k) :
    chowGroup C (baseMap1 D C q) (k-3) :=
  @tensorInput X D 9 hD F 10 hF C q inferInstance 2 3 (by decide) k α

/-- The middle actual top-Chern input, with original exponent one. -/
def middleTensorInput (k : ℤ) (α : chowGroup C q k) :
    chowGroup C (baseMap2 D C q) ((k-3)-3) :=
  @tensorInput (space1 D) (kernel1 D) 8 (kernel1Rank D)
    (target1 D F) 10 (target1Rank D F) C (baseMap1 D C q) inferInstance
    1 3 (by decide) (k-3) (outerTensorInput D F C q k α)

/-- The three actual inputs composed on the original native flag.
The sole final grade cast identifies k−3−3−3 with k−9. -/
def normalTensorInput (k : ℤ) (α : chowGroup C q k) :
    chowGroup C (baseMap3 D C q) (k-9) :=
  chowGroupCast C (baseMap3 D C q) (by omega)
    (@tensorInput (space2 D) (kernel2 D) 7 (kernel2Rank D)
      (target2 D F) 10 (target2Rank D F) C (baseMap2 D C q) inferInstance
      0 3 (by decide) ((k-3)-3) (middleTensorInput D F C q k α))

theorem normalTensorInput_heq_raw (k : ℤ) (α : chowGroup C q k) :
    normalTensorInput D F C q k α ≍
      @tensorInput (space2 D) (kernel2 D) 7 (kernel2Rank D)
        (target2 D F) 10 (target2Rank D F) C (baseMap2 D C q) inferInstance
        0 3 (by decide) ((k-3)-3) (middleTensorInput D F C q k α) :=
  chowGroupCast_heq C (baseMap3 D C q) _ _

/-- The same actual class on the original flag structure morphism,
transported only by the proved equality of original morphisms. -/
def normalTensorInputOnOriginalFlag (k : ℤ) (α : chowGroup C q k) :
    chowGroup C (FlagThreeQuotient.projection D ≫ q) (k-9) :=
  structureMapCast C (baseMap3 D C q) (FlagThreeQuotient.projection D ≫ q)
    (baseMap3_eq_original D C q) (k-9) (normalTensorInput D F C q k α)

theorem normalTensorInputOnOriginalFlag_heq (k : ℤ) (α : chowGroup C q k) :
    normalTensorInputOnOriginalFlag D F C q k α ≍ normalTensorInput D F C q k α :=
  structureMapCast_heq C (baseMap3 D C q) (FlagThreeQuotient.projection D ≫ q)
    (baseMap3_eq_original D C q) (k-9) _

end M9Native.ChowFlagThreeInputs
