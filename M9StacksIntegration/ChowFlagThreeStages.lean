module

public import M9StacksIntegration.ChowProjectiveMoments
public import StacksFrontier.AlgebraicGeometry.FlagTower.Tower
public import M9StacksIntegration.FlagThreeQuotient

/-!
# Original rank-ten flag stages and the actual normalizing Chow class

The three projective bundles, their original maps, all pullbacks and
proper pushforwards, and the normalizer are concrete geometric objects.
The normalizer is constructed on every original integer Chow grade;
no Schur or Gysin identity is assumed in these definitions.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
set_option maxRecDepth 4096
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Stacks.Chow
universe u
namespace M9Native.ChowFlagThreeStages

local instance actualHasKernels {T : Scheme.{u}} : HasKernels T.Modules := inferInstance
local instance actualHasKernel {T : Scheme.{u}} {A B : T.Modules} (f : A ⟶ B) : HasKernel f :=
  HasKernels.has_limit f

variable {X : Scheme.{u}} (D : X.Modules)
  [hD : SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} D 10]

local instance sourceFinite : SheafOfModules.IsFiniteLocallyFree.{u,u,u} D :=
  hD.isFiniteLocallyFree

abbrev space1 : Scheme.{u} := bundle D
abbrev kernel1 : (space1 D).Modules := kernel (bundleTautological D)
local instance kernel1Rank :
    SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} (kernel1 D) 9 :=
  Stacks.Chow.isFiniteLocallyFreeOfRank_kernel_bundleTautological D 9 hD
local instance kernel1Finite : SheafOfModules.IsFiniteLocallyFree.{u,u,u} (kernel1 D) :=
  (kernel1Rank D).isFiniteLocallyFree

abbrev space2 : Scheme.{u} := bundle (kernel1 D)
abbrev kernel2 : (space2 D).Modules := kernel (bundleTautological (kernel1 D))
local instance kernel2Rank :
    SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} (kernel2 D) 8 :=
  Stacks.Chow.isFiniteLocallyFreeOfRank_kernel_bundleTautological (kernel1 D) 8 (kernel1Rank D)
local instance kernel2Finite : SheafOfModules.IsFiniteLocallyFree.{u,u,u} (kernel2 D) :=
  (kernel2Rank D).isFiniteLocallyFree

abbrev space3 : Scheme.{u} := bundle (kernel2 D)
abbrev projection1 : space1 D ⟶ X := bundleProj D
abbrev projection2 : space2 D ⟶ space1 D := bundleProj (kernel1 D)
abbrev projection3 : space3 D ⟶ space2 D := bundleProj (kernel2 D)

local instance projection1Flat : Flat (projection1 D) := @Stacks.Chow.flat_bundleProj X D 9 hD
local instance projection2Flat : Flat (projection2 D) :=
  @Stacks.Chow.flat_bundleProj (space1 D) (kernel1 D) 8 (kernel1Rank D)
local instance projection3Flat : Flat (projection3 D) :=
  @Stacks.Chow.flat_bundleProj (space2 D) (kernel2 D) 7 (kernel2Rank D)
local instance projection1LFT : LocallyOfFiniteType (projection1 D) :=
  @Stacks.Chow.locallyOfFiniteType_bundleProj X D 9 hD
local instance projection2LFT : LocallyOfFiniteType (projection2 D) :=
  @Stacks.Chow.locallyOfFiniteType_bundleProj (space1 D) (kernel1 D) 8 (kernel1Rank D)
local instance projection3LFT : LocallyOfFiniteType (projection3 D) :=
  @Stacks.Chow.locallyOfFiniteType_bundleProj (space2 D) (kernel2 D) 7 (kernel2Rank D)

variable (C : ChowSituation.{u}) (q : X ⟶ C.S) [LocallyOfFiniteType q]
abbrev baseMap1 : space1 D ⟶ C.S := projection1 D ≫ q
abbrev baseMap2 : space2 D ⟶ C.S := projection2 D ≫ baseMap1 D C q
abbrev baseMap3 : space3 D ⟶ C.S := projection3 D ≫ baseMap2 D C q

/-- The original first projective flat pullback, in relative dimension nine. -/
def pull1 (k : ℤ) : chowGroup C q k →+ chowGroup C (baseMap1 D C q) (k+9) :=
  bundlePullback C q (baseMap1 D C q) (projection1 D) rfl 9
    (@Stacks.Chow.relativeDimension_bundleProj X D 9 hD) k
/-- The original second projective flat pullback, in relative dimension eight. -/
def pull2 (k : ℤ) :
    chowGroup C (baseMap1 D C q) k →+ chowGroup C (baseMap2 D C q) (k+8) :=
  bundlePullback C (baseMap1 D C q) (baseMap2 D C q) (projection2 D) rfl 8
    (@Stacks.Chow.relativeDimension_bundleProj (space1 D) (kernel1 D) 8 (kernel1Rank D)) k
/-- The original third projective flat pullback, in relative dimension seven. -/
def pull3 (k : ℤ) :
    chowGroup C (baseMap2 D C q) k →+ chowGroup C (baseMap3 D C q) (k+7) :=
  bundlePullback C (baseMap2 D C q) (baseMap3 D C q) (projection3 D) rfl 7
    (@Stacks.Chow.relativeDimension_bundleProj (space2 D) (kernel2 D) 7 (kernel2Rank D)) k

/-- The first literal proper Chow pushforward. -/
def push1 (k : ℤ) : chowGroup C (baseMap1 D C q) k →+ chowGroup C q k :=
  properChowPushforward C (baseMap1 D C q) q (projection1 D) rfl k
    (properPushforwardFactorsThroughRationalEquivalence_of_isProper C _ _ _ rfl k)
/-- The second literal proper Chow pushforward. -/
def push2 (k : ℤ) :
    chowGroup C (baseMap2 D C q) k →+ chowGroup C (baseMap1 D C q) k :=
  properChowPushforward C (baseMap2 D C q) (baseMap1 D C q) (projection2 D) rfl k
    (properPushforwardFactorsThroughRationalEquivalence_of_isProper C _ _ _ rfl k)
/-- The third literal proper Chow pushforward. -/
def push3 (k : ℤ) :
    chowGroup C (baseMap3 D C q) k →+ chowGroup C (baseMap2 D C q) k :=
  properChowPushforward C (baseMap3 D C q) (baseMap2 D C q) (projection3 D) rfl k
    (properPushforwardFactorsThroughRationalEquivalence_of_isProper C _ _ _ rfl k)

/-- The actual successive proper pushes, without a trace or coefficient model. -/
def triplePush (k : ℤ) : chowGroup C (baseMap3 D C q) k →+ chowGroup C q k :=
  (push1 D C q k).comp ((push2 D C q k).comp (push3 D C q k))

/-- The actual normalizer ξ₁² ξ₂, interleaved with the three original
flat pullbacks. It takes degree k to the actual flag degree k+21. -/
def normalClass (k : ℤ) (α : chowGroup C q k) :
    chowGroup C (baseMap3 D C q) (k+21) :=
  gradedDegreeCast (chowGroup C (baseMap3 D C q)) (by omega)
    (pull3 D C q (k+14)
      (capPow C (baseMap2 D C q)
        (invCap C (baseMap2 D C q) (bundleTwist (kernel1 D))) 1 ((k+7)+8) (k+14) (by ring)
        (pull2 D C q (k+7)
          (capPow C (baseMap1 D C q) (invCap C (baseMap1 D C q) (bundleTwist D))
            2 (k+9) (k+7) (by ring) (pull1 D C q k α)))))

/-- Every operation in triplePush is exactly its original proper pushforward. -/
theorem triplePush_apply (k : ℤ) (β : chowGroup C (baseMap3 D C q) k) :
    triplePush D C q k β = push1 D C q k (push2 D C q k (push3 D C q k β)) := rfl


/-- The literal native flag projection is the composite of these
three original projective maps, with no chosen comparison premise. -/
theorem originalProjection_eq :
    FlagThreeQuotient.projection D =
      (projection3 D ≫ projection2 D) ≫ projection1 D := by
  change ((𝟙 _ ≫ projection3 D) ≫ projection2 D) ≫ projection1 D = _
  rw [Category.id_comp]

local instance originalProjectionLFT : LocallyOfFiniteType (FlagThreeQuotient.projection D) := by
  rw [originalProjection_eq]
  infer_instance

/-- The first actual pullback of a target sheaf, with no rank assumption. -/
abbrev target1 (F : X.Modules) : (space1 D).Modules :=
  (Scheme.Modules.pullback (projection1 D)).obj F
/-- The second actual pullback of the same original sheaf. -/
abbrev target2 (F : X.Modules) : (space2 D).Modules :=
  (Scheme.Modules.pullback (projection2 D)).obj (target1 D F)
/-- The third actual pullback of the same original sheaf. -/
abbrev target3 (F : X.Modules) : (space3 D).Modules :=
  (Scheme.Modules.pullback (projection3 D)).obj (target2 D F)

/-- Actual composition of the three original pullback functors,
normalized by the proved ORIGINAL native flag projection. -/
def target3IsoOriginal (F : X.Modules) :
    target3 D F ≅ (Scheme.Modules.pullback (FlagThreeQuotient.projection D)).obj F :=
  (Scheme.Modules.pullbackComp (projection3 D) (projection2 D)).app (target1 D F) ≪≫
    (Scheme.Modules.pullbackComp (projection3 D ≫ projection2 D) (projection1 D)).app F ≪≫
      (Scheme.Modules.pullbackCongr (originalProjection_eq D).symm).app F

/-- The original structure morphism is exactly the one carried through
all three concrete projective stages. -/
theorem baseMap3_eq_original :
    baseMap3 D C q = FlagThreeQuotient.projection D ≫ q := by
  rw [originalProjection_eq]
  simp only [baseMap3, baseMap2, baseMap1, Category.assoc]

/-- The constructed normalizer class on the ORIGINAL native flag and
its original structure morphism. The only transport is their proved
equality of morphisms. -/
def structureMapCast {Y : Scheme.{u}} (f g : Y ⟶ C.S)
    [LocallyOfFiniteType f] [LocallyOfFiniteType g] (h : f=g) (k : ℤ)
    (β : chowGroup C f k) : chowGroup C g k := by
  subst g
  exact β

theorem structureMapCast_heq {Y : Scheme.{u}} (f g : Y ⟶ C.S)
    [LocallyOfFiniteType f] [LocallyOfFiniteType g] (h : f=g) (k : ℤ)
    (β : chowGroup C f k) : structureMapCast C f g h k β ≍ β := by
  subst g
  rfl

def normalClassOnOriginalFlag (k : ℤ) (α : chowGroup C q k) :
    chowGroup C (FlagThreeQuotient.projection D ≫ q) (k+21) :=
  structureMapCast C (baseMap3 D C q) (FlagThreeQuotient.projection D ≫ q)
    (baseMap3_eq_original D C q) (k+21) (normalClass D C q k α)

end M9Native.ChowFlagThreeStages
