module

public import M9StacksIntegration.LagrangianProjectivePowerPush
public import M9StacksIntegration.FlagThreeIdentityLines
public import M9StacksIntegration.ChowFlagThreeNormalizer

/-!
# The original rank-six quotient-flag power classes

The three spaces are the native projective bundles of E, its original
tautological kernel, and that kernel's original tautological kernel.
All maps, powers, flat pullbacks and proper pushforwards below are the
original native operations. No numerical push value is a definition.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
set_option maxRecDepth 4096
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Stacks.Chow
universe u
namespace M9Native.LagrangianFlagPowerStages
open ChowCapWords GradedLineCapSubring

local instance actualHasKernels {T : Scheme.{u}} : HasKernels T.Modules := inferInstance
local instance actualHasKernel {T : Scheme.{u}} {A B : T.Modules} (f : A ⟶ B) : HasKernel f :=
  HasKernels.has_limit f

variable {X : Scheme.{u}} (E : X.Modules)
    [hE : SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} E 6]
local instance sourceFinite : SheafOfModules.IsFiniteLocallyFree.{u,u,u} E :=
  hE.isFiniteLocallyFree

abbrev space1 : Scheme.{u} := FlagThreeIdentityLines.space1 E
abbrev kernel1 : (space1 E).Modules := FlagThreeIdentityLines.kernel1 E
local instance kernel1Rank : SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} (kernel1 E) 5 :=
  Stacks.Chow.isFiniteLocallyFreeOfRank_kernel_bundleTautological E 5 hE
local instance kernel1Finite : SheafOfModules.IsFiniteLocallyFree.{u,u,u} (kernel1 E) :=
  (kernel1Rank E).isFiniteLocallyFree
abbrev space2 : Scheme.{u} := FlagThreeIdentityLines.space2 E
abbrev kernel2 : (space2 E).Modules := FlagThreeIdentityLines.kernel2 E
local instance kernel2Rank : SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} (kernel2 E) 4 :=
  Stacks.Chow.isFiniteLocallyFreeOfRank_kernel_bundleTautological (kernel1 E) 4 (kernel1Rank E)
local instance kernel2Finite : SheafOfModules.IsFiniteLocallyFree.{u,u,u} (kernel2 E) :=
  (kernel2Rank E).isFiniteLocallyFree
abbrev space3 : Scheme.{u} := FlagThreeIdentityLines.space3 E
abbrev projection1 : space1 E ⟶ X := bundleProj E
abbrev projection2 : space2 E ⟶ space1 E := FlagThreeIdentityLines.projection2 E
abbrev projection3 : space3 E ⟶ space2 E := FlagThreeIdentityLines.projection3 E

local instance projection1Flat : Flat (projection1 E) := @flat_bundleProj X E 5 hE
local instance projection2Flat : Flat (projection2 E) :=
  @flat_bundleProj (space1 E) (kernel1 E) 4 (kernel1Rank E)
local instance projection3Flat : Flat (projection3 E) :=
  @flat_bundleProj (space2 E) (kernel2 E) 3 (kernel2Rank E)
local instance projection1LFT : LocallyOfFiniteType (projection1 E) :=
  @locallyOfFiniteType_bundleProj X E 5 hE
local instance projection2LFT : LocallyOfFiniteType (projection2 E) :=
  @locallyOfFiniteType_bundleProj (space1 E) (kernel1 E) 4 (kernel1Rank E)
local instance projection3LFT : LocallyOfFiniteType (projection3 E) :=
  @locallyOfFiniteType_bundleProj (space2 E) (kernel2 E) 3 (kernel2Rank E)

def firstLine : InvertibleLine (space1 E) :=
  ⟨bundleTwist E, isInvertible_bundleTwist E⟩
def secondLine : InvertibleLine (space2 E) :=
  ⟨bundleTwist (kernel1 E), isInvertible_bundleTwist (kernel1 E)⟩
def thirdLine : InvertibleLine (space3 E) :=
  ⟨bundleTwist (kernel2 E), isInvertible_bundleTwist (kernel2 E)⟩
def firstLineAt2 : InvertibleLine (space2 E) := by
  letI := (firstLine E).2
  exact ⟨(Scheme.Modules.pullback (projection2 E)).obj (firstLine E).1,
    GenuineChern.isInvertible_pullback (projection2 E) (firstLine E).1⟩
def firstLineAt3 : InvertibleLine (space3 E) := by
  letI := (firstLineAt2 E).2
  exact ⟨(Scheme.Modules.pullback (projection3 E)).obj (firstLineAt2 E).1,
    GenuineChern.isInvertible_pullback (projection3 E) (firstLineAt2 E).1⟩
def secondLineAt3 : InvertibleLine (space3 E) := by
  letI := (secondLine E).2
  exact ⟨(Scheme.Modules.pullback (projection3 E)).obj (secondLine E).1,
    GenuineChern.isInvertible_pullback (projection3 E) (secondLine E).1⟩

/-- Positive quotient roots, in the original first/second/third order. -/
def positiveLines : Fin 3 → InvertibleLine (space3 E) :=
  ![firstLineAt3 E, secondLineAt3 E, thirdLine E]

def first_original_iso : (positiveLines E 0).1 ≅ FlagThreeQuotient.line1 E :=
  (FlagThreeIdentityLines.line1Iso E).symm
def second_original_iso : (positiveLines E 1).1 ≅ FlagThreeQuotient.line2 E :=
  (FlagThreeIdentityLines.line2Iso E).symm
def third_original_iso : (positiveLines E 2).1 ≅ FlagThreeQuotient.line3 E :=
  (FlagThreeIdentityLines.line3Iso E).symm

variable (C : ChowSituation.{u}) (q : X ⟶ C.S) [LocallyOfFiniteType q]
abbrev baseMap1 : space1 E ⟶ C.S := projection1 E ≫ q
abbrev baseMap2 : space2 E ⟶ C.S := projection2 E ≫ baseMap1 E C q
abbrev baseMap3 : space3 E ⟶ C.S := projection3 E ≫ baseMap2 E C q

def pull1 (k : ℤ) : chowGroup C q k →+ chowGroup C (baseMap1 E C q) (k+5) :=
  bundlePullback C q (baseMap1 E C q) (projection1 E) rfl 5
    (@relativeDimension_bundleProj X E 5 hE) k
def pull2 (k : ℤ) :
    chowGroup C (baseMap1 E C q) k →+ chowGroup C (baseMap2 E C q) (k+4) :=
  bundlePullback C (baseMap1 E C q) (baseMap2 E C q) (projection2 E) rfl 4
    (@relativeDimension_bundleProj (space1 E) (kernel1 E) 4 (kernel1Rank E)) k
def pull3 (k : ℤ) :
    chowGroup C (baseMap2 E C q) k →+ chowGroup C (baseMap3 E C q) (k+3) :=
  bundlePullback C (baseMap2 E C q) (baseMap3 E C q) (projection3 E) rfl 3
    (@relativeDimension_bundleProj (space2 E) (kernel2 E) 3 (kernel2Rank E)) k

abbrev push1 (k : ℤ) : chowGroup C (baseMap1 E C q) k →+ chowGroup C q k :=
  ChowLineProperPush.properPush C (baseMap1 E C q) q (projection1 E) rfl k
abbrev push2 (k : ℤ) :
    chowGroup C (baseMap2 E C q) k →+ chowGroup C (baseMap1 E C q) k :=
  ChowLineProperPush.properPush C (baseMap2 E C q) (baseMap1 E C q) (projection2 E) rfl k
abbrev push3 (k : ℤ) :
    chowGroup C (baseMap3 E C q) k →+ chowGroup C (baseMap2 E C q) k :=
  ChowLineProperPush.properPush C (baseMap3 E C q) (baseMap2 E C q) (projection3 E) rfl k
def triplePush (k : ℤ) : chowGroup C (baseMap3 E C q) k →+ chowGroup C q k :=
  (push1 E C q k).comp ((push2 E C q k).comp (push3 E C q k))

/-- The actual full flat pullback, in its literal twelve-dimensional degree shift. -/
def flatPullClass (k : ℤ) (α : chowGroup C q k) :
    chowGroup C (baseMap3 E C q) (k+12) :=
  chowGroupCast C (baseMap3 E C q) (by omega)
    (pull3 E C q ((k+5)+4) (pull2 E C q (k+5) (pull1 E C q k α)))

def powerClass1 (a : ℕ) (k : ℤ) (α : chowGroup C q k) :
    chowGroup C (baseMap1 E C q) (k+5-(a:ℤ)) :=
  capPow C (baseMap1 E C q) (lineCap C (baseMap1 E C q) (firstLine E))
    a (k+5) (k+5-(a:ℤ)) (by omega) (pull1 E C q k α)
def powerClass2 (a b : ℕ) (k : ℤ) (α : chowGroup C q k) :
    chowGroup C (baseMap2 E C q) ((k+5-(a:ℤ))+4-(b:ℤ)) :=
  capPow C (baseMap2 E C q) (lineCap C (baseMap2 E C q) (secondLine E))
    b ((k+5-(a:ℤ))+4) ((k+5-(a:ℤ))+4-(b:ℤ)) (by omega)
    (pull2 E C q (k+5-(a:ℤ)) (powerClass1 E C q a k α))
def powerClass3 (a b c : ℕ) (k : ℤ) (α : chowGroup C q k) :
    chowGroup C (baseMap3 E C q) (((k+5-(a:ℤ))+4-(b:ℤ))+3-(c:ℤ)) :=
  capPow C (baseMap3 E C q) (lineCap C (baseMap3 E C q) (thirdLine E))
    c (((k+5-(a:ℤ))+4-(b:ℤ))+3) (((k+5-(a:ℤ))+4-(b:ℤ))+3-(c:ℤ)) (by omega)
    (pull3 E C q ((k+5-(a:ℤ))+4-(b:ℤ)) (powerClass2 E C q a b k α))

theorem push1_powerClass (a : ℕ) (k : ℤ) (α : chowGroup C q k) :
    push1 E C q (k+5-(a:ℤ)) (powerClass1 E C q a k α) =
      LagrangianProjectivePowerPush.powerPush E 5 C q a k α := rfl

theorem push2_powerClass (a b : ℕ) (k : ℤ) (α : chowGroup C q k) :
    push2 E C q ((k+5-(a:ℤ))+4-(b:ℤ)) (powerClass2 E C q a b k α) =
      @LagrangianProjectivePowerPush.powerPush (space1 E) (kernel1 E) 4 (kernel1Rank E)
        C (baseMap1 E C q) inferInstance b (k+5-(a:ℤ)) (powerClass1 E C q a k α) := rfl

theorem push3_powerClass (a b c : ℕ) (k : ℤ) (α : chowGroup C q k) :
    push3 E C q (((k+5-(a:ℤ))+4-(b:ℤ))+3-(c:ℤ)) (powerClass3 E C q a b c k α) =
      @LagrangianProjectivePowerPush.powerPush (space2 E) (kernel2 E) 3 (kernel2Rank E)
        C (baseMap2 E C q) inferInstance c ((k+5-(a:ℤ))+4-(b:ℤ))
        (powerClass2 E C q a b k α) := rfl

end M9Native.LagrangianFlagPowerStages
