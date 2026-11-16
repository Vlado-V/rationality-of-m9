module

public import M9StacksIntegration.FlagThreeIdentityLines
public import M9StacksIntegration.ChowProjectiveMoments
public import M9StacksIntegration.ChowLineProperPush
public import M9StacksIntegration.LineFamilyCapPower

/-!
# Genuine rank-three flag normalization on every Chow class

The positive original flag lines give the normalizer ξ₁² ξ₂. Its
successive actual proper pushforwards undo the actual three flat
pullbacks, by native projective-bundle normalization in relative
dimensions zero, one, and two. No pushforward identity is an input.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1600000
set_option maxRecDepth 4096

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Stacks.Chow

universe u

namespace M9Native.ChowFlagThreeNormalizer

open ChowCapWords GradedLineCapSubring

section ProperCaps

variable (C : ChowSituation.{u}) {Y Z : Scheme.{u}}
    (qY : Y ⟶ C.S) [LocallyOfFiniteType qY]
    (qZ : Z ⟶ C.S) [LocallyOfFiniteType qZ]
    (p : Y ⟶ Z) [IsProper p] (hp : p ≫ qZ = qY)

theorem properPush_heq {a b : ℤ} (hab : a=b)
    {x : chowGroup C qY a} {y : chowGroup C qY b} (hxy : x ≍ y) :
    ChowLineProperPush.properPush C qY qZ p hp a x ≍
      ChowLineProperPush.properPush C qY qZ p hp b y := by
  cases hab
  cases hxy
  rfl

theorem capPow_input_heq (ξ : ChernCapOperator C qY) (s : ℕ) (a b m : ℤ)
    (ha : a=m+(s:ℤ)) (hb : b=m+(s:ℤ)) (hab : a=b)
    {x : chowGroup C qY a} {y : chowGroup C qY b} (hxy : x ≍ y) :
    capPow C qY ξ s a m ha x = capPow C qY ξ s b m hb y := by
  cases hab
  cases hxy
  rfl

/-- Powers of the SAME genuine pulled line commute with actual proper
pushforward. The line-family/capPow identification is proved, not assumed. -/
theorem properPush_capPow (L : InvertibleLine Z) (L' : InvertibleLine Y)
    (e : L'.1 ≅ (Scheme.Modules.pullback p).obj L.1)
    (s : ℕ) (a m : ℤ) (h : a=m+(s:ℤ)) (x : chowGroup C qY a) :
    ChowLineProperPush.properPush C qY qZ p hp m
        (capPow C qY (lineCap C qY L') s a m h x) =
      capPow C qZ (lineCap C qZ L) s a m h
        (ChowLineProperPush.properPush C qY qZ p hp a x) := by
  apply eq_of_heq
  refine (properPush_heq C qY qZ p hp (show m=a-(s:ℤ) by omega)
    (LineFamilyCapPower.lineFamily_pow_apply_heq C qY L' s a m h x).symm).trans ?_
  refine (heq_of_eq (ChowLineProperPush.properPush_lineFamily_pow_apply
    C qY qZ p hp L L' e s a s x)).trans ?_
  exact LineFamilyCapPower.lineFamily_pow_apply_heq C qZ L s a m h _

end ProperCaps

local instance actualHasKernels {T : Scheme.{u}} : HasKernels T.Modules := inferInstance
local instance actualHasKernel {T : Scheme.{u}} {A B : T.Modules} (f : A ⟶ B) :
    HasKernel f := HasKernels.has_limit f

variable {X : Scheme.{u}} (D : X.Modules)
    [hD : SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} D 3]

local instance sourceFinite : SheafOfModules.IsFiniteLocallyFree.{u,u,u} D :=
  hD.isFiniteLocallyFree

abbrev space1 : Scheme.{u} := FlagThreeIdentityLines.space1 D
abbrev kernel1 : (space1 D).Modules := FlagThreeIdentityLines.kernel1 D
local instance kernel1Rank :
    SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} (kernel1 D) 2 :=
  Stacks.Chow.isFiniteLocallyFreeOfRank_kernel_bundleTautological D 2 hD
local instance kernel1Finite : SheafOfModules.IsFiniteLocallyFree.{u,u,u} (kernel1 D) :=
  (kernel1Rank D).isFiniteLocallyFree
abbrev space2 : Scheme.{u} := FlagThreeIdentityLines.space2 D
abbrev kernel2 : (space2 D).Modules := FlagThreeIdentityLines.kernel2 D
local instance kernel2Rank :
    SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} (kernel2 D) 1 :=
  Stacks.Chow.isFiniteLocallyFreeOfRank_kernel_bundleTautological (kernel1 D) 1 (kernel1Rank D)
local instance kernel2Finite : SheafOfModules.IsFiniteLocallyFree.{u,u,u} (kernel2 D) :=
  (kernel2Rank D).isFiniteLocallyFree
abbrev space3 : Scheme.{u} := FlagThreeIdentityLines.space3 D
abbrev projection1 : space1 D ⟶ X := bundleProj D
abbrev projection2 : space2 D ⟶ space1 D := FlagThreeIdentityLines.projection2 D
abbrev projection3 : space3 D ⟶ space2 D := FlagThreeIdentityLines.projection3 D

local instance projection1Flat : Flat (projection1 D) := @flat_bundleProj X D 2 hD
local instance projection2Flat : Flat (projection2 D) :=
  @flat_bundleProj (space1 D) (kernel1 D) 1 (kernel1Rank D)
local instance projection3Flat : Flat (projection3 D) :=
  @flat_bundleProj (space2 D) (kernel2 D) 0 (kernel2Rank D)
local instance projection1LFT : LocallyOfFiniteType (projection1 D) :=
  @locallyOfFiniteType_bundleProj X D 2 hD
local instance projection2LFT : LocallyOfFiniteType (projection2 D) :=
  @locallyOfFiniteType_bundleProj (space1 D) (kernel1 D) 1 (kernel1Rank D)
local instance projection3LFT : LocallyOfFiniteType (projection3 D) :=
  @locallyOfFiniteType_bundleProj (space2 D) (kernel2 D) 0 (kernel2Rank D)

variable (C : ChowSituation.{u}) (q : X ⟶ C.S) [LocallyOfFiniteType q]

abbrev baseMap1 : space1 D ⟶ C.S := projection1 D ≫ q
abbrev baseMap2 : space2 D ⟶ C.S := projection2 D ≫ baseMap1 D C q
abbrev baseMap3 : space3 D ⟶ C.S := projection3 D ≫ baseMap2 D C q

def pull1 (k : ℤ) : chowGroup C q k →+ chowGroup C (baseMap1 D C q) (k+2) :=
  bundlePullback C q (baseMap1 D C q) (projection1 D) rfl 2
    (@relativeDimension_bundleProj X D 2 hD) k

def pull2 (k : ℤ) :
    chowGroup C (baseMap1 D C q) k →+ chowGroup C (baseMap2 D C q) (k+1) :=
  bundlePullback C (baseMap1 D C q) (baseMap2 D C q) (projection2 D) rfl 1
    (@relativeDimension_bundleProj (space1 D) (kernel1 D) 1 (kernel1Rank D)) k

/-- The third genuine flat pullback has relative dimension zero.
The only extra map is the native k+0=k degree cast. -/
def pull3 (k : ℤ) :
    chowGroup C (baseMap2 D C q) k →+ chowGroup C (baseMap3 D C q) k :=
  (gradedDegreeCast (chowGroup C (baseMap3 D C q)) (show k+0=k by omega)).toAddMonoidHom.comp
    (bundlePullback C (baseMap2 D C q) (baseMap3 D C q) (projection3 D) rfl 0
      (@relativeDimension_bundleProj (space2 D) (kernel2 D) 0 (kernel2Rank D)) k)

abbrev push1 (k : ℤ) : chowGroup C (baseMap1 D C q) k →+ chowGroup C q k :=
  ChowLineProperPush.properPush C (baseMap1 D C q) q (projection1 D) rfl k
abbrev push2 (k : ℤ) :
    chowGroup C (baseMap2 D C q) k →+ chowGroup C (baseMap1 D C q) k :=
  ChowLineProperPush.properPush C (baseMap2 D C q) (baseMap1 D C q) (projection2 D) rfl k
abbrev push3 (k : ℤ) :
    chowGroup C (baseMap3 D C q) k →+ chowGroup C (baseMap2 D C q) k :=
  ChowLineProperPush.properPush C (baseMap3 D C q) (baseMap2 D C q) (projection3 D) rfl k

def triplePush (k : ℤ) : chowGroup C (baseMap3 D C q) k →+ chowGroup C q k :=
  (push1 D C q k).comp ((push2 D C q k).comp (push3 D C q k))

def firstLine : InvertibleLine (space1 D) := ⟨bundleTwist D, isInvertible_bundleTwist D⟩
def secondLine : InvertibleLine (space2 D) :=
  ⟨bundleTwist (kernel1 D), isInvertible_bundleTwist (kernel1 D)⟩
def firstLineAt2 : InvertibleLine (space2 D) := by
  letI := (firstLine D).2
  exact ⟨(Scheme.Modules.pullback (projection2 D)).obj (firstLine D).1,
    GenuineChern.isInvertible_pullback (projection2 D) (firstLine D).1⟩

local instance flagLine1Rank :
    SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} (FlagThreeQuotient.line1 D) 1 :=
  FlagThreeQuotient.line1_rank D
local instance flagLine2Rank :
    SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} (FlagThreeQuotient.line2 D) 1 :=
  FlagThreeQuotient.line2_rank D

/-- The ORIGINAL first positive flag line, not a chosen root. -/
def flagLine1 : InvertibleLine (space3 D) :=
  ⟨FlagThreeQuotient.line1 D, GenuineChern.isInvertible_of_rank_one _⟩
/-- The ORIGINAL second positive flag line. -/
def flagLine2 : InvertibleLine (space3 D) :=
  ⟨FlagThreeQuotient.line2 D, GenuineChern.isInvertible_of_rank_one _⟩

/-- All three literal projective flat pullbacks, of dimensions 2,1,0. -/
def flatPullClass (k : ℤ) (α : chowGroup C q k) :
    chowGroup C (baseMap3 D C q) (k+3) :=
  gradedDegreeCast (chowGroup C (baseMap3 D C q)) (by omega)
    (pull3 D C q ((k+2)+1) (pull2 D C q (k+2) (pull1 D C q k α)))

/-- The actual native cap word ξ₁² ξ₂ on the actual full flat pullback. -/
def normalClass (k : ℤ) (α : chowGroup C q k) : chowGroup C (baseMap3 D C q) k :=
  capPow C (baseMap3 D C q) (lineCap C (baseMap3 D C q) (flagLine1 D)) 2 (k+2) k (by omega)
    (capPow C (baseMap3 D C q) (lineCap C (baseMap3 D C q) (flagLine2 D))
      1 (k+3) (k+2) (by omega) (flatPullClass D C q k α))

/-- Native top-power normalization at the first actual projective stage. -/
theorem push1_top (k : ℤ) (α : chowGroup C q k) :
    push1 D C q k
      (capPow C (baseMap1 D C q) (lineCap C (baseMap1 D C q) (firstLine D))
        2 (k+2) k (by omega) (pull1 D C q k α)) = α :=
  projectiveBundle_projection_self D 2 C q k α

/-- Native top-power normalization at the second actual projective stage. -/
theorem push2_top (k : ℤ) (α : chowGroup C (baseMap1 D C q) k) :
    push2 D C q k
      (capPow C (baseMap2 D C q) (lineCap C (baseMap2 D C q) (secondLine D))
        1 (k+1) k (by omega) (pull2 D C q k α)) = α :=
  @projectiveBundle_projection_self (space1 D) (kernel1 D) 1 (kernel1Rank D)
    C (baseMap1 D C q) inferInstance k α

/-- Native zero-dimensional projective normalization gives the third
push-pull identity, including the real zero-grade transport. -/
theorem push3_pull3 (k : ℤ) (α : chowGroup C (baseMap2 D C q) k) :
    push3 D C q k (pull3 D C q k α) = α := by
  have h := @projectiveBundle_projection_self (space2 D) (kernel2 D) 0 (kernel2Rank D)
    C (baseMap2 D C q) inferInstance k α
  change push3 D C q k
    (capPow C (baseMap3 D C q)
      (invCap C (baseMap3 D C q) (bundleTwist (kernel2 D)))
      0 (k+0) k (by omega)
      (bundlePullback C (baseMap2 D C q) (baseMap3 D C q) (projection3 D) rfl 0
        (@relativeDimension_bundleProj (space2 D) (kernel2 D) 0 (kernel2Rank D)) k α)) = α at h
  rw [capPow_zero_apply] at h
  exact h

/-- The original full pullback becomes the first two actual pullbacks
after the third proper push; no fiber/fundamental formula is assumed. -/
theorem push3_flatPullClass (k : ℤ) (α : chowGroup C q k) :
    push3 D C q (k+3) (flatPullClass D C q k α) ≍
      pull2 D C q (k+2) (pull1 D C q k α) := by
  refine (properPush_heq C (baseMap3 D C q) (baseMap2 D C q) (projection3 D) rfl
    (show k+3=(k+2)+1 by omega) (gradedDegreeCast_heq _ _)).trans ?_
  exact heq_of_eq (push3_pull3 D C q ((k+2)+1) _)

/-- The genuine three-stage flag normalizer integrates to one on EVERY
original Chow class. Actual line pullback and native top powers prove it. -/
theorem triplePush_normalClass (k : ℤ) (α : chowGroup C q k) :
    triplePush D C q k (normalClass D C q k α) = α := by
  have h31 := properPush_capPow C (baseMap3 D C q) (baseMap2 D C q)
    (projection3 D) rfl (firstLineAt2 D) (flagLine1 D)
    (FlagThreeIdentityLines.line1Iso D) 2 (k+2) k (by omega)
    (capPow C (baseMap3 D C q) (lineCap C (baseMap3 D C q) (flagLine2 D))
      1 (k+3) (k+2) (by omega) (flatPullClass D C q k α))
  have h32 := properPush_capPow C (baseMap3 D C q) (baseMap2 D C q)
    (projection3 D) rfl (secondLine D) (flagLine2 D)
    (FlagThreeIdentityLines.line2Iso D) 1 (k+3) (k+2) (by omega) (flatPullClass D C q k α)
  have h2 := properPush_capPow C (baseMap2 D C q) (baseMap1 D C q)
    (projection2 D) rfl (firstLine D) (firstLineAt2 D) (Iso.refl _)
    2 (k+2) k (by omega)
    (capPow C (baseMap2 D C q) (lineCap C (baseMap2 D C q) (secondLine D))
      1 (k+3) (k+2) (by omega)
      (push3 D C q (k+3) (flatPullClass D C q k α)))
  have htop : push2 D C q (k+2)
      (capPow C (baseMap2 D C q) (lineCap C (baseMap2 D C q) (secondLine D))
        1 (k+3) (k+2) (by omega)
        (push3 D C q (k+3) (flatPullClass D C q k α))) = pull1 D C q k α := by
    apply eq_of_heq
    refine (heq_of_eq (congrArg (push2 D C q (k+2))
      (capPow_input_heq C (baseMap2 D C q) (lineCap C (baseMap2 D C q) (secondLine D))
        1 (k+3) ((k+2)+1) (k+2) (by omega) (by omega) (by omega)
        (push3_flatPullClass D C q k α)))).trans ?_
    exact heq_of_eq (push2_top D C q (k+2) (pull1 D C q k α))
  change push1 D C q k (push2 D C q k (push3 D C q k (normalClass D C q k α))) = α
  change push1 D C q k (push2 D C q k
    (ChowLineProperPush.properPush C (baseMap3 D C q) (baseMap2 D C q)
      (projection3 D) rfl k _)) = α
  dsimp only [normalClass]
  rw [h31, h32, h2, htop]
  exact push1_top D C q k α

/-- The iterated pushforward spelling of the same actual identity. -/
theorem push1_push2_push3_normalClass (k : ℤ) (α : chowGroup C q k) :
    push1 D C q k (push2 D C q k (push3 D C q k (normalClass D C q k α))) = α :=
  triplePush_normalClass D C q k α

end M9Native.ChowFlagThreeNormalizer
