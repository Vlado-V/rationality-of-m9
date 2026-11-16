module

public import M9StacksIntegration.ChowFlagThreeNormalizer
public import M9StacksIntegration.LagrangianLinePullback

/-!
# Actual rank-three full-flag flat pullback and Chern naturality

The Chow map is literally the original three projective flat pullbacks
of relative dimensions two, one, and zero. Native Chern flat naturality
at each stage and the actual pullback-composition isomorphisms identify
the target with the original full-projection pullback. Line caps and
all powers inherit this proved naturality. No cap compatibility or
bundle-comparison premise is supplied.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxRecDepth 4096

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Stacks.Chow Stacks.Chow.GenuineChern

universe u v

namespace M9Native.ChowFlagThreePullback

open ChowCapWords GradedLineCapSubring ChowFlagThreeNormalizer

section GradedTransport

variable {G H : ℤ → Type v} [∀ k, AddCommGroup (G k)] [∀ k, AddCommGroup (H k)]

/-- An actual graded additive map preserves heterogeneous equality in equal degrees. -/
theorem shiftedMap_heq {d : ℤ} (p : ∀ k, G k →+ H (k+d))
    {a b : ℤ} (hab : a=b) {x : G a} {y : G b} (hxy : x ≍ y) :
    p a x ≍ p b y := by
  cases hab
  cases hxy
  rfl

/-- The native positive-shift intertwiner, without hiding its degree cast. -/
theorem intertwines_apply_heq {d : ℤ} {p : ∀ k, G k →+ H (k+d)}
    {a : GradedCapFamily G} {b : GradedCapFamily H}
    (h : Stacks.Chow.Intertwines p a b) (k : ℤ) (i : ℕ) (x : G k) :
    p (k-i) (a k i x) ≍ b (k+d) i (p k x) :=
  (heq_of_eq (h k i x)).trans (gradedDegreeCast_heq _ _)

end GradedTransport

local instance actualHasKernels {T : Scheme.{u}} : HasKernels T.Modules := inferInstance
local instance actualHasKernel {T : Scheme.{u}} {A B : T.Modules} (f : A ⟶ B) : HasKernel f :=
  HasKernels.has_limit f

variable {X : Scheme.{u}} (D : X.Modules)
  [hD : SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} D 3]

local instance sourceFinite : SheafOfModules.IsFiniteLocallyFree.{u,u,u} D :=
  hD.isFiniteLocallyFree
local instance kernel1Rank :
    SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} (kernel1 D) 2 :=
  Stacks.Chow.isFiniteLocallyFreeOfRank_kernel_bundleTautological D 2 hD
local instance kernel1Finite : SheafOfModules.IsFiniteLocallyFree.{u,u,u} (kernel1 D) :=
  (kernel1Rank D).isFiniteLocallyFree
local instance kernel2Rank :
    SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} (kernel2 D) 1 :=
  Stacks.Chow.isFiniteLocallyFreeOfRank_kernel_bundleTautological (kernel1 D) 1 (kernel1Rank D)
local instance kernel2Finite : SheafOfModules.IsFiniteLocallyFree.{u,u,u} (kernel2 D) :=
  (kernel2Rank D).isFiniteLocallyFree
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

set_option maxHeartbeats 1600000 in
/-- The literal original full projection equals the actual three-stage composite. -/
theorem originalProjection_eq :
    FlagThreeQuotient.projection D = (projection3 D ≫ projection2 D) ≫ projection1 D := by
  rw [← FlagThreeIdentityLines.head1_eq D]
  change (Stacks.FlagTower.kernelTower 2 D).2 ≫ bundleProj D =
    (𝟙 _ ≫ (Stacks.FlagTower.kernelTower 2 D).2) ≫ bundleProj D
  rw [Category.id_comp]

local instance originalProjectionLFT : LocallyOfFiniteType (FlagThreeQuotient.projection D) := by
  rw [originalProjection_eq]
  infer_instance

abbrev target1 (F : X.Modules) : (space1 D).Modules :=
  (Scheme.Modules.pullback (projection1 D)).obj F
abbrev target2 (F : X.Modules) : (space2 D).Modules :=
  (Scheme.Modules.pullback (projection2 D)).obj (target1 D F)
abbrev target3 (F : X.Modules) : (space3 D).Modules :=
  (Scheme.Modules.pullback (projection3 D)).obj (target2 D F)

/-- The actual original full-projection pullback of the original bundle. -/
abbrev pulledBundle (F : X.Modules) : (space3 D).Modules :=
  (Scheme.Modules.pullback (FlagThreeQuotient.projection D)).obj F

set_option maxHeartbeats 1600000 in
/-- Composition of the actual native pullback functors, normalized by the proved original projection. -/
def target3IsoOriginal (F : X.Modules) : target3 D F ≅ pulledBundle D F := by
  let e12 : target3 D F ≅
      (Scheme.Modules.pullback (projection3 D ≫ projection2 D)).obj (target1 D F) :=
    (Scheme.Modules.pullbackComp (projection3 D) (projection2 D)).app (target1 D F)
  let e123 : (Scheme.Modules.pullback (projection3 D ≫ projection2 D)).obj (target1 D F) ≅
      (Scheme.Modules.pullback ((projection3 D ≫ projection2 D) ≫ projection1 D)).obj F :=
    (Scheme.Modules.pullbackComp (projection3 D ≫ projection2 D) (projection1 D)).app F
  let efull : (Scheme.Modules.pullback ((projection3 D ≫ projection2 D) ≫ projection1 D)).obj F ≅
      pulledBundle D F := (Scheme.Modules.pullbackCongr (originalProjection_eq D).symm).app F
  exact e12 ≪≫ e123 ≪≫ efull

variable (C : ChowSituation.{u}) (q : X ⟶ C.S) [LocallyOfFiniteType q]

set_option maxHeartbeats 1600000 in
omit [LocallyOfFiniteType q] in
/-- The right-associated original Chow structure map is the original full flag projection over the base. -/
theorem baseMap3_eq_original :
    baseMap3 D C q = FlagThreeQuotient.projection D ≫ q := by
  rw [originalProjection_eq D]
  simp only [baseMap3, baseMap2, baseMap1, Category.assoc]

/-- The additive map of the literal original flatPullClass, including only its genuine degree casts. -/
def fullPull (k : ℤ) : chowGroup C q k →+ chowGroup C (baseMap3 D C q) (k+3) :=
  (gradedDegreeCast (chowGroup C (baseMap3 D C q))
    (show (k+2)+1=k+3 by omega)).toAddMonoidHom.comp
    ((pull3 D C q ((k+2)+1)).comp ((pull2 D C q (k+2)).comp (pull1 D C q k)))

@[simp] theorem fullPull_apply (k : ℤ) (α : chowGroup C q k) :
    fullPull D C q k α = flatPullClass D C q k α := rfl

abbrev rawPull3 (k : ℤ) :
    chowGroup C (baseMap2 D C q) k →+ chowGroup C (baseMap3 D C q) (k+(0:ℤ)) :=
  bundlePullback C (baseMap2 D C q) (baseMap3 D C q) (projection3 D) rfl 0
    (@relativeDimension_bundleProj (space2 D) (kernel2 D) 0 (kernel2Rank D)) k

/-- Only the two original degree casts separate fullPull from the raw third flat pullback. -/
theorem fullPull_heq_raw (k : ℤ) (α : chowGroup C q k) :
    fullPull D C q k α ≍ rawPull3 D C q ((k+2)+1)
      (pull2 D C q (k+2) (pull1 D C q k α)) :=
by
  refine (gradedDegreeCast_heq (show (k+2)+1=k+3 by omega)
    (pull3 D C q ((k+2)+1) (pull2 D C q (k+2) (pull1 D C q k α)))).trans ?_
  exact gradedDegreeCast_heq (show ((k+2)+1)+0=(k+2)+1 by omega)
    (rawPull3 D C q ((k+2)+1) (pull2 D C q (k+2) (pull1 D C q k α)))

section Chern

variable (F : X.Modules) (r : ℕ)
  [SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} F r]

local instance target1Rank : SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} (target1 D F) r :=
  AlgebraicGeometry.isFiniteLocallyFreeOfRank_pullback (projection1 D) F r
local instance target2Rank : SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} (target2 D F) r :=
  AlgebraicGeometry.isFiniteLocallyFreeOfRank_pullback (projection2 D) (target1 D F) r
local instance target3Rank : SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} (target3 D F) r :=
  AlgebraicGeometry.isFiniteLocallyFreeOfRank_pullback (projection3 D) (target2 D F) r
/-- The actual full pulled bundle has its source rank, derived by genuine pullback. -/
theorem pulledBundle_rank :
    SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} (pulledBundle D F) r :=
  AlgebraicGeometry.isFiniteLocallyFreeOfRank_pullback (FlagThreeQuotient.projection D) F r

local instance pulledBundleRank :
    SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} (pulledBundle D F) r := pulledBundle_rank D F r

/-- Native CapRuleFlat at all three genuine stages proves total-Chern naturality. -/
theorem fullPull_chernFamily_nested :
    Stacks.Chow.Intertwines (fullPull D C q)
      (chernFamily C q F r) (chernFamily C (baseMap3 D C q) (target3 D F) r) := by
  have h1 : Stacks.Chow.Intertwines (pull1 D C q)
      (chernFamily C q F r) (chernFamily C (baseMap1 D C q) (target1 D F) r) :=
    intertwines_chernFamily C q F r (baseMap1 D C q) (projection1 D) rfl 2
      (@relativeDimension_bundleProj X D 2 hD) (target1 D F) (Iso.refl _)
  have h2 : Stacks.Chow.Intertwines (pull2 D C q)
      (chernFamily C (baseMap1 D C q) (target1 D F) r)
      (chernFamily C (baseMap2 D C q) (target2 D F) r) :=
    intertwines_chernFamily C (baseMap1 D C q) (target1 D F) r
      (baseMap2 D C q) (projection2 D) rfl 1
      (@relativeDimension_bundleProj (space1 D) (kernel1 D) 1 (kernel1Rank D))
      (target2 D F) (Iso.refl _)
  have h3 : Stacks.Chow.Intertwines (rawPull3 D C q)
      (chernFamily C (baseMap2 D C q) (target2 D F) r)
      (chernFamily C (baseMap3 D C q) (target3 D F) r) :=
    intertwines_chernFamily C (baseMap2 D C q) (target2 D F) r
      (baseMap3 D C q) (projection3 D) rfl 0
      (@relativeDimension_bundleProj (space2 D) (kernel2 D) 0 (kernel2Rank D))
      (target3 D F) (Iso.refl _)
  intro k i α
  apply eq_of_heq
  refine (fullPull_heq_raw D C q (k-i) (chernFamily C q F r k i α)).trans ?_
  have h12 := (shiftedMap_heq (pull2 D C q) (show (k-i)+2=(k+2)-i by omega)
      (intertwines_apply_heq h1 k i α)).trans
    (intertwines_apply_heq h2 (k+2) i (pull1 D C q k α))
  refine (shiftedMap_heq (rawPull3 D C q)
    (show ((k-i)+2)+1=((k+2)+1)-i by omega) h12).trans ?_
  refine (intertwines_apply_heq h3 ((k+2)+1) i
    (pull2 D C q (k+2) (pull1 D C q k α))).trans ?_
  refine ((chernFamily C (baseMap3 D C q) (target3 D F) r).apply_heq
    (show ((k+2)+1)+0=k+3 by omega) i (fullPull_heq_raw D C q k α).symm).trans ?_
  exact (gradedDegreeCast_heq _ _).symm

/-- The target is the actual original full-projection pullback, not a supplied comparison bundle. -/
theorem fullPull_chernFamily :
    Stacks.Chow.Intertwines (fullPull D C q)
      (chernFamily C q F r) (chernFamily C (baseMap3 D C q) (pulledBundle D F) r) := by
  rw [← chernFamily_congr C (baseMap3 D C q) (pulledBundle D F) r (target3IsoOriginal D F) rfl]
  exact fullPull_chernFamily_nested D C q F r

end Chern

/-- The genuine original full-projection pullback of an actual invertible line. -/
def pulledLine (L : InvertibleLine X) : InvertibleLine (space3 D) := by
  let := L.2
  exact ⟨pulledBundle D L.1, GenuineChern.isInvertible_pullback
    (FlagThreeQuotient.projection D) L.1⟩

section Lines

variable (L : InvertibleLine X)
local instance lineRank : SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} L.1 1 :=
  @SheafOfModules.isFiniteLocallyFreeOfRank_one_of_isInvertible X L.1 L.2
local instance pulledLineRank :
    SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} (pulledLine D L).1 1 :=
  @SheafOfModules.isFiniteLocallyFreeOfRank_one_of_isInvertible (space3 D)
    (pulledLine D L).1 (pulledLine D L).2

/-- Actual line caps are natural for the SAME literal triple flat pullback. -/
theorem fullPull_lineFamily :
    Stacks.Chow.Intertwines (fullPull D C q)
      (lineFamily C q L) (lineFamily C (baseMap3 D C q) (pulledLine D L)) := by
  rw [ChowLineFamilyComparison.lineFamily_eq_homComponent C q L,
    ChowLineFamilyComparison.lineFamily_eq_homComponent C (baseMap3 D C q) (pulledLine D L)]
  apply (ChowVirtualPullback.intertwines_iff_lowering _ _ _).2
  exact ((ChowVirtualPullback.intertwines_iff_lowering _ _ _).1
    (fullPull_chernFamily D C q L.1 1)).homComponent 1

/-- In particular all powers of the actual pulled determinant line obey genuine naturality. -/
theorem fullPull_lineFamily_pow (s : ℕ) :
    Stacks.Chow.Intertwines (fullPull D C q)
      (lineFamily C q L ^ s) (lineFamily C (baseMap3 D C q) (pulledLine D L) ^ s) := by
  apply (ChowVirtualPullback.intertwines_iff_lowering _ _ _).2
  have h := (ChowVirtualPullback.intertwines_iff_lowering _ _ _).1
    (fullPull_lineFamily D C q L)
  induction s with
  | zero => simpa only [pow_zero] using GradedCapFamily.Intertwines.one
  | succ s ih => simpa only [pow_succ] using ih.mul h

/-- Literal actual cap powers commute with the original flatPullClass in every displayed grade. -/
theorem flatPullClass_capPow (s : ℕ) (a m : ℤ) (h : a=m+(s:ℤ))
    (α : chowGroup C q a) :
    flatPullClass D C q m (capPow C q (lineCap C q L) s a m h α) =
      capPow C (baseMap3 D C q) (lineCap C (baseMap3 D C q) (pulledLine D L))
        s (a+3) (m+3) (by omega) (flatPullClass D C q a α) := by
  have hp := (fullPull_lineFamily_pow D C q L s).capTo s (show a-(s:ℤ)=m by omega) α
  dsimp only [capTo] at hp
  rw [LineFamilyCapPower.gradedDegreeCast_lineFamily_pow_apply C q L s a m h α,
    LineFamilyCapPower.gradedDegreeCast_lineFamily_pow_apply C (baseMap3 D C q)
      (pulledLine D L) s (a+3) (m+3) (by omega)] at hp
  exact hp

end Lines

end M9Native.ChowFlagThreePullback
