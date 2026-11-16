module

public import M9StacksIntegration.ChowFlagThreeInputs
public import M9StacksIntegration.ChowFlagThreeStages
public import M9StacksIntegration.FlagThreeIdentityLines
public import M9StacksIntegration.FlagThreeTensorChern
public import M9StacksIntegration.ChowProjectiveTensorInput
public import M9StacksIntegration.NativePullbackTensorLine
public import StacksFrontier.AlgebraicGeometry.Chow.GenuineChern.CapRuleFlat
public import StacksFrontier.AlgebraicGeometry.Chow.GenuineChern.CapRuleComm

/-!
# Original flag tensor inputs and genuine Chern pullback

The tensor factors are compared using the actual flag lines and native
pullback tensor isomorphisms. Chern caps commute with the original flat
pullbacks and the original invertible-line cap powers.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1500000
set_option maxRecDepth 4096

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Stacks.Chow Stacks.Chow.GenuineChern

universe u

attribute [local implicit_reducible] TopCat.Sheaf CategoryTheory.sheafCompose
  AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme.Modules.Hom
  AlgebraicGeometry.Scheme.Modules.pullback Stacks.SheafOfModules.Tensor.ringSheaf
attribute [local instance] AlgebraicGeometry.isFiniteLocallyFreeOfRank_pullback

namespace M9Native.ChowFlagThreeInputNormalization

open ChowFlagThreeStages

/-- Native tensoring carries both original sheaf isomorphisms. -/
def tensorCongr {T : Scheme.{u}} {A A' B B' : T.Modules}
    (a : A ≅ A') (b : B ≅ B') :
    Scheme.Modules.tensorObj A B ≅ Scheme.Modules.tensorObj A' B' :=
  ((Stacks.SheafOfModules.Tensor.sheafTensor T.sheaf).mapIso a).app B ≪≫
    ((Stacks.SheafOfModules.Tensor.sheafTensor T.sheaf).obj A').mapIso b

/-- Genuine pullback of the same native tensor product. -/
def tensorPullbackIso {X Y : Scheme.{u}} (f : Y ⟶ X) (A B : X.Modules) :
    (Scheme.Modules.pullback f).obj (Scheme.Modules.tensorObj A B) ≅
      Scheme.Modules.tensorObj ((Scheme.Modules.pullback f).obj A)
        ((Scheme.Modules.pullback f).obj B) :=
  NativePullbackTensorLine.pullbackTensorIso f A B

section GeneralCaps

variable (C : ChowSituation.{u}) {T : Scheme.{u}} (q : T ⟶ C.S)
  [LocallyOfFiniteType q]

theorem groupCast_self {k : ℤ} (h : k=k) (x : chowGroup C q k) :
    chowGroupCast C q h x=x := by
  cases h
  rfl

/-- Chern caps respect only the written integer degree and the original input. -/
theorem cap_heq (E : T.Modules) (r : ℕ)
    [SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} E r] (j : Fin (r+1))
    {a b : ℤ} (h : a=b) {x : chowGroup C q a} {y : chowGroup C q b} (hxy : x ≍ y) :
    chernCap C r q E a j x ≍ chernCap C r q E b j y := by
  cases h
  cases hxy
  rfl

/-- Actual Chern caps commute with the same genuine line cap power.
Native lowering commutation supplies the identity. -/
theorem cap_capPow (E : T.Modules) (r : ℕ)
    [SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} E r]
    (L : T.Modules)
    [SheafOfModules.IsInvertible T.sheaf.obj T.ringCatSheaf.property L]
    (j : Fin (r+1)) (s : ℕ) (a m : ℤ) (h : a=m+s) (x : chowGroup C q a) :
    chernCap C r q E m j (capPow C q (invCap C q L) s a m h x) =
      capPow C q (invCap C q L) s (a-(j:ℤ)) (m-(j:ℤ)) (by omega)
        (chernCap C r q E a j x) := by
  let ψ := chernLowering C q E r j
  have hc : ∀ (b c : ℤ) (hb : b=c+(j:ℤ)) (z : chowGroup C q (b+1)),
      ψ b c hb ((invCap C q L).capOnChow C q b z) =
        (invCap C q L).capOnChow C q c (ψ (b+1) (c+1) (by omega) z) := by
    intro b c hb z
    exact chernLowering_invCap_comm C q E r j L b c hb z
  have H := GenuineChern.lowering_capPow (C:=C) (sP:=q)
    (twist:=invCap C q L) (e:=(j:ℤ)) (ψ:=ψ) hc s a m h
      (a-(j:ℤ)) (m-(j:ℤ)) (by omega) (by omega) (by omega) x
  dsimp only [ψ] at H
  simp only [chernLowering_apply,groupCast_self] at H
  exact H

/-- Transport of the actual structure map changes no Chern cap. -/
theorem cap_structureMapCast_heq (q' : T ⟶ C.S) [LocallyOfFiniteType q'] (h : q=q')
    (E : T.Modules) (r : ℕ) [SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} E r]
    (k : ℤ) (j : Fin (r+1)) (x : chowGroup C q k) :
    chernCap C r q' E k j (structureMapCast C q q' h k x) ≍
      chernCap C r q E k j x := by
  subst q'
  rfl

end GeneralCaps

local instance actualHasKernels {T : Scheme.{u}} : HasKernels T.Modules := inferInstance
local instance actualHasKernel {T : Scheme.{u}} {A B : T.Modules} (f : A ⟶ B) : HasKernel f :=
  HasKernels.has_limit f

variable {X : Scheme.{u}} (D : X.Modules)
  [hD : SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} D 10]
  (F : X.Modules) [hF : SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} F 10]

local instance sourceFinite : SheafOfModules.IsFiniteLocallyFree.{u,u,u} D := hD.isFiniteLocallyFree
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
local instance projection1Flat : Flat (projection1 D) := @Stacks.Chow.flat_bundleProj X D 9 hD
local instance projection2Flat : Flat (projection2 D) :=
  @Stacks.Chow.flat_bundleProj (space1 D) (kernel1 D) 8 (kernel1Rank D)
local instance projection3Flat : Flat (projection3 D) :=
  @Stacks.Chow.flat_bundleProj (space2 D) (kernel2 D) 7 (kernel2Rank D)
local instance target1Rank : SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} (target1 D F) 10 :=
  AlgebraicGeometry.isFiniteLocallyFreeOfRank_pullback (projection1 D) F 10
local instance target2Rank : SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} (target2 D F) 10 :=
  AlgebraicGeometry.isFiniteLocallyFreeOfRank_pullback (projection2 D) (target1 D F) 10
local instance target3Rank : SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} (target3 D F) 10 :=
  AlgebraicGeometry.isFiniteLocallyFreeOfRank_pullback (projection3 D) (target2 D F) 10

abbrev tensorBundle1 : (space1 D).Modules :=
  Scheme.Modules.tensorObj (target1 D F) (bundleTwist D)
abbrev tensorBundle2 : (space2 D).Modules :=
  Scheme.Modules.tensorObj (target2 D F) (bundleTwist (kernel1 D))
abbrev tensorBundle3 : (space3 D).Modules :=
  Scheme.Modules.tensorObj (target3 D F) (bundleTwist (kernel2 D))

/-- The original first flag factor is the actual double pullback of
the first projective tensor bundle. -/
def factor1Iso :
    Scheme.Modules.tensorObj (X:=space3 D) (FlagThreeQuotient.line1 D) (target3 D F) ≅
      (Scheme.Modules.pullback (projection3 D)).obj
        ((Scheme.Modules.pullback (projection2 D)).obj (tensorBundle1 D F)) :=
  Scheme.Modules.tensorObjBraiding _ _ ≪≫
    tensorCongr (Iso.refl (target3 D F)) (FlagThreeIdentityLines.line1Iso D) ≪≫
    (tensorPullbackIso (projection3 D) (target2 D F)
      ((Scheme.Modules.pullback (projection2 D)).obj (bundleTwist D))).symm ≪≫
    (Scheme.Modules.pullback (projection3 D)).mapIso
      (tensorPullbackIso (projection2 D) (target1 D F) (bundleTwist D)).symm

/-- The original second flag factor is the actual pullback of the
second projective tensor bundle. -/
def factor2Iso :
    Scheme.Modules.tensorObj (X:=space3 D) (FlagThreeQuotient.line2 D) (target3 D F) ≅
      (Scheme.Modules.pullback (projection3 D)).obj (tensorBundle2 D F) :=
  Scheme.Modules.tensorObjBraiding _ _ ≪≫
    tensorCongr (Iso.refl (target3 D F)) (FlagThreeIdentityLines.line2Iso D) ≪≫
    (tensorPullbackIso (projection3 D) (target2 D F) (bundleTwist (kernel1 D))).symm

/-- The third original factor uses the third original O(1). -/
def factor3Iso :
    Scheme.Modules.tensorObj (X:=space3 D) (FlagThreeQuotient.line3 D) (target3 D F) ≅ tensorBundle3 D F :=
  Scheme.Modules.tensorObjBraiding _ _ ≪≫
    tensorCongr (Iso.refl (target3 D F)) (FlagThreeIdentityLines.line3Iso D)

variable (C : ChowSituation.{u}) (q : X ⟶ C.S) [LocallyOfFiniteType q]

/-- Genuine Chern pullback at the second original projective stage. -/
theorem cap_pull2 (E : (space1 D).Modules)
    [SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} E 10] (k : ℤ)
    (x : chowGroup C (baseMap1 D C q) k) :
    chernCap C 10 (baseMap2 D C q) ((Scheme.Modules.pullback (projection2 D)).obj E)
        (k+8) (Fin.last 10) (pull2 D C q k x) ≍
      pull2 D C q (k-10) (chernCap C 10 (baseMap1 D C q) E k (Fin.last 10) x) :=
  chernCap_flatPullback_heq C (baseMap1 D C q) (baseMap2 D C q) (projection2 D) rfl 8
    (@Stacks.Chow.relativeDimension_bundleProj (space1 D) (kernel1 D) 8 (kernel1Rank D))
    E 10 ((Scheme.Modules.pullback (projection2 D)).obj E) (Iso.refl _) k (Fin.last 10)
    (flatPullbackFactorsThroughRationalEquivalence_general C _ _ _ rfl _ _ k)
    (flatPullbackFactorsThroughRationalEquivalence_general C _ _ _ rfl _ _ _) x

/-- Genuine Chern pullback at the third original projective stage. -/
theorem cap_pull3 (E : (space2 D).Modules)
    [SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} E 10] (k : ℤ)
    (x : chowGroup C (baseMap2 D C q) k) :
    chernCap C 10 (baseMap3 D C q) ((Scheme.Modules.pullback (projection3 D)).obj E)
        (k+7) (Fin.last 10) (pull3 D C q k x) ≍
      pull3 D C q (k-10) (chernCap C 10 (baseMap2 D C q) E k (Fin.last 10) x) :=
  chernCap_flatPullback_heq C (baseMap2 D C q) (baseMap3 D C q) (projection3 D) rfl 7
    (@Stacks.Chow.relativeDimension_bundleProj (space2 D) (kernel2 D) 7 (kernel2Rank D))
    E 10 ((Scheme.Modules.pullback (projection3 D)).obj E) (Iso.refl _) k (Fin.last 10)
    (flatPullbackFactorsThroughRationalEquivalence_general C _ _ _ rfl _ _ k)
    (flatPullbackFactorsThroughRationalEquivalence_general C _ _ _ rfl _ _ _) x

/-- The actual second flat pullback respects only the written degree. -/
theorem pull2_heq {a b : ℤ} (h : a=b)
    {x : chowGroup C (baseMap1 D C q) a} {y : chowGroup C (baseMap1 D C q) b} (hxy : x ≍ y) :
    pull2 D C q a x ≍ pull2 D C q b y := by
  cases h
  cases hxy
  rfl

/-- The actual third flat pullback respects only the written degree. -/
theorem pull3_heq {a b : ℤ} (h : a=b)
    {x : chowGroup C (baseMap2 D C q) a} {y : chowGroup C (baseMap2 D C q) b} (hxy : x ≍ y) :
    pull3 D C q a x ≍ pull3 D C q b y := by
  cases h
  cases hxy
  rfl

local instance twist1Invertible :
    SheafOfModules.IsInvertible (space1 D).sheaf.obj (space1 D).ringCatSheaf.property (bundleTwist D) :=
  Stacks.Chow.isInvertible_bundleTwist D
local instance twist2Invertible :
    SheafOfModules.IsInvertible (space2 D).sheaf.obj (space2 D).ringCatSheaf.property
      (bundleTwist (kernel1 D)) := Stacks.Chow.isInvertible_bundleTwist (kernel1 D)
local instance twist3Invertible :
    SheafOfModules.IsInvertible (space3 D).sheaf.obj (space3 D).ringCatSheaf.property
      (bundleTwist (kernel2 D)) := Stacks.Chow.isInvertible_bundleTwist (kernel2 D)
local instance twist1Rank : SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} (bundleTwist D) 1 :=
  Stacks.Chow.isFiniteLocallyFreeOfRank_bundleTwist D
local instance twist2Rank : SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u}
    (bundleTwist (kernel1 D)) 1 := Stacks.Chow.isFiniteLocallyFreeOfRank_bundleTwist (kernel1 D)
local instance twist3Rank : SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u}
    (bundleTwist (kernel2 D)) 1 := Stacks.Chow.isFiniteLocallyFreeOfRank_bundleTwist (kernel2 D)
local instance tensorBundle1Rank : SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u}
    (tensorBundle1 D F) 10 :=
  FlagThreeTensorChern.tensor_rank (target1 D F) (bundleTwist D) 10 1
local instance tensorBundle2Rank : SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u}
    (tensorBundle2 D F) 10 :=
  FlagThreeTensorChern.tensor_rank (target2 D F) (bundleTwist (kernel1 D)) 10 1
local instance tensorBundle3Rank : SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u}
    (tensorBundle3 D F) 10 :=
  FlagThreeTensorChern.tensor_rank (target3 D F) (bundleTwist (kernel2 D)) 10 1
local instance flagQuotientRank : SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u}
    (FlagThreeQuotient.quotientBundle D 2) 3 := FlagThreeQuotient.quotientBundle_rank D 2
local instance flagLine1Rank : SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u}
    (FlagThreeQuotient.line1 D) 1 := FlagThreeQuotient.line1_rank D
local instance flagLine2Rank : SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u}
    (FlagThreeQuotient.line2 D) 1 := FlagThreeQuotient.line2_rank D
local instance flagLine3Rank : SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u}
    (FlagThreeQuotient.line3 D) 1 := FlagThreeQuotient.line3_rank D
local instance flagFactor1Rank : SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u}
    (Scheme.Modules.tensorObj (X:=space3 D) (FlagThreeQuotient.line1 D) (target3 D F)) 10 :=
  @FlagThreeTensorChern.tensor_rank (space3 D) (FlagThreeQuotient.line1 D) (target3 D F)
    1 10 (flagLine1Rank D) (target3Rank D F)
local instance flagFactor2Rank : SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u}
    (Scheme.Modules.tensorObj (X:=space3 D) (FlagThreeQuotient.line2 D) (target3 D F)) 10 :=
  @FlagThreeTensorChern.tensor_rank (space3 D) (FlagThreeQuotient.line2 D) (target3 D F)
    1 10 (flagLine2Rank D) (target3Rank D F)
local instance flagFactor3Rank : SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u}
    (Scheme.Modules.tensorObj (X:=space3 D) (FlagThreeQuotient.line3 D) (target3 D F)) 10 :=
  @FlagThreeTensorChern.tensor_rank (space3 D) (FlagThreeQuotient.line3 D) (target3 D F)
    1 10 (flagLine3Rank D) (target3Rank D F)
local instance flagTensorRank : SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u}
    (Scheme.Modules.tensorObj (X:=space3 D) (FlagThreeQuotient.quotientBundle D 2) (target3 D F)) 30 :=
  @FlagThreeTensorChern.tensor_rank (space3 D) (FlagThreeQuotient.quotientBundle D 2) (target3 D F)
    3 10 (flagQuotientRank D) (target3Rank D F)

/-- The first original input is its actual tensor cap after the actual
square of the first tautological cap and the first flat pullback. -/
theorem outer_input_heq (k : ℤ) (x : chowGroup C q k) :
    ChowFlagThreeInputs.outerTensorInput D F C q k x ≍
      chernCap C 10 (baseMap1 D C q) (tensorBundle1 D F) (k+7) (Fin.last 10)
        (capPow C (baseMap1 D C q) (invCap C (baseMap1 D C q) (bundleTwist D))
          2 (k+9) (k+7) (by omega) (pull1 D C q k x)) := by
  unfold ChowFlagThreeInputs.outerTensorInput ChowProjectiveTensorInput.tensorInput
  refine (chowGroupCast_heq C (baseMap1 D C q) _ _).trans ?_
  apply cap_heq C (baseMap1 D C q) (tensorBundle1 D F) 10 (Fin.last 10) (by omega)
  exact GenuineChern.capPow_heq C (baseMap1 D C q)
    (invCap C (baseMap1 D C q) (bundleTwist D)) _ _ rfl rfl (by omega) HEq.rfl

/-- The second original input retains the original exponent-one cap. -/
theorem middle_input_heq (k : ℤ) (x : chowGroup C q k) :
    ChowFlagThreeInputs.middleTensorInput D F C q k x ≍
      chernCap C 10 (baseMap2 D C q) (tensorBundle2 D F) (k+4) (Fin.last 10)
        (capPow C (baseMap2 D C q) (invCap C (baseMap2 D C q) (bundleTwist (kernel1 D)))
          1 ((k-3)+8) (k+4) (by omega)
          (pull2 D C q (k-3) (ChowFlagThreeInputs.outerTensorInput D F C q k x))) := by
  unfold ChowFlagThreeInputs.middleTensorInput ChowProjectiveTensorInput.tensorInput
  refine (chowGroupCast_heq C (baseMap2 D C q) _ _).trans ?_
  apply cap_heq C (baseMap2 D C q) (tensorBundle2 D F) 10 (Fin.last 10) (by omega)
  exact GenuineChern.capPow_heq C (baseMap2 D C q)
    (invCap C (baseMap2 D C q) (bundleTwist (kernel1 D))) _ _ rfl rfl (by omega) HEq.rfl

/-- The last exponent is genuinely zero, so the third original input
is the third actual tensor cap of the third flat pullback. -/
theorem normal_input_heq (k : ℤ) (x : chowGroup C q k) :
    ChowFlagThreeInputs.normalTensorInput D F C q k x ≍
      chernCap C 10 (baseMap3 D C q) (tensorBundle3 D F) (((k-3)-3)+7) (Fin.last 10)
        (pull3 D C q ((k-3)-3) (ChowFlagThreeInputs.middleTensorInput D F C q k x)) := by
  refine (ChowFlagThreeInputs.normalTensorInput_heq_raw D F C q k x).trans ?_
  unfold ChowProjectiveTensorInput.tensorInput
  refine (chowGroupCast_heq C (baseMap3 D C q) _ _).trans ?_
  apply cap_heq C (baseMap3 D C q) (tensorBundle3 D F) 10 (Fin.last 10) (by omega)
  rw [capPow_zero_apply]
  exact chowGroupCast_heq C (baseMap3 D C q) _ _

/-- The actual rank-thirty tensor cap of the constructed original
normalizer equals the three nested geometric tensor inputs. -/
theorem tensor_on_normalClass_heq (k : ℤ) (x : chowGroup C q k) :
    chernCap C 30 (baseMap3 D C q)
      (Scheme.Modules.tensorObj (X:=space3 D) (FlagThreeQuotient.quotientBundle D 2) (target3 D F))
      (k+21) (Fin.last 30) (normalClass D C q k x) ≍
    ChowFlagThreeInputs.normalTensorInput D F C q k x := by
  have hlast : ((Fin.last 10 : Fin 11) : ℤ)=10 := rfl
  let x1 := capPow C (baseMap1 D C q) (invCap C (baseMap1 D C q) (bundleTwist D))
    2 (k+9) (k+7) (by omega) (pull1 D C q k x)
  let x2 := capPow C (baseMap2 D C q)
    (invCap C (baseMap2 D C q) (bundleTwist (kernel1 D)))
    1 ((k+7)+8) (k+14) (by omega) (pull2 D C q (k+7) x1)
  let x3 := pull3 D C q (k+14) x2
  let p2 := capPow C (baseMap2 D C q)
    (invCap C (baseMap2 D C q) (bundleTwist (kernel1 D)))
    1 ((k-3)+8) (k+4) (by omega)
      (pull2 D C q (k-3) (ChowFlagThreeInputs.outerTensorInput D F C q k x))
  have hN : normalClass D C q k x ≍ x3 := by
    unfold normalClass
    exact gradedDegreeCast_heq _ _
  have h1 :
      chernCap C 10 (baseMap3 D C q)
        (Scheme.Modules.tensorObj (X:=space3 D) (FlagThreeQuotient.line1 D) (target3 D F))
        (k+21) (Fin.last 10) (normalClass D C q k x) ≍
      pull3 D C q (k+4) p2 := by
    refine (@cap_heq C (space3 D) (baseMap3 D C q) inferInstance
      (Scheme.Modules.tensorObj (X:=space3 D) (FlagThreeQuotient.line1 D) (target3 D F))
      10 (flagFactor1Rank D F) (Fin.last 10) _ _ (by omega) _ _ hN).trans ?_
    refine (heq_of_eq (@chernCap_congr C (space3 D) (baseMap3 D C q) inferInstance
      (Scheme.Modules.tensorObj (X:=space3 D) (FlagThreeQuotient.line1 D) (target3 D F))
      _ 10 (flagFactor1Rank D F) inferInstance (factor1Iso D F)
      ((k+14)+7) (Fin.last 10) x3)).trans ?_
    refine (cap_pull3 D C q ((Scheme.Modules.pullback (projection2 D)).obj (tensorBundle1 D F))
      (k+14) x2).trans ?_
    apply pull3_heq D C q (by omega)
    refine (heq_of_eq (cap_capPow C (baseMap2 D C q)
      ((Scheme.Modules.pullback (projection2 D)).obj (tensorBundle1 D F)) 10
      (bundleTwist (kernel1 D)) (Fin.last 10) 1 ((k+7)+8) (k+14) (by omega)
      (pull2 D C q (k+7) x1))).trans ?_
    refine GenuineChern.capPow_heq C (baseMap2 D C q)
      (invCap C (baseMap2 D C q) (bundleTwist (kernel1 D))) _ _ rfl (by omega) (by omega) ?_
    refine (cap_pull2 D C q (tensorBundle1 D F) (k+7) x1).trans ?_
    apply pull2_heq D C q (by omega)
    exact (outer_input_heq D F C q k x).symm
  have h2 :
      chernCap C 10 (baseMap3 D C q)
        (Scheme.Modules.tensorObj (X:=space3 D) (FlagThreeQuotient.line2 D) (target3 D F))
        ((k+21)-10) (Fin.last 10)
        (chernCap C 10 (baseMap3 D C q)
          (Scheme.Modules.tensorObj (X:=space3 D) (FlagThreeQuotient.line1 D) (target3 D F))
          (k+21) (Fin.last 10) (normalClass D C q k x)) ≍
      pull3 D C q ((k-3)-3) (ChowFlagThreeInputs.middleTensorInput D F C q k x) := by
    refine (@cap_heq C (space3 D) (baseMap3 D C q) inferInstance
      (Scheme.Modules.tensorObj (X:=space3 D) (FlagThreeQuotient.line2 D) (target3 D F))
      10 (flagFactor2Rank D F) (Fin.last 10) _ _ (by omega) _ _ h1).trans ?_
    refine (heq_of_eq (@chernCap_congr C (space3 D) (baseMap3 D C q) inferInstance
      (Scheme.Modules.tensorObj (X:=space3 D) (FlagThreeQuotient.line2 D) (target3 D F))
      _ 10 (flagFactor2Rank D F) inferInstance (factor2Iso D F)
      ((k+4)+7) (Fin.last 10) (pull3 D C q (k+4) p2))).trans ?_
    refine (cap_pull3 D C q (tensorBundle2 D F) (k+4) p2).trans ?_
    apply pull3_heq D C q (by omega)
    exact (middle_input_heq D F C q k x).symm
  refine (FlagThreeTensorChern.tensor_topCap_heq D C (baseMap3 D C q) (target3 D F)
    (k+21) (normalClass D C q k x)).trans ?_
  refine (@cap_heq C (space3 D) (baseMap3 D C q) inferInstance
      (Scheme.Modules.tensorObj (X:=space3 D) (FlagThreeQuotient.line3 D) (target3 D F))
      10 (flagFactor3Rank D F) (Fin.last 10) _ _ (by omega) _ _ h2).trans ?_
  refine (heq_of_eq (@chernCap_congr C (space3 D) (baseMap3 D C q) inferInstance
      (Scheme.Modules.tensorObj (X:=space3 D) (FlagThreeQuotient.line3 D) (target3 D F))
      _ 10 (flagFactor3Rank D F) inferInstance (factor3Iso D F)
    (((k-3)-3)+7) (Fin.last 10)
    (pull3 D C q ((k-3)-3) (ChowFlagThreeInputs.middleTensorInput D F C q k x)))).trans ?_
  exact (normal_input_heq D F C q k x).symm

end M9Native.ChowFlagThreeInputNormalization
