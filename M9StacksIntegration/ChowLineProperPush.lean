module

public import M9StacksIntegration.ChowLineFamilyComparison
public import M9StacksIntegration.ChowVirtualPullback
public import StacksFrontier.AlgebraicGeometry.Chow.GenuineChern.CapRuleProper

/-! Genuine proper pushforward intertwines the ORIGINAL line-cap
families and their ordered products. Rank one and the cap compatibility
are derived from the actual invertible lines and native Stacks 02U9. -/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option maxRecDepth 4096

open AlgebraicGeometry CategoryTheory Stacks.Chow Stacks.Chow.GenuineChern

universe u v

namespace M9Native.ChowLineProperPush

open ChowCapWords GradedLineCapSubring ChowLineFamilyComparison GradedCapVirtualSchur

local instance lineRank {T : Scheme.{u}} (L : InvertibleLine T) :
    SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} L.1 1 :=
  @SheafOfModules.isFiniteLocallyFreeOfRank_one_of_isInvertible T L.1 L.2

variable (C : ChowSituation.{u}) {X Y : Scheme.{u}}
variable (qX : X ⟶ C.S) [LocallyOfFiniteType qX]
variable (qY : Y ⟶ C.S) [LocallyOfFiniteType qY]
variable (p : X ⟶ Y) [IsProper p] (hp : p ≫ qY = qX)

/-- The literal genuine proper pushforward, with its rational-equivalence
factorization supplied by actual properness. -/
abbrev properPush (k : ℤ) : chowGroup C qX k →+ chowGroup C qY k :=
  properChowPushforward C qX qY p hp k
    (properPushforwardFactorsThroughRationalEquivalence_of_isProper C qX qY p hp k)

/-- Only the native zero-degree transport is inserted to fit the
degree-shifting Intertwines convention. -/
def actualPush (k : ℤ) : chowGroup C qX k →+ chowGroup C qY (k+0) :=
  (gradedDegreeCast (chowGroup C qY) (show k=k+0 by omega)).toAddMonoidHom.comp
    (properPush C qX qY p hp k)

theorem actualPush_heq (k : ℤ) (α : chowGroup C qX k) :
    actualPush C qX qY p hp k α ≍ properPush C qX qY p hp k α :=
  gradedDegreeCast_heq (show k=k+0 by omega) (properPush C qX qY p hp k α)

/-- The shifted convention is exactly the literal unshifted coefficient
identity; no transport compatibility is assumed. -/
theorem intertwines_iff (a : GradedCapFamily (chowGroup C qX))
    (b : GradedCapFamily (chowGroup C qY)) :
    Intertwines (d:=0) (actualPush C qX qY p hp) a b ↔
      ∀ (k : ℤ) (i : ℕ) (α : chowGroup C qX k),
        properPush C qX qY p hp (k-(i:ℤ)) (a k i α) =
          b k i (properPush C qX qY p hp k α) := by
  constructor
  · intro h k i α
    apply eq_of_heq
    refine (actualPush_heq C qX qY p hp (k-(i:ℤ)) (a k i α)).symm.trans ?_
    refine (heq_of_eq (h k i α)).trans ?_
    refine (gradedDegreeCast_heq
      (show k+0-(i:ℤ)=k-(i:ℤ)+0 by omega)
        (b (k+0) i (actualPush C qX qY p hp k α))).trans ?_
    exact b.apply_heq (show k+0=k by omega) i (actualPush_heq C qX qY p hp k α)
  · intro h k i α
    apply eq_of_heq
    refine (actualPush_heq C qX qY p hp (k-(i:ℤ)) (a k i α)).trans ?_
    refine (heq_of_eq (h k i α)).trans ?_
    refine (b.apply_heq (show k=k+0 by omega) i
      (actualPush_heq C qX qY p hp k α).symm).trans ?_
    exact (gradedDegreeCast_heq
      (show k+0-(i:ℤ)=k-(i:ℤ)+0 by omega)
        (b (k+0) i (actualPush C qX qY p hp k α))).symm

section Bundles

variable (E : Y.Modules) (rE : ℕ)
variable [SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} E rE]
variable (E' : X.Modules) [SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} E' rE]
variable (eE : E' ≅ (Scheme.Modules.pullback p).obj E)

include eE in
/-- Every coefficient of the genuine total Chern family commutes with
the original actual proper pushforward, in arbitrary genuine rank. -/
theorem properPush_chernFamily_apply (k : ℤ) (i : ℕ) (α : chowGroup C qX k) :
    properPush C qX qY p hp (k-(i:ℤ)) (chernFamily C qX E' rE k i α) =
      chernFamily C qY E rE k i (properPush C qX qY p hp k α) := by
  by_cases hi : i ≤ rE
  · rw [chernFamily_apply_of_le C qX E' rE k hi,
      chernFamily_apply_of_le C qY E rE k hi]
    exact (chernCap_properPushforward C qX qY p hp E rE E' eE k
      ⟨i,Nat.lt_succ_of_le hi⟩
      (properPushforwardFactorsThroughRationalEquivalence_of_isProper C qX qY p hp k)
      (properPushforwardFactorsThroughRationalEquivalence_of_isProper C qX qY p hp
        (k-(i:ℤ))) α).symm
  · rw [chernFamily_apply_of_gt C qX E' rE k hi,
      chernFamily_apply_of_gt C qY E rE k hi]
    simp only [AddMonoidHom.zero_apply,map_zero]

include eE in
theorem properPush_intertwines_chernFamily :
    Intertwines (d:=0) (actualPush C qX qY p hp)
      (chernFamily C qX E' rE) (chernFamily C qY E rE) :=
  (intertwines_iff C qX qY p hp _ _).2
    (properPush_chernFamily_apply C qX qY p hp E rE E' eE)

include eE in
/-- Native formal inversion of the actual Chern family preserves the
genuine proper intertwiner; no invertibility hypothesis is supplied. -/
theorem properPush_intertwines_inverseFamily :
    Intertwines (d:=0) (actualPush C qX qY p hp)
      (inverseFamily C qX E' rE) (inverseFamily C qY E rE) := by
  rw [inverseFamily_eq_gradedRightInv,inverseFamily_eq_gradedRightInv]
  exact ChowVirtualPullback.intertwines_gradedRightInv _
    (properPush_intertwines_chernFamily C qX qY p hp E rE E' eE)

variable (F : Y.Modules) (rF : ℕ)
variable [SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} F rF]
variable (F' : X.Modules) [SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} F' rF]
variable (eF : F' ≅ (Scheme.Modules.pullback p).obj F)

include eE eF in
/-- The original ordered virtual family c(F)c(E)^(-1) has actual
proper-pushforward naturality, derived from the two genuine bundle maps. -/
theorem properPush_intertwines_virtualFamily :
    Intertwines (d:=0) (actualPush C qX qY p hp)
      (virtualFamily C qX F' E' rF rE) (virtualFamily C qY F E rF rE) :=
  (properPush_intertwines_chernFamily C qX qY p hp F rF F' eF).convolve
    (properPush_intertwines_inverseFamily C qX qY p hp E rE E' eE)

end Bundles

variable (L : InvertibleLine Y) (L' : InvertibleLine X)
variable (eL : L'.1 ≅ (Scheme.Modules.pullback p).obj L.1)

include eL in
/-- Literal coefficient-wise compatibility of the genuine proper map
with the actual named first-Chern family, in every original Chow grade. -/
theorem properPush_lineFamily_apply (k : ℤ) (i : ℕ) (α : chowGroup C qX k) :
    properPush C qX qY p hp (k-(i:ℤ)) (lineFamily C qX L' k i α) =
      lineFamily C qY L k i (properPush C qX qY p hp k α) := by
  by_cases hi : i=1
  · subst i
    rw [lineFamily_eq_homComponent,lineFamily_eq_homComponent,
      homComponent_apply_self,homComponent_apply_self]
    exact properPush_chernFamily_apply C qX qY p hp L.1 1 L'.1 eL k 1 α
  · rw [lineFamily_homogeneous C qX L' k i hi,lineFamily_homogeneous C qY L k i hi]
    simp only [AddMonoidHom.zero_apply,map_zero]

include eL in
/-- Actual proper pushforward intertwines the original operational line
families. The only transport is the genuine native zero-degree cast. -/
theorem properPush_intertwines_lineFamily :
    Intertwines (d:=0) (actualPush C qX qY p hp)
      (lineFamily C qX L') (lineFamily C qY L) :=
  (intertwines_iff C qX qY p hp _ _).2
    (properPush_lineFamily_apply C qX qY p hp L L' eL)

include eL in
/-- The genuine ordered powers also intertwine; no commutativity of the
ambient operational ring is needed. -/
theorem properPush_intertwines_lineFamily_pow (n : ℕ) :
    Intertwines (d:=0) (actualPush C qX qY p hp)
      (lineFamily C qX L' ^ n) (lineFamily C qY L ^ n) := by
  apply (ChowVirtualPullback.intertwines_iff_lowering
    (actualPush C qX qY p hp) _ _).2
  have h := (ChowVirtualPullback.intertwines_iff_lowering
    (actualPush C qX qY p hp) _ _).1
      (properPush_intertwines_lineFamily C qX qY p hp L L' eL)
  induction n with
  | zero => simpa only [pow_zero] using GradedCapFamily.Intertwines.one
  | succ n ih => simpa only [pow_succ] using ih.mul h

include eL in
theorem properPush_lineFamily_pow_apply (n : ℕ) (k : ℤ) (i : ℕ)
    (α : chowGroup C qX k) :
    properPush C qX qY p hp (k-(i:ℤ)) ((lineFamily C qX L' ^ n) k i α) =
      (lineFamily C qY L ^ n) k i (properPush C qX qY p hp k α) :=
  (intertwines_iff C qX qY p hp _ _).1
    (properPush_intertwines_lineFamily_pow C qX qY p hp L L' eL n) k i α

section OrderedWords

variable {ι : Type v} (lines : ι → InvertibleLine Y) (lines' : ι → InvertibleLine X)
variable (isos : ∀ i, (lines' i).1 ≅ (Scheme.Modules.pullback p).obj (lines i).1)

include isos in
/-- An actual finite ordered word of pulled named lines has genuine
proper-pushforward naturality, derived by native convolution induction. -/
theorem properPush_intertwines_lineFamily_prod (w : List ι) :
    Intertwines (d:=0) (actualPush C qX qY p hp)
      ((w.map fun i => lineFamily C qX (lines' i)).prod)
      ((w.map fun i => lineFamily C qY (lines i)).prod) := by
  apply (ChowVirtualPullback.intertwines_iff_lowering
    (actualPush C qX qY p hp) _ _).2
  induction w with
  | nil => simpa only [List.map_nil,List.prod_nil] using GradedCapFamily.Intertwines.one
  | cons i w ih =>
      simp only [List.map_cons,List.prod_cons]
      exact ((ChowVirtualPullback.intertwines_iff_lowering
        (actualPush C qX qY p hp) _ _).1
          (properPush_intertwines_lineFamily C qX qY p hp (lines i) (lines' i) (isos i))).mul ih

include isos in
/-- The optional ordered coefficient-word formula is stated using the
original proper pushforward and the original actual graded cap maps. -/
theorem properPush_lineFamily_prod_apply (w : List ι) (k : ℤ) (i : ℕ)
    (α : chowGroup C qX k) :
    properPush C qX qY p hp (k-(i:ℤ))
        (((w.map fun j => lineFamily C qX (lines' j)).prod) k i α) =
      ((w.map fun j => lineFamily C qY (lines j)).prod) k i
        (properPush C qX qY p hp k α) :=
  (intertwines_iff C qX qY p hp _ _).1
    (properPush_intertwines_lineFamily_prod C qX qY p hp lines lines' isos w) k i α

end OrderedWords

end M9Native.ChowLineProperPush
