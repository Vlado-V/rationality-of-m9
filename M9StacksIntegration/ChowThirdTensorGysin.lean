module

public import M9StacksIntegration.ChowTensorGysinComposition
public import M9StacksIntegration.ChowSignedVirtualKernel
public import M9StacksIntegration.ChowVirtualSchurWords
public import M9StacksIntegration.Private.CommutingSchurWords

/-!
# Three actual projective tensor Gysin maps and the ordered Schur operator

The third actual push is composed with the two actual kernel pushes.
The normalizing powers are two, one and zero. Only genuine geometric
Gysin, kernel Whitney and proper Chern naturality are used. The ordered
six-word expression, and its ordinary virtual Schur specialization on
the actual dual source, are conclusions.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
set_option maxRecDepth 4096
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Stacks.Chow
open Stacks.Chow.GenuineChern
open Stacks.AlgebraicGeometry.ReflexiveModules
universe u
namespace M9Native.ChowThirdTensorGysin
open GradedCapVirtualSchur ChowCapWords GradedLineCapSubring
open ChowProjectiveTensorInput ChowTensorGysinComposition

variable {X : Scheme.{u}} (D F : X.Modules)
    [hD : SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} D 10]
    [hF : SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} F 10]
    (C : ChowSituation.{u}) (q : X ⟶ C.S) [LocallyOfFiniteType q]

local instance actualHasKernels {T : Scheme.{u}} : HasKernels T.Modules := inferInstance
local instance actualHasKernel {T : Scheme.{u}} {A B : T.Modules} (f : A ⟶ B) : HasKernel f :=
  HasKernels.has_limit f
local instance sourceFinite : SheafOfModules.IsFiniteLocallyFree.{u,u,u} D :=
  hD.isFiniteLocallyFree
local instance sourceFlat : Flat (bundleProj D) :=
  @Stacks.Chow.flat_bundleProj X D 9 hD
local instance sourceLFT : LocallyOfFiniteType (bundleProj D) :=
  @Stacks.Chow.locallyOfFiniteType_bundleProj X D 9 hD
local instance kernelRank : SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u}
    (ChowFlagMoments.firstKernel D) 9 :=
  Stacks.Chow.isFiniteLocallyFreeOfRank_kernel_bundleTautological D 9 hD
local instance pulledTargetRank : SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u}
    ((Scheme.Modules.pullback (bundleProj D)).obj F) 10 :=
  AlgebraicGeometry.isFiniteLocallyFreeOfRank_pullback (bundleProj D) F 10
local instance pulledSourceRank : SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u}
    ((Scheme.Modules.pullback (bundleProj D)).obj D) 10 :=
  AlgebraicGeometry.isFiniteLocallyFreeOfRank_pullback (bundleProj D) D 10

/-- The literal three successive projective tensor pushes. -/
def tripleTensorPush (k : ℤ) (α : chowGroup C q k) : chowGroup C q (k-9) :=
  ChowLineProperPush.properPush C (bundleProj D ≫ q) q (bundleProj D) rfl (k-9)
    (chowGroupCast C (bundleProj D ≫ q) (by omega)
      (@doubleTensorPush (bundle D) (ChowFlagMoments.firstKernel D) (kernelRank D)
        ((Scheme.Modules.pullback (bundleProj D)).obj F) (pulledTargetRank D F)
        C (bundleProj D ≫ q) inferInstance (k-3)
        (tensorInput D 9 F 10 C q 2 3 (by decide) k α)))

/-- The six ordered coefficient words obtained by the genuine pushes. -/
def orderedWords (a : GradedCapFamily (chowGroup C q)) : GradedCapFamily (chowGroup C q) :=
  homComponent 3 a * homComponent 3 a * homComponent 3 a -
    homComponent 3 a * homComponent 2 a * homComponent 4 a -
    homComponent 2 a * homComponent 4 a * homComponent 3 a +
    homComponent 2 a * homComponent 2 a * homComponent 5 a +
    homComponent 1 a * homComponent 4 a * homComponent 4 a -
    homComponent 1 a * homComponent 3 a * homComponent 5 a

theorem tripleTensorPush_eq_orderedWords (k : ℤ) (α : chowGroup C q k) :
    tripleTensorPush D F C q k α =
      orderedWords C q (ChowSignedVirtualFamily.family C q F D 10 10) k 9 α := by
  let qP := bundleProj D ≫ q
  let PD := (Scheme.Modules.pullback (bundleProj D)).obj D
  let PF := (Scheme.Modules.pullback (bundleProj D)).obj F
  let K := ChowFlagMoments.firstKernel D
  let A := ChowSignedVirtualFamily.family C qP PF K 10 9
  let cP := ChowSignedVirtualFamily.family C qP PF PD 10 10
  let c := ChowSignedVirtualFamily.family C q F D 10 10
  let L : InvertibleLine (bundle D) :=
    ⟨bundleTwist D, Stacks.Chow.isInvertible_bundleTwist D⟩
  let x := lineFamily C qP L
  let β := tensorInput D 9 F 10 C q 2 3 (by decide) k α
  let P := fun l => ChowLineProperPush.properPush C qP q (bundleProj D) rfl l
  let c₁ := homComponent 1 cP
  let c₂ := homComponent 2 cP
  let c₃ := homComponent 3 cP
  let c₄ := homComponent 4 cP
  let Q₀ := c₃*c₃-c₂*c₄
  let Q₁ := c₁*c₄-c₃*c₂
  let Q₂ := c₂*c₂-c₁*c₃
  let B₀ := homComponent 3 c * homComponent 3 c - homComponent 2 c * homComponent 4 c
  let B₁ := homComponent 1 c * homComponent 4 c - homComponent 3 c * homComponent 2 c
  let B₂ := homComponent 2 c * homComponent 2 c - homComponent 1 c * homComponent 3 c
  have hx := lineFamily_homogeneous C qP L
  have hcomm (i : ℕ) : Commute x (homComponent i cP) :=
    ChowSignedVirtualLineCommutation.lineFamily_commute_homComponent C qP PD 10 L PF 10 i
  have hA (i : ℕ) (hi : 1 ≤ i) : homComponent i A =
      homComponent i cP - x*homComponent (i-1) cP :=
    ChowSignedVirtualKernel.family_kernel_coefficients D 8 C qP PF 10 i hi
  have hmiddle : homComponent 3 A * homComponent 3 A -
      homComponent 2 A * homComponent 4 A = Q₀+x*Q₁+(x*x)*Q₂ := by
    rw [hA 3 (by decide), hA 2 (by decide), hA 4 (by decide)]
    exact CommutingSchurWords.middle_quadratic x c₁ c₂ c₃ c₄
      (hcomm 1) (hcomm 2) (hcomm 3)
  have hxQ₁ : Commute x Q₁ :=
    ((hcomm 1).mul_right (hcomm 4)).sub_right ((hcomm 3).mul_right (hcomm 2))
  have hxQ₂ : Commute (x*x) Q₂ := by
    simpa only [pow_two] using
      ((((hcomm 2).mul_right (hcomm 2)).sub_right
        ((hcomm 1).mul_right (hcomm 3))).pow_left 2)
  have hproper := ChowSignedVirtualFamily.properPush C qP q (bundleProj D) rfl
    D 10 PD (Iso.refl _) F 10 PF (Iso.refl _)
  have hp := (ChowVirtualPullback.intertwines_iff_lowering
    (ChowLineProperPush.actualPush C qP q (bundleProj D) rfl) cP c).1 hproper
  have hP₀ : Intertwines (d:=0) (ChowLineProperPush.actualPush C qP q (bundleProj D) rfl)
      Q₀ B₀ :=
    (ChowVirtualPullback.intertwines_iff_lowering _ _ _).2
      (((hp.homComponent 3).mul (hp.homComponent 3)).sub
        ((hp.homComponent 2).mul (hp.homComponent 4)))
  have hP₁ : Intertwines (d:=0) (ChowLineProperPush.actualPush C qP q (bundleProj D) rfl)
      Q₁ B₁ :=
    (ChowVirtualPullback.intertwines_iff_lowering _ _ _).2
      (((hp.homComponent 1).mul (hp.homComponent 4)).sub
        ((hp.homComponent 3).mul (hp.homComponent 2)))
  have hP₂ : Intertwines (d:=0) (ChowLineProperPush.actualPush C qP q (bundleProj D) rfl)
      Q₂ B₂ :=
    (ChowVirtualPullback.intertwines_iff_lowering _ _ _).2
      (((hp.homComponent 2).mul (hp.homComponent 2)).sub
        ((hp.homComponent 1).mul (hp.homComponent 3)))
  have hxβ : capTo x 1 (show (k-3)-1=k-4 by omega) β =
      tensorInput D 9 F 10 C q 3 4 (by decide) k α := by
    apply eq_of_heq
    exact (gradedDegreeCast_heq _ _).trans
      (line_tensorInput_succ D 9 F 10 C q 2 3 (by decide) k α)
  have hx₂β : capTo (x*x) 2 (show (k-3)-2=k-5 by omega) β =
      tensorInput D 9 F 10 C q 4 5 (by decide) k α := by
    rw [capTo_product x x 1 1 hx (show (k-3)-1=k-4 by omega)
      (show (k-4)-1=k-5 by omega), hxβ]
    apply eq_of_heq
    exact (gradedDegreeCast_heq _ _).trans
      (line_tensorInput_succ D 9 F 10 C q 3 4 (by decide) k α)
  have hpush₀ : P (k-3) β = c k 3 α :=
    push_tensorInput_eq_signed D 9 F 10 C q 2 3 (by decide) k α
  have hpush₁ : P (k-4) (capTo x 1 (by omega) β) = c k 4 α := by
    rw [hxβ]
    exact push_tensorInput_eq_signed D 9 F 10 C q 3 4 (by decide) k α
  have hpush₂ : P (k-5) (capTo (x*x) 2 (by omega) β) = c k 5 α := by
    rw [hx₂β]
    exact push_tensorInput_eq_signed D 9 F 10 C q 4 5 (by decide) k α
  have hterm₀ : P (k-9) (capTo Q₀ 6 (by omega) β) =
      capTo B₀ 6 (by omega) (c k 3 α) := by
    have h := properPush_capTo C qP q (bundleProj D) rfl Q₀ B₀ hP₀ 6
      (k:=k-3) (m:=k-9) (by omega) β
    change P (k-9) (capTo Q₀ 6 (by omega) β) =
      capTo B₀ 6 (by omega) (P (k-3) β) at h
    rw [hpush₀] at h
    simpa only [capTo_def, Nat.cast_ofNat] using h
  have hterm₁ : P (k-9) (capTo (x*Q₁) 6 (by omega) β) =
      capTo B₁ 5 (by omega) (c k 4 α) := by
    rw [hxQ₁.eq, capTo_product Q₁ x 5 1 hx (show (k-3)-1=k-4 by omega)
      (show (k-4)-5=k-9 by omega)]
    rw [properPush_capTo C qP q (bundleProj D) rfl Q₁ B₁ hP₁, hpush₁]
  have hterm₂ : P (k-9) (capTo ((x*x)*Q₂) 6 (by omega) β) =
      capTo B₂ 4 (by omega) (c k 5 α) := by
    rw [hxQ₂.eq, capTo_product Q₂ (x*x) 4 2 (hx.mul hx)
      (show (k-3)-2=k-5 by omega) (show (k-5)-4=k-9 by omega)]
    rw [properPush_capTo C qP q (bundleProj D) rfl Q₂ B₂ hP₂, hpush₂]
  have hfinal : B₀ * homComponent 3 c + B₁ * homComponent 4 c + B₂ * homComponent 5 c =
      orderedWords C q c := by
    dsimp only [B₀, B₁, B₂, orderedWords]
    noncomm_ring
  calc
    tripleTensorPush D F C q k α =
        P (k-9) (capTo (Q₀+x*Q₁+(x*x)*Q₂) 6 (by omega) β) := by
      dsimp only [tripleTensorPush]
      rw [doubleTensorPush_eq, hmiddle]
      rfl
    _ = capTo B₀ 6 (by omega) (c k 3 α) +
          capTo B₁ 5 (by omega) (c k 4 α) + capTo B₂ 4 (by omega) (c k 5 α) := by
      change P (k-9) (gradedDegreeCast _ _ (_+_+_)) = _
      rw [map_add, map_add, map_add, map_add]
      simpa only [capTo_def, Nat.cast_ofNat] using
        congrArg₂ (fun v w : chowGroup C q (k-9) => v+w)
          (congrArg₂ (fun v w : chowGroup C q (k-9) => v+w) hterm₀ hterm₁) hterm₂
    _ = (B₀ * homComponent 3 c + B₁ * homComponent 4 c + B₂ * homComponent 5 c) k 9 α := by
      rw [Pi.add_apply, Pi.add_apply, AddMonoidHom.add_apply,
        Pi.add_apply, Pi.add_apply, AddMonoidHom.add_apply]
      rw [mul_apply_of_homogeneous_right B₀ (isHomogeneous_homComponent 3 c) 6,
        mul_apply_of_homogeneous_right B₁ (isHomogeneous_homComponent 4 c) 5,
        mul_apply_of_homogeneous_right B₂ (isHomogeneous_homComponent 5 c) 4]
      simp only [homComponent_apply_self]
    _ = _ := congrArg (fun a : GradedCapFamily (chowGroup C q) => a k 9 α) hfinal

end M9Native.ChowThirdTensorGysin

namespace M9Native.ChowThirdTensorGysin
open GradedCapVirtualSchur

/-- On the genuine dual source, the actual three pushes give the
ordinary virtual Schur operator, with actual coefficient commutation
and native Chern duality both derived internally. -/
theorem tripleTensorPush_dual_eq_schur {X : Scheme.{u}} (E F : X.Modules)
    [hE : SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} E 10]
    [SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} F 10]
    (C : ChowSituation.{u}) (q : X ⟶ C.S) [LocallyOfFiniteType q] :
    letI := isFiniteLocallyFreeOfRank_dualSheaf E 10 hE
    ∀ (k : ℤ) (α : chowGroup C q k),
      tripleTensorPush (dualSheaf E) F C q k α =
        schur333 (virtualFamily C q F E 10 10) k 9 α := by
  letI := isFiniteLocallyFreeOfRank_dualSheaf E 10 hE
  intro k α
  rw [tripleTensorPush_eq_orderedWords,
    ChowSignedVirtualFamily.dual_source_eq_virtual C q F E 10 10]
  exact congrArg (fun a : GradedCapFamily (chowGroup C q) => a k 9 α)
    (ChowVirtualSchurWords.ordered_words_eq_schur333 C q F E 10 10)

end M9Native.ChowThirdTensorGysin
