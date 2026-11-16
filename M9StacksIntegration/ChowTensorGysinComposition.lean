module

public import M9StacksIntegration.ChowProjectiveTensorInput
public import M9StacksIntegration.GradedCapSegreComparison

/-!
# Composition of two original projective tensor Gysin maps

The two maps are the actual projective bundles of a rank-nine bundle
and its original tautological kernel. The input class and both proper
pushforwards are the native Chow operations. The quadratic coefficient
expression is a conclusion of the two genuine geometric Gysin formulas.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
set_option maxRecDepth 4096
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Stacks.Chow
open Stacks.Chow.GenuineChern
universe u v
namespace M9Native.ChowTensorGysinComposition
open GradedCapVirtualSchur ChowCapWords GradedLineCapSubring
open ChowProjectiveTensorInput

section Generic
variable {G : ℤ → Type v} [∀ k, AddCommGroup (G k)]

/-- Ordered homogeneous convolution in explicitly chosen equal grades. -/
theorem capTo_product (a b : GradedCapFamily G) (i j : ℕ)
    (hb : b.IsHomogeneous j) {k l m : ℤ}
    (h₀ : k-(j:ℤ)=l) (h₁ : l-(i:ℤ)=m) (α : G k) :
    capTo (a*b) (i+j) (by push_cast; omega) α =
      capTo a i h₁ (capTo b j h₀ α) := by
  rw [capTo_def, mul_apply_of_homogeneous_right a hb i k α,
    gradedDegreeCast_capTo, capTo_capTo]

end Generic

section Proper
variable (C : ChowSituation.{u}) {X Y : Scheme.{u}}
    (qX : X ⟶ C.S) [LocallyOfFiniteType qX]
    (qY : Y ⟶ C.S) [LocallyOfFiniteType qY]
    (p : X ⟶ Y) [IsProper p] (hp : p ≫ qY=qX)

/-- A genuine proper intertwiner also applies in any displayed equal
output grade. The hypothesis is only the native algebraic intertwiner. -/
theorem properPush_capTo (a : GradedCapFamily (chowGroup C qX))
    (b : GradedCapFamily (chowGroup C qY))
    (h : Intertwines (d:=0) (ChowLineProperPush.actualPush C qX qY p hp) a b)
    (i : ℕ) {k m : ℤ} (hm : k-(i:ℤ)=m) (β : chowGroup C qX k) :
    ChowLineProperPush.properPush C qX qY p hp m (capTo a i hm β) =
      capTo b i hm (ChowLineProperPush.properPush C qX qY p hp k β) := by
  subst m
  exact (ChowLineProperPush.intertwines_iff C qX qY p hp a b).1 h k i β

end Proper

variable {X : Scheme.{u}} (E : X.Modules)
    [hE : SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} E 9]
    (F : X.Modules) [hF : SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} F 10]
    (C : ChowSituation.{u}) (q : X ⟶ C.S) [LocallyOfFiniteType q]

local instance sourceFinite : SheafOfModules.IsFiniteLocallyFree.{u,u,u} E :=
  hE.isFiniteLocallyFree
local instance sourceFlat : Flat (bundleProj E) :=
  @Stacks.Chow.flat_bundleProj X E 8 hE
local instance sourceLFT : LocallyOfFiniteType (bundleProj E) :=
  @Stacks.Chow.locallyOfFiniteType_bundleProj X E 8 hE
local instance kernelRank : SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u}
    (ChowFlagMoments.firstKernel E) 8 :=
  Stacks.Chow.isFiniteLocallyFreeOfRank_kernel_bundleTautological E 8 hE
local instance pulledTargetRank : SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u}
    ((Scheme.Modules.pullback (bundleProj E)).obj F) 10 :=
  AlgebraicGeometry.isFiniteLocallyFreeOfRank_pullback (bundleProj E) F 10
local instance pulledSourceRank : SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u}
    ((Scheme.Modules.pullback (bundleProj E)).obj E) 9 :=
  AlgebraicGeometry.isFiniteLocallyFreeOfRank_pullback (bundleProj E) E 9

/-- The two successive actual projective tensor pushes. The first
normalizing quotient cap is inside the actual rank-nine input. -/
def doubleTensorPush (k : ℤ) (α : chowGroup C q k) : chowGroup C q (k-6) :=
  ChowLineProperPush.properPush C (bundleProj E ≫ q) q (bundleProj E) rfl (k-6)
    (chowGroupCast C (bundleProj E ≫ q) (by omega)
      (@ChowProjectiveTensorPush.tensorProjection (bundle E)
        (ChowFlagMoments.firstKernel E) 7 (kernelRank E)
        ((Scheme.Modules.pullback (bundleProj E)).obj F) 10 (pulledTargetRank E F)
        C (bundleProj E ≫ q) inferInstance
        0 3 (by decide) (k-3)
        (tensorInput E 8 F 10 C q 1 3 (by decide) k α)))

/-- The actual two Gysin pushes give the ordered quadratic coefficient
expression. No coefficient commutation or push formula is a premise. -/
theorem doubleTensorPush_eq (k : ℤ) (α : chowGroup C q k) :
    doubleTensorPush E F C q k α =
      (homComponent 3 (ChowSignedVirtualFamily.family C q F E 10 9) *
          homComponent 3 (ChowSignedVirtualFamily.family C q F E 10 9) -
        homComponent 2 (ChowSignedVirtualFamily.family C q F E 10 9) *
          homComponent 4 (ChowSignedVirtualFamily.family C q F E 10 9)) k 6 α := by
  let qP := bundleProj E ≫ q
  let PE := (Scheme.Modules.pullback (bundleProj E)).obj E
  let PF := (Scheme.Modules.pullback (bundleProj E)).obj F
  let A := ChowSignedVirtualFamily.family C qP PF PE 10 9
  let c := ChowSignedVirtualFamily.family C q F E 10 9
  let L : InvertibleLine (bundle E) :=
    ⟨bundleTwist E, Stacks.Chow.isInvertible_bundleTwist E⟩
  let y := lineFamily C qP L
  let β := tensorInput E 8 F 10 C q 1 3 (by decide) k α
  let P := fun l => ChowLineProperPush.properPush C qP q (bundleProj E) rfl l
  have hproper := ChowSignedVirtualFamily.properPush C qP q (bundleProj E) rfl
    E 9 PE (Iso.refl _) F 10 PF (Iso.refl _)
  have hcomm := ChowSignedVirtualLineCommutation.lineFamily_commute_homComponent
    C qP PE 9 L PF 10 2
  have hinner := ChowKernelTensorGysin.tensorProjection_eq_parent_coefficients E 7
    C qP PF 10 0 3 (by decide) (by decide) (k-3) β
  have hline : capTo y 1 (show (k-3)-1=k-4 by omega) β =
      tensorInput E 8 F 10 C q 2 4 (by decide) k α := by
    apply eq_of_heq
    exact (gradedDegreeCast_heq _ _).trans
      (line_tensorInput_succ E 8 F 10 C q 1 3 (by decide) k α)
  have hP₁ : P (k-3) β = c k 3 α :=
    push_tensorInput_eq_signed E 8 F 10 C q 1 3 (by decide) k α
  have hP₂ : P (k-4) (capTo y 1 (by omega) β) = c k 4 α := by
    rw [hline]
    exact push_tensorInput_eq_signed E 8 F 10 C q 2 4 (by decide) k α
  have hterm₁ : P (k-6) (capTo (homComponent 3 A) 3 (by omega) β) =
      capTo c 3 (by omega) (c k 3 α) := by
    have h := properPush_capTo C qP q (bundleProj E) rfl A c hproper 3
      (k:=k-3) (m:=k-6) (by omega) β
    change P (k-6) (capTo A 3 (by omega) β) =
      capTo c 3 (by omega) (P (k-3) β) at h
    rw [hP₁] at h
    simpa only [capTo_def, homComponent_apply_self, Nat.cast_ofNat] using h
  have hterm₂ : P (k-6) (capTo (y * homComponent 2 A) 3 (by omega) β) =
      capTo c 2 (by omega) (c k 4 α) := by
    rw [hcomm.eq]
    rw [capTo_product (homComponent 2 A) y 2 1 (lineFamily_homogeneous C qP L)
      (show (k-3)-1=k-4 by omega) (show (k-4)-2=k-6 by omega)]
    have h := properPush_capTo C qP q (bundleProj E) rfl A c hproper 2
      (k:=k-4) (m:=k-6) (by omega)
      (capTo y 1 (show (k-3)-1=k-4 by omega) β)
    change P (k-6) (capTo A 2 (by omega) (capTo y 1 (by omega) β)) =
      capTo c 2 (by omega) (P (k-4) (capTo y 1 (by omega) β)) at h
    rw [hP₂] at h
    simpa only [capTo_def, homComponent_apply_self, Nat.cast_ofNat] using h
  calc
    doubleTensorPush E F C q k α =
        P (k-6) (capTo (homComponent 3 A - y*homComponent 2 A) 3 (by omega) β) := by
      dsimp only [doubleTensorPush]
      rw [hinner]
      rfl
    _ = capTo c 3 (by omega) (c k 3 α) - capTo c 2 (by omega) (c k 4 α) := by
      change P (k-6) (gradedDegreeCast _ _ (_-_)) = _
      rw [map_sub, map_sub]
      simpa only [capTo_def, Nat.cast_ofNat] using
        congrArg₂ (fun v w : chowGroup C q (k-6) => v-w) hterm₁ hterm₂
    _ = _ := by
      rw [Pi.sub_apply, Pi.sub_apply, AddMonoidHom.sub_apply,
        GradedCapSegreComparison.homComponent_mul_apply c c 3 3 6 (by decide),
        GradedCapSegreComparison.homComponent_mul_apply c c 2 4 6 (by decide)]

end M9Native.ChowTensorGysinComposition
