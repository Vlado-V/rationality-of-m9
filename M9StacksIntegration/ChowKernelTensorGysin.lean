module

public import M9StacksIntegration.ChowFlagMoments
public import M9StacksIntegration.ChowFlagMomentCoefficients
public import M9StacksIntegration.ChowSignedVirtualFamily
public import M9StacksIntegration.ChowChernLineCommutation
public import M9StacksIntegration.ChowProjectiveTensorPushFormula

/-!
# Genuine tensor Gysin on an original tautological kernel

The source of this projective bundle is the actual kernel of the
previous original tautological quotient. Its tensor top-Chern push is
computed from the actual single Gysin theorem and the genuine kernel
row. The two-term coefficient formula is a conclusion, with no
projection, inverse or commutation formula supplied as a premise.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
set_option maxRecDepth 4096
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Stacks.Chow
open Stacks.Chow.GenuineChern
universe u
namespace M9Native.ChowKernelTensorGysin
open GradedCapVirtualSchur ChowCapWords GradedLineCapSubring

/-- The actual tensor Gysin on an actual preceding kernel has the
original signed quotient-line factor and the original pulled source. -/
theorem tensorProjection_eq_signed_parent_product {X : Scheme.{u}}
    (U : X.Modules) (n : ℕ)
    [hU : SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} U (n+2)] :
    letI := hU.isFiniteLocallyFree
    letI := Stacks.Chow.isFiniteLocallyFreeOfRank_kernel_bundleTautological U (n+1) hU
    letI := Stacks.Chow.isFiniteLocallyFreeOfRank_bundleTwist U
    letI := AlgebraicGeometry.isFiniteLocallyFreeOfRank_pullback (bundleProj U) U (n+2)
    ∀ (C : ChowSituation.{u}) (q : bundle U ⟶ C.S) [LocallyOfFiniteType q]
      (F : (bundle U).Modules) (r : ℕ)
      [SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} F r]
      (a b : ℕ) (hab : r+a=n+b) (k : ℤ) (α : chowGroup C q k),
      ChowProjectiveTensorPush.tensorProjection (ChowFlagMoments.firstKernel U) n F r C q
        a b hab k α =
        (chernFamily C q F r *
          (capFamilySignScale (chernFamily C q (bundleTwist U) 1) *
            capFamilySignScale (inverseFamily C q
              ((Scheme.Modules.pullback (bundleProj U)).obj U) (n+2)))) k b α := by
  letI := hU.isFiniteLocallyFree
  letI := Stacks.Chow.isFiniteLocallyFreeOfRank_kernel_bundleTautological U (n+1) hU
  letI := Stacks.Chow.isFiniteLocallyFreeOfRank_bundleTwist U
  letI := AlgebraicGeometry.isFiniteLocallyFreeOfRank_pullback (bundleProj U) U (n+2)
  intro C q _ F r _ a b hab k α
  have hg := ChowProjectiveTensorPushFormula.tensorProjection_eq_chern_mul_moment
    (ChowFlagMoments.firstKernel U) n F r C q a b hab k α
  have hm := ChowFlagMoments.first_kernel_momentFamily U n C q
  exact hg.trans (congrArg (fun M : GradedCapFamily (chowGroup C q) =>
    (chernFamily C q F r * M) k b α) hm)

/-- The actual kernel tensor Gysin has the literal two ordered
homogeneous coefficient terms of its actual signed-parent family. -/
theorem tensorProjection_eq_parent_coefficients {X : Scheme.{u}}
    (U : X.Modules) (n : ℕ)
    [hU : SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} U (n+2)] :
    letI := hU.isFiniteLocallyFree
    letI := Stacks.Chow.isFiniteLocallyFreeOfRank_kernel_bundleTautological U (n+1) hU
    letI := Stacks.Chow.isFiniteLocallyFreeOfRank_bundleTwist U
    letI := AlgebraicGeometry.isFiniteLocallyFreeOfRank_pullback (bundleProj U) U (n+2)
    ∀ (C : ChowSituation.{u}) (q : bundle U ⟶ C.S) [LocallyOfFiniteType q]
      (F : (bundle U).Modules) (r : ℕ)
      [SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} F r]
      (a b : ℕ) (hab : r+a=n+b) (hb : 1 ≤ b) (k : ℤ) (α : chowGroup C q k),
      ChowProjectiveTensorPush.tensorProjection (ChowFlagMoments.firstKernel U) n F r C q
        a b hab k α =
        (homComponent b (ChowSignedVirtualFamily.family C q F
            ((Scheme.Modules.pullback (bundleProj U)).obj U) r (n+2)) -
          lineFamily C q ⟨bundleTwist U, Stacks.Chow.isInvertible_bundleTwist U⟩ *
            homComponent (b-1) (ChowSignedVirtualFamily.family C q F
              ((Scheme.Modules.pullback (bundleProj U)).obj U) r (n+2))) k b α := by
  letI := hU.isFiniteLocallyFree
  letI := Stacks.Chow.isFiniteLocallyFreeOfRank_kernel_bundleTautological U (n+1) hU
  letI := Stacks.Chow.isFiniteLocallyFreeOfRank_bundleTwist U
  letI := AlgebraicGeometry.isFiniteLocallyFreeOfRank_pullback (bundleProj U) U (n+2)
  intro C q _ F r _ a b hab hb k α
  let L : InvertibleLine (bundle U) :=
    ⟨bundleTwist U, Stacks.Chow.isInvertible_bundleTwist U⟩
  let x := lineFamily C q L
  let W := ChowSignedVirtualFamily.family C q F
    ((Scheme.Modules.pullback (bundleProj U)).obj U) r (n+2)
  have hsign := ChowFlagMomentCoefficients.signed_chernFamily_line C q L
  have hcomm := ChowChernLineCommutation.chernFamily_commute_lineFamily C q F r L
  have hmove : chernFamily C q F r * (1-x) = (1-x) * chernFamily C q F r := by
    rw [mul_sub, mul_one, sub_mul, one_mul, hcomm.eq]
  have hfactor : chernFamily C q F r *
      (capFamilySignScale (chernFamily C q (bundleTwist U) 1) *
        capFamilySignScale (inverseFamily C q
          ((Scheme.Modules.pullback (bundleProj U)).obj U) (n+2))) = (1-x)*W := by
    rw [hsign, ← mul_assoc, hmove, mul_assoc]
    rfl
  have hcoeff := ChowFlagMomentCoefficients.homComponent_one_sub_mul x W
    (lineFamily_homogeneous C q L) b hb
  have heval := congrArg (fun M : GradedCapFamily (chowGroup C q) => M k b α) hcoeff
  simp only [homComponent_apply_self] at heval
  have hg := tensorProjection_eq_signed_parent_product U n C q F r a b hab k α
  exact hg.trans ((congrArg (fun M : GradedCapFamily (chowGroup C q) => M k b α) hfactor).trans
    heval)

end M9Native.ChowKernelTensorGysin
