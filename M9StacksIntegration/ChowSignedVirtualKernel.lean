module

public import M9StacksIntegration.ChowTautologicalKernelInverse
public import M9StacksIntegration.ChowSignedVirtualFamily
public import M9StacksIntegration.ChowFlagMomentCoefficients
public import M9StacksIntegration.ChowChernLineCommutation

/-!
# Signed-source families on the actual tautological kernel

The original kernel row gives its actual quotient-line factor. The
factorization and every positive homogeneous coefficient are conclusions
of genuine Whitney and line-cap commutation, with no Chern identity
supplied as a premise.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
set_option maxRecDepth 4096
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Stacks.Chow
open Stacks.Chow.GenuineChern
universe u
namespace M9Native.ChowSignedVirtualKernel
open GradedCapVirtualSchur ChowCapWords GradedLineCapSubring

variable {X : Scheme.{u}} (U : X.Modules) (n : ℕ)
    [hU : SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} U (n+2)]
    (C : ChowSituation.{u})

theorem family_kernel_eq_line_factor :
    letI := hU.isFiniteLocallyFree
    letI := Stacks.Chow.isFiniteLocallyFreeOfRank_kernel_bundleTautological U (n+1) hU
    letI := AlgebraicGeometry.isFiniteLocallyFreeOfRank_pullback (bundleProj U) U (n+2)
    ∀ (q : bundle U ⟶ C.S) [LocallyOfFiniteType q]
      (F : (bundle U).Modules) (r : ℕ)
      [SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} F r],
      ChowSignedVirtualFamily.family C q F (kernel (bundleTautological U)) r (n+1) =
        (1-lineFamily C q ⟨bundleTwist U, Stacks.Chow.isInvertible_bundleTwist U⟩) *
          ChowSignedVirtualFamily.family C q F
            ((Scheme.Modules.pullback (bundleProj U)).obj U) r (n+2) := by
  letI := hU.isFiniteLocallyFree
  letI := Stacks.Chow.isFiniteLocallyFreeOfRank_kernel_bundleTautological U (n+1) hU
  letI := AlgebraicGeometry.isFiniteLocallyFreeOfRank_pullback (bundleProj U) U (n+2)
  intro q _ F r _
  let L : InvertibleLine (bundle U) :=
    ⟨bundleTwist U, Stacks.Chow.isInvertible_bundleTwist U⟩
  have hkernel := ChowTautologicalKernelInverse.signScale_inverseFamily_kernel U (n+1) C q
  have hline := ChowFlagMomentCoefficients.signed_chernFamily_line C q L
  have hcomm := ChowChernLineCommutation.chernFamily_commute_lineFamily C q F r L
  have hmove : chernFamily C q F r * (1-lineFamily C q L) =
      (1-lineFamily C q L) * chernFamily C q F r := by
    rw [mul_sub, mul_one, sub_mul, one_mul, hcomm.eq]
  dsimp only [ChowSignedVirtualFamily.family]
  rw [hkernel, hline, ← mul_assoc, hmove, mul_assoc]

theorem family_kernel_coefficients :
    letI := hU.isFiniteLocallyFree
    letI := Stacks.Chow.isFiniteLocallyFreeOfRank_kernel_bundleTautological U (n+1) hU
    letI := AlgebraicGeometry.isFiniteLocallyFreeOfRank_pullback (bundleProj U) U (n+2)
    ∀ (q : bundle U ⟶ C.S) [LocallyOfFiniteType q]
      (F : (bundle U).Modules) (r : ℕ)
      [SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} F r]
      (m : ℕ) (hm : 1 ≤ m),
      homComponent m
          (ChowSignedVirtualFamily.family C q F (kernel (bundleTautological U)) r (n+1)) =
        homComponent m (ChowSignedVirtualFamily.family C q F
            ((Scheme.Modules.pullback (bundleProj U)).obj U) r (n+2)) -
          lineFamily C q ⟨bundleTwist U, Stacks.Chow.isInvertible_bundleTwist U⟩ *
            homComponent (m-1) (ChowSignedVirtualFamily.family C q F
              ((Scheme.Modules.pullback (bundleProj U)).obj U) r (n+2)) := by
  letI := hU.isFiniteLocallyFree
  letI := Stacks.Chow.isFiniteLocallyFreeOfRank_kernel_bundleTautological U (n+1) hU
  letI := AlgebraicGeometry.isFiniteLocallyFreeOfRank_pullback (bundleProj U) U (n+2)
  intro q _ F r _ m hm
  rw [family_kernel_eq_line_factor U n C q F r]
  exact ChowFlagMomentCoefficients.homComponent_one_sub_mul _ _
    (lineFamily_homogeneous C q _) m hm

end M9Native.ChowSignedVirtualKernel
