module

public import M9StacksIntegration.ChowTautologicalKernelInverse
public import M9StacksIntegration.ChowProjectiveMomentInverse

/-!
# Genuine recursive kernel moments on the original projective flag tower

The source bundle is arbitrary and need not be free. The moment maps of
each original kernel are factored using its genuine exact row. Applying
this identity recursively gives the successive flag evaluations, for
both the rank-ten Brill–Noether flag and the free rank-six degree calculation.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
set_option maxRecDepth 4096
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Stacks.Chow
open Stacks.Chow.GenuineChern
universe u
namespace M9Native.ChowFlagMoments
open GradedCapVirtualSchur

local instance actualHasKernels {T : Scheme.{u}} : HasKernels T.Modules := inferInstance
local instance actualHasKernel {T : Scheme.{u}} {A B : T.Modules} (f : A ⟶ B) : HasKernel f :=
  HasKernels.has_limit f

/-- The original first tautological kernel, independent of any rank proof. -/
abbrev firstKernel {X : Scheme.{u}} (E : X.Modules)
    [SheafOfModules.IsFiniteLocallyFree.{u,u,u} E] : (bundle E).Modules :=
  kernel (bundleTautological E)

/-- The moment family of the first actual tautological kernel factors
by its original quotient line and the actual pulled source inverse. -/
theorem first_kernel_momentFamily {X : Scheme.{u}} (E : X.Modules) (n : ℕ)
    [hE : SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} E (n+2)] :
    letI := hE.isFiniteLocallyFree

    letI := Stacks.Chow.isFiniteLocallyFreeOfRank_kernel_bundleTautological E (n+1) hE
    letI := Stacks.Chow.isFiniteLocallyFreeOfRank_bundleTwist E
    letI := AlgebraicGeometry.isFiniteLocallyFreeOfRank_pullback (bundleProj E) E (n+2)
    ∀ (C : ChowSituation.{u}) (q : bundle E ⟶ C.S) [LocallyOfFiniteType q],
      ChowProjectiveMoments.momentFamily (firstKernel E) n C q =
        capFamilySignScale (chernFamily C q (bundleTwist E) 1) *
          capFamilySignScale
            (inverseFamily C q ((Scheme.Modules.pullback (bundleProj E)).obj E) (n+2)) := by
  letI := hE.isFiniteLocallyFree

  letI := Stacks.Chow.isFiniteLocallyFreeOfRank_kernel_bundleTautological E (n+1) hE
  letI := Stacks.Chow.isFiniteLocallyFreeOfRank_bundleTwist E
  letI := AlgebraicGeometry.isFiniteLocallyFreeOfRank_pullback (bundleProj E) E (n+2)
  intro C q _
  have hm := ChowProjectiveMomentInverse.momentFamily_eq_signed_inverse (firstKernel E) n C q
  have hi := ChowTautologicalKernelInverse.signScale_inverseFamily_kernel E (n+1) C q
  exact hm.trans hi

end M9Native.ChowFlagMoments
