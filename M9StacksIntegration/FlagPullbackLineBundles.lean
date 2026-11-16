module

public import M9StacksIntegration.PullbackQuotientLines
public import StacksFrontier.AlgebraicGeometry.ProjectiveBundleSplitting.PullbackStableLocallyFree

/-!
# Actual pullback of named kernel lines with locally free quotients

The hypotheses are local freeness of the original quotient sheaves.
The true short exact rows imply that their original inclusions remain
monic after arbitrary scheme pullback. The original normalized quotient
maps then identify the actual named kernel lines, including their
inclusions. No flatness of the test morphism, preserved-kernel hypothesis,
or line-isomorphism premise is supplied.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace M9Native.FlagPullbackLineBundles

variable {X Y : Scheme.{u}} (i : Y ⟶ X)

/-- A genuine short exact row with locally free quotient stays exact. -/
def kernelPullbackIso (S : ShortComplex X.Modules) (hS : S.ShortExact)
    (h₃ : _root_.SheafOfModules.IsLocallyFree S.X₃) :
    (Scheme.Modules.pullback i).obj S.X₁ ≅
      kernel ((Scheme.Modules.pullback i).map S.g) := by
  let e := (shortExact_map_pullback_of_isLocallyFree i hS h₃).fIsKernel.conePointUniqueUpToIso
    (kernelIsKernel ((Scheme.Modules.pullback i).map S.g))
  exact e

@[reassoc]
theorem kernelPullbackIso_hom_ι (S : ShortComplex X.Modules) (hS : S.ShortExact)
    (h₃ : _root_.SheafOfModules.IsLocallyFree S.X₃) :
    (kernelPullbackIso i S hS h₃).hom ≫
        kernel.ι ((Scheme.Modules.pullback i).map S.g) =
      (Scheme.Modules.pullback i).map S.f :=
  IsLimit.conePointUniqueUpToIso_hom_comp
    (shortExact_map_pullback_of_isLocallyFree i hS h₃).fIsKernel
    (kernelIsKernel ((Scheme.Modules.pullback i).map S.g)) WalkingParallelPair.zero

@[reassoc]
theorem kernelPullbackIso_inv_map (S : ShortComplex X.Modules) (hS : S.ShortExact)
    (h₃ : _root_.SheafOfModules.IsLocallyFree S.X₃) :
    (kernelPullbackIso i S hS h₃).inv ≫ (Scheme.Modules.pullback i).map S.f =
      kernel.ι ((Scheme.Modules.pullback i).map S.g) :=
  IsLimit.conePointUniqueUpToIso_inv_comp
    (shortExact_map_pullback_of_isLocallyFree i hS h₃).fIsKernel
    (kernelIsKernel ((Scheme.Modules.pullback i).map S.g)) WalkingParallelPair.zero

variable {M : X.Modules} {N : Y.Modules}
  (e : N ≅ (Scheme.Modules.pullback i).obj M)

/-- Monicity follows from local freeness of the original quotient. -/
instance mono_pullback_subobject_arrow (S : Subobject M)
    [hS : _root_.SheafOfModules.IsLocallyFree (cokernel S.arrow)] :
    Mono ((Scheme.Modules.pullback i).map S.arrow) := by
  have hs : (ShortComplex.mk S.arrow (cokernel.π S.arrow)
      (cokernel.condition S.arrow)).ShortExact :=
    { exact := ShortComplex.exact_cokernel S.arrow }
  exact (shortExact_map_pullback_of_isLocallyFree i hs hS).mono_f

variable {S S' : Subobject M}
  [hS : _root_.SheafOfModules.IsLocallyFree (cokernel S.arrow)]
  [hS' : _root_.SheafOfModules.IsLocallyFree (cokernel S'.arrow)]

/-- The actual kernel line of the actual pulled-back quotient step is
canonically the pullback of the original actual kernel line. -/
def quotientKernelIso (h : S ≤ S') :
    kernel (FlagQuotientLines.quotientStep
      (PullbackQuotientLines.subobjectPullback_le i e h)) ≅
        (Scheme.Modules.pullback i).obj (kernel (FlagQuotientLines.quotientStep h)) :=
  PullbackQuotientLines.quotientKernelMapIso i e h ≪≫
    (kernelPullbackIso i (FlagQuotientLines.quotientKernelSequence h)
      (FlagQuotientLines.quotientKernelSequence_shortExact h) hS').symm

@[reassoc]
theorem quotientKernelIso_hom_map_ι (h : S ≤ S') :
    (quotientKernelIso i e h).hom ≫
        (Scheme.Modules.pullback i).map (kernel.ι (FlagQuotientLines.quotientStep h)) =
      kernel.ι (FlagQuotientLines.quotientStep
        (PullbackQuotientLines.subobjectPullback_le i e h)) ≫
          (PullbackQuotientLines.quotientIso i e S).hom := by
  calc
    (quotientKernelIso i e h).hom ≫
        (Scheme.Modules.pullback i).map (kernel.ι (FlagQuotientLines.quotientStep h)) =
      (PullbackQuotientLines.quotientKernelMapIso i e h).hom ≫
        ((kernelPullbackIso i (FlagQuotientLines.quotientKernelSequence h)
          (FlagQuotientLines.quotientKernelSequence_shortExact h) hS').inv ≫
            (Scheme.Modules.pullback i).map (kernel.ι (FlagQuotientLines.quotientStep h))) :=
              Category.assoc _ _ _
    _ = (PullbackQuotientLines.quotientKernelMapIso i e h).hom ≫
        kernel.ι ((Scheme.Modules.pullback i).map (FlagQuotientLines.quotientStep h)) :=
      congrArg (fun a => (PullbackQuotientLines.quotientKernelMapIso i e h).hom ≫ a)
        (kernelPullbackIso_inv_map i (FlagQuotientLines.quotientKernelSequence h)
          (FlagQuotientLines.quotientKernelSequence_shortExact h) hS')
    _ = _ := PullbackQuotientLines.quotientKernelMapIso_hom_ι i e h

end M9Native.FlagPullbackLineBundles
