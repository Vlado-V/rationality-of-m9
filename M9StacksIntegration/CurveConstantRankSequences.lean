module

public import M9StacksIntegration.CurveConstantRankFibers

/-!
# Canonical image sequences and the actual field-fibre kernel comparison

The short exact sequences use the original categorical kernel, image,
and cokernel with their original maps. Once the actual image and cokernel
are locally free, the canonical map on residue-field fibres identifies
the fibre of the original kernel with the kernel of the original fibre map.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1200000
set_option maxRecDepth 4096

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace M9Native.CurveConstantRankSequences

open MukaiSaturationRank TupleEvaluationFiber MukaiShortExactFiberRank
open CurveConstantRankFibers

variable {X : Scheme.{u}}

/-- The literal kernel-to-source-to-image sequence of the original map. -/
def kernelImageSequence {F G : X.Modules} (φ : F ⟶ G) : ShortComplex X.Modules :=
  ShortComplex.mk (kernel.ι φ) (factorThruImage φ) (by
    apply (cancel_mono (image.ι φ)).mp
    rw [Category.assoc, image.fac, kernel.condition, zero_comp])

/-- Its exactness is the actual abelian kernel/image factorization. -/
theorem kernelImageSequence_shortExact {F G : X.Modules} (φ : F ⟶ G) :
    (kernelImageSequence φ).ShortExact := by
  refine { exact := ?_, mono_f := ?_, epi_g := ?_ }
  · exact ShortComplex.exact_of_g_is_cokernel _ (ShortComplex.exact_kernel φ).isColimitImage
  · change Mono (kernel.ι φ)
    infer_instance
  · change Epi (factorThruImage φ)
    infer_instance

/-- The literal image-to-target-to-cokernel sequence of the original map. -/
def imageCokernelSequence {F G : X.Modules} (φ : F ⟶ G) : ShortComplex X.Modules :=
  ShortComplex.mk (image.ι φ) (cokernel.π φ) (by
    apply (cancel_epi (factorThruImage φ)).mp
    rw [← Category.assoc, image.fac, cokernel.condition, comp_zero])

/-- Its exactness retains the original image inclusion and cokernel projection. -/
theorem imageCokernelSequence_shortExact {F G : X.Modules} (φ : F ⟶ G) :
    (imageCokernelSequence φ).ShortExact := by
  refine { exact := ?_, mono_f := ?_, epi_g := ?_ }
  · exact ShortComplex.exact_of_f_is_kernel _ (ShortComplex.exact_cokernel φ).isLimitImage'
  · change Mono (image.ι φ)
    infer_instance
  · change Epi (cokernel.π φ)
    infer_instance

/-- The canonical actual residue-fibre map into the kernel of the
original residue-fibre map; this map is defined before any freeness result. -/
def fiberKernelMap {F G : X.Modules} (φ : F ⟶ G) (x : X) :
    Fiber (kernel φ) x →ₗ[X.residueField x] LinearMap.ker (inducedFiberMap φ x) := by
  let := residueAlgebra x
  refine LinearMap.codRestrict _ (inducedFiberMap (kernel.ι φ) x) ?_
  intro v
  rw [LinearMap.mem_ker]
  have h := stalkMap_exact (ShortComplex.mk (kernel.ι φ) φ (kernel.condition φ))
    (ShortComplex.exact_kernel φ) x
  change ((stalkMap φ x).baseChange (X.residueField x))
    (((stalkMap (kernel.ι φ) x).baseChange (X.residueField x)) v) = 0
  rw [← LinearMap.comp_apply, ← LinearMap.baseChange_comp,
    h.linearMap_comp_eq_zero, LinearMap.baseChange_zero, LinearMap.zero_apply]

/-- Derived local freeness of the actual image and cokernel proves
bijectivity of the canonical original fibre-kernel map. -/
theorem fiberKernelMap_bijective {F G : X.Modules} (φ : F ⟶ G)
    [SheafOfModules.IsFiniteLocallyFree.{u,u,u} (image φ)]
    [SheafOfModules.IsFiniteLocallyFree.{u,u,u} (cokernel φ)] (x : X) :
    Function.Bijective (fiberKernelMap φ x) := by
  let := residueAlgebra x
  have hK := kernelImageSequence_shortExact φ
  have hQ := imageCokernelSequence_shortExact φ
  have hk : Function.Injective (inducedFiberMap (kernel.ι φ) x) :=
    fiberMap_injective_of_shortExact (kernelImageSequence φ) hK
      (by change SheafOfModules.IsFiniteLocallyFree.{u,u,u} (image φ); infer_instance) x
  have hi : Function.Injective (inducedFiberMap (image.ι φ) x) :=
    fiberMap_injective_of_shortExact (imageCokernelSequence φ) hQ
      (by change SheafOfModules.IsFiniteLocallyFree.{u,u,u} (cokernel φ); infer_instance) x
  let : Epi (kernelImageSequence φ).g := hK.epi_g
  have hex := fiberMap_exact (kernelImageSequence φ) hK.exact x
  change Function.Exact (inducedFiberMap (kernel.ι φ) x)
    (inducedFiberMap (factorThruImage φ) x) at hex
  refine ⟨fun a b hab => hk (congrArg Subtype.val hab), ?_⟩
  intro v
  have hv : inducedFiberMap (factorThruImage φ) x v.val = 0 := by
    apply hi
    rw [map_zero, ← LinearMap.comp_apply, ← fiberMap_comp, image.fac]
    exact v.property
  obtain ⟨a,ha⟩ := (hex v.val).mp hv
  exact ⟨a, Subtype.ext ha⟩

/-- The actual field-fibre kernel equivalence induced by the original
kernel inclusion; its bijectivity is derived from the actual short exacts. -/
def fiberKernelEquiv {F G : X.Modules} (φ : F ⟶ G)
    [SheafOfModules.IsFiniteLocallyFree.{u,u,u} (image φ)]
    [SheafOfModules.IsFiniteLocallyFree.{u,u,u} (cokernel φ)] (x : X) :
    Fiber (kernel φ) x ≃ₗ[X.residueField x] LinearMap.ker (inducedFiberMap φ x) :=
  LinearEquiv.ofBijective (fiberKernelMap φ x) (fiberKernelMap_bijective φ x)

/-- The equivalence's underlying map is the actual fibre of the original inclusion. -/
theorem fiberKernelEquiv_ι {F G : X.Modules} (φ : F ⟶ G)
    [SheafOfModules.IsFiniteLocallyFree.{u,u,u} (image φ)]
    [SheafOfModules.IsFiniteLocallyFree.{u,u,u} (cokernel φ)]
    (x : X) (v : Fiber (kernel φ) x) :
    (fiberKernelEquiv φ x v).val = inducedFiberMap (kernel.ι φ) x v := rfl

end M9Native.CurveConstantRankSequences
