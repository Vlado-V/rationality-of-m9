module

public import M9StacksIntegration.CurveConstantRankSequences
public import StacksFrontier.AlgebraicGeometry.Modules.ReducedFiniteLocallyFree
public import StacksFrontier.AlgebraicGeometry.ProjectiveBundleSplitting.KernelConstantRankGeneral
public import StacksFrontier.AlgebraicGeometry.FiberRank.ConstantRank
public import StacksFrontier.AlgebraicGeometry.Variety.Smooth.Regular

/-!
# Actual bundle kernels, images, and cokernels from constant residue rank

On a reduced locally Noetherian scheme, the actual constant rank of a map
between finite locally free bundles makes its actual cokernel finite locally
free by native Tag 0FWH. The actual image and kernel are then finite locally
free as kernels of epimorphisms onto the derived bundles. All prescribed
ranks and the canonical residue-fibre kernel comparison follow.

The smooth integral curve specialization derives the scheme hypotheses.
No kernel/cokernel flatness or local-freeness witness is an input.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1200000
set_option maxRecDepth 4096

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace M9Native.CurveConstantRank

open TupleEvaluationFiber MukaiShortExactFiberRank
open CurveConstantRankFibers CurveConstantRankSequences

variable {X : Scheme.{u}}

/-- Actual finite local freeness and an actual constant fibre dimension
give the prescribed locally free rank, also on an empty scheme. -/
theorem finiteLocallyFreeOfRank_of_all_fiberRank (M : X.Modules) (r : ℕ)
    (hM : SheafOfModules.IsFiniteLocallyFree.{u,u,u} M)
    (hr : ∀ x : X, Scheme.Modules.fiberRank M x = r) :
    SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} M r := by
  let := hM
  have hres : SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u}
      (M.restrict (⊤ : X.Opens).ι) r :=
    Scheme.Modules.isFiniteLocallyFreeOfRank_restrict_of_fiberRank_eq M ⊤ r fun x _ => hr x
  have htop : Scheme.Modules.IsFiniteLocallyFreeOfRank M r :=
    Scheme.Modules.isFiniteLocallyFreeOfRank_of_iSup_eq_top (ι := PUnit.{u+1})
      (fun _ => (⊤ : X.Opens)) (by simp)
      (fun _ => (Scheme.Modules.isFiniteLocallyFreeOfRank_iff _ r).2 hres)
  exact (Scheme.Modules.isFiniteLocallyFreeOfRank_iff M r).1 htop

section Reduced

variable [IsReduced X] [IsLocallyNoetherian X]

/-- The original rank condition proves actual cokernel local freeness
by native reduced-scheme fibre-rank descent. -/
theorem cokernel_finiteLocallyFree {F G : X.Modules} (φ : F ⟶ G) (m n r : ℕ)
    (hF : SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} F m)
    (hG : SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} G n)
    (hr : MukaiSemiIrreducible.EverywhereRank φ r) :
    SheafOfModules.IsFiniteLocallyFree.{u,u,u} (cokernel φ) := by
  let := hF
  let := hG
  let : SheafOfModules.IsFiniteLocallyFree.{u,u,u} F := hF.isFiniteLocallyFree
  let : SheafOfModules.IsFiniteLocallyFree.{u,u,u} G := hG.isFiniteLocallyFree
  let : F.IsCoherent :=
    Stacks.AlgebraicGeometry.CoherenceCriteria.isCoherent_of_isFiniteLocallyFree X F
  let : G.IsCoherent :=
    Stacks.AlgebraicGeometry.CoherenceCriteria.isCoherent_of_isFiniteLocallyFree X G
  let : (cokernel φ).IsCoherent := _root_.SheafOfModules.cokernel_isCoherent φ
  let : (cokernel φ).IsQuasicoherent := _root_.isQuasicoherent_of_isCoherent _
  have hconst : Scheme.Modules.fiberRank (cokernel φ) = fun _ : X => n-r :=
    funext (cokernel_fiberRank_of_everywhereRank φ n r hr)
  have hlc : IsLocallyConstant (Scheme.Modules.fiberRank (cokernel φ)) := by
    rw [hconst]
    exact IsLocallyConstant.const _
  exact (Stacks.FiniteLocallyFree.Reduced.isFiniteLocallyFree_iff_isFiniteType_and_isLocallyConstant_fiberRank
    (cokernel φ)).mpr
      ⟨_root_.IsCoherent.toIsFiniteType _, hlc⟩

/-- The actual cokernel has the actual complementary constant rank. -/
theorem cokernel_rank {F G : X.Modules} (φ : F ⟶ G) (m n r : ℕ)
    (hF : SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} F m)
    (hG : SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} G n)
    (hr : MukaiSemiIrreducible.EverywhereRank φ r) :
    SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} (cokernel φ) (n-r) := by
  let := hG
  exact finiteLocallyFreeOfRank_of_all_fiberRank (cokernel φ) (n-r)
    (cokernel_finiteLocallyFree φ m n r hF hG hr)
    (cokernel_fiberRank_of_everywhereRank φ n r hr)

/-- The actual categorical image is locally free of the original
residue-map rank, rather than the fibre rank of an unsaturated substitute. -/
theorem image_rank {F G : X.Modules} (φ : F ⟶ G) (m n r : ℕ)
    (hF : SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} F m)
    (hG : SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} G n)
    (hr : MukaiSemiIrreducible.EverywhereRank φ r) :
    SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} (image φ) r := by
  let hQ := cokernel_rank φ m n r hF hG hr
  have hK := Stacks.ProjectiveBundleSplitting.isFiniteLocallyFreeOfRank_kernel_of_epi
    (cokernel.π φ) (by infer_instance) n (n-r) hG hQ
  have hIrank := SheafOfModules.IsFiniteLocallyFreeOfRank.of_iso (Abelian.imageIsoImage φ) hK
  let hI : SheafOfModules.IsFiniteLocallyFree.{u,u,u} (image φ) := hIrank.isFiniteLocallyFree
  apply finiteLocallyFreeOfRank_of_all_fiberRank (image φ) r hI
  intro x
  let := residueAlgebra x
  have hi : Function.Injective (inducedFiberMap (image.ι φ) x) :=
    fiberMap_injective_of_shortExact (imageCokernelSequence φ)
      (imageCokernelSequence_shortExact φ) hQ.isFiniteLocallyFree x
  have hRange := range_fiberMap_comp (factorThruImage φ) (image.ι φ) x
  rw [image.fac] at hRange
  rw [fiberRank_eq_finrank]
  calc
    Module.finrank (X.residueField x) (Fiber (image φ) x) =
        Module.finrank (X.residueField x) (LinearMap.range (inducedFiberMap (image.ι φ) x)) :=
      (LinearMap.finrank_range_of_inj hi).symm
    _ = Module.finrank (X.residueField x) (LinearMap.range (inducedFiberMap φ x)) :=
      congrArg (fun S : Submodule (X.residueField x) (Fiber G x) =>
        Module.finrank (X.residueField x) S) hRange.symm
    _ = r := hr x

/-- The actual original kernel has the actual source-complementary rank. -/
theorem kernel_rank {F G : X.Modules} (φ : F ⟶ G) (m n r : ℕ)
    (hF : SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} F m)
    (hG : SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} G n)
    (hr : MukaiSemiIrreducible.EverywhereRank φ r) :
    SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} (kernel φ) (m-r) := by
  have hI := image_rank φ m n r hF hG hr
  have hK := Stacks.ProjectiveBundleSplitting.isFiniteLocallyFreeOfRank_kernel_of_epi
    (factorThruImage φ) (by infer_instance) m r hF hI
  exact SheafOfModules.IsFiniteLocallyFreeOfRank.of_iso (kernelFactorThruImage φ) hK

/-- All three prescribed locally free ranks follow from the original
constant-rank map and the original two bundle ranks. -/
theorem ranks {F G : X.Modules} (φ : F ⟶ G) (m n r : ℕ)
    (hF : SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} F m)
    (hG : SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} G n)
    (hr : MukaiSemiIrreducible.EverywhereRank φ r) :
    SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} (kernel φ) (m-r) ∧
      SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} (image φ) r ∧
      SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} (cokernel φ) (n-r) :=
  ⟨kernel_rank φ m n r hF hG hr, image_rank φ m n r hF hG hr,
    cokernel_rank φ m n r hF hG hr⟩

/-- Original constant rank derives the canonical actual field-fibre
kernel equivalence, including the required local-freeness hypotheses. -/
def residueKernelEquiv {F G : X.Modules} (φ : F ⟶ G) (m n r : ℕ)
    (hF : SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} F m)
    (hG : SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} G n)
    (hr : MukaiSemiIrreducible.EverywhereRank φ r) (x : X) :
    Fiber (kernel φ) x ≃ₗ[X.residueField x] LinearMap.ker (inducedFiberMap φ x) := by
  letI : SheafOfModules.IsFiniteLocallyFree.{u,u,u} (image φ) :=
    (image_rank φ m n r hF hG hr).isFiniteLocallyFree
  letI : SheafOfModules.IsFiniteLocallyFree.{u,u,u} (cokernel φ) :=
    (cokernel_rank φ m n r hF hG hr).isFiniteLocallyFree
  exact fiberKernelEquiv φ x

/-- The derived comparison retains the actual original kernel inclusion. -/
theorem residueKernelEquiv_ι {F G : X.Modules} (φ : F ⟶ G) (m n r : ℕ)
    (hF : SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} F m)
    (hG : SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} G n)
    (hr : MukaiSemiIrreducible.EverywhereRank φ r) (x : X) (v : Fiber (kernel φ) x) :
    (residueKernelEquiv φ m n r hF hG hr x v).val = inducedFiberMap (kernel.ι φ) x v := rfl

end Reduced

/-- An actual smooth integral curve supplies reducedness and local
Noetherianity; the original residue rank determines all three actual bundles. -/
theorem ranks_on_smooth_curve (k : Type u) [Field k] (f : X ⟶ Spec (.of k))
    [IsCurve k f] [Smooth f] {F G : X.Modules} (φ : F ⟶ G) (m n r : ℕ)
    (hF : SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} F m)
    (hG : SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} G n)
    (hr : MukaiSemiIrreducible.EverywhereRank φ r) :
    SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} (kernel φ) (m-r) ∧
      SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} (image φ) r ∧
      SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} (cokernel φ) (n-r) := by
  let : IsLocallyNoetherian X := isLocallyNoetherian_of_isRegular (isRegular_of_smooth_over_field f)
  exact ranks φ m n r hF hG hr

/-- The canonical actual field-fibre kernel comparison on the original smooth curve. -/
def residueKernelEquiv_on_smooth_curve (k : Type u) [Field k]
    (f : X ⟶ Spec (.of k)) [IsCurve k f] [Smooth f]
    {F G : X.Modules} (φ : F ⟶ G) (m n r : ℕ)
    (hF : SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} F m)
    (hG : SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} G n)
    (hr : MukaiSemiIrreducible.EverywhereRank φ r) (x : X) :
    Fiber (kernel φ) x ≃ₗ[X.residueField x] LinearMap.ker (inducedFiberMap φ x) := by
  letI : IsLocallyNoetherian X := isLocallyNoetherian_of_isRegular (isRegular_of_smooth_over_field f)
  exact residueKernelEquiv φ m n r hF hG hr x

/-- The smooth-curve comparison has the literal original inclusion on fibres. -/
theorem residueKernelEquiv_on_smooth_curve_ι (k : Type u) [Field k]
    (f : X ⟶ Spec (.of k)) [IsCurve k f] [Smooth f]
    {F G : X.Modules} (φ : F ⟶ G) (m n r : ℕ)
    (hF : SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} F m)
    (hG : SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} G n)
    (hr : MukaiSemiIrreducible.EverywhereRank φ r) (x : X) (v : Fiber (kernel φ) x) :
    (residueKernelEquiv_on_smooth_curve k f φ m n r hF hG hr x v).val =
      inducedFiberMap (kernel.ι φ) x v := rfl

end M9Native.CurveConstantRank
