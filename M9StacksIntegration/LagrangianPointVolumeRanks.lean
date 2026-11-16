module

public import M9StacksIntegration.LagrangianPointKernelCoordinates

/-! The original primitive fourteen-vector and the full kernel-plane
trivector are related by one fixed injective linear map. Hence both
their span ranks and every finite deletion independence agree. No
pointwise scalar or exterior-volume comparison is assumed. -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory Module
universe u

namespace M9Native.LagrangianPointVolumeRanks
open LagrangianPointKernelCoordinates LagrangianPluckerDuality

variable (K : Type u) [Field K] [CharZero K]

def fourteen (p : Spec (.of K) ⟶ LagrangianGrassmannian.space K) : Fin 14 → K :=
  LagrangianField.rowFourteen K (matrix K p)

def volumeEmbedding : (Fin 14 → K) →ₗ[K] (⋀[K]^3 (Fin 6 → K)) :=
  (LagrangianField.coordinateEmbedding K).comp
    (LagrangianField.coordinateBasis14 K).equivFun.symm.toLinearMap

theorem volumeEmbedding_injective : Function.Injective (volumeEmbedding K) :=
  (LagrangianField.coordinateEmbedding_injective K).comp
    (LagrangianField.coordinateBasis14 K).equivFun.symm.injective

theorem volumeEmbedding_fourteen (p : Spec (.of K) ⟶ LagrangianGrassmannian.space K) :
    volumeEmbedding K (fourteen K p) = rowVolume K p := by
  have hσ : LagrangianField.quotientSigma K (matrix K p) = 0 :=
    (LagrangianField.quotientSigma_zero_iff_rows_isotropic K (matrix K p)).mpr
      (matrix_rows_isotropic K p)
  change LagrangianField.coordinateEmbedding K
    ((LagrangianField.coordinateBasis14 K).equivFun.symm
      ((LagrangianField.coordinateBasis14 K).equivFun
        (LagrangianField.coordinateProjection K (LagrangianField.rowPlucker K (matrix K p))))) = _
  rw [LinearEquiv.symm_apply_apply,
    LagrangianField.coordinateEmbedding_rowProjection K (matrix K p) hσ]
  unfold LagrangianField.rowPlucker LagrangianField.wedge3 rowVolume
  congr 1
  funext i
  fin_cases i <;> rfl

def kernelVolumeEmbedding : (Fin 14 → K) →ₗ[K] (⋀[K]^3 (Fin 6 → K)) :=
  (exteriorPower.map 3 (symplecticDuality K)).comp (volumeEmbedding K)

theorem kernelVolumeEmbedding_injective : Function.Injective (kernelVolumeEmbedding K) :=
  (exterior_symplecticDuality_injective K).comp (volumeEmbedding_injective K)

theorem kernelVolumeEmbedding_fourteen (p : Spec (.of K) ⟶ LagrangianGrassmannian.space K) :
    kernelVolumeEmbedding K (fourteen K p) = kernelVolume K p := by
  rw [kernelVolumeEmbedding, LinearMap.comp_apply, volumeEmbedding_fourteen,
    rowVolume_to_kernelVolume]

theorem finrank_span_injective_image {V W : Type u}
    [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
    {ι : Type u} (t : V →ₗ[K] W) (ht : Function.Injective t) (s : ι → V) :
    finrank K (Submodule.span K (Set.range (fun i => t (s i)))) =
      finrank K (Submodule.span K (Set.range s)) := by
  have h := (Submodule.equivMapOfInjective t ht (Submodule.span K (Set.range s))).finrank_eq.symm
  rwa [Submodule.map_span, ← Set.range_comp'] at h

theorem finrank_span_kernelVolume_eq_fourteen {ι : Type u}
    (p : ι → (Spec (.of K) ⟶ LagrangianGrassmannian.space K)) :
    finrank K (Submodule.span K (Set.range (fun i => kernelVolume K (p i)))) =
      finrank K (Submodule.span K (Set.range (fun i => fourteen K (p i)))) := by
  have h := finrank_span_injective_image K (kernelVolumeEmbedding K)
    (kernelVolumeEmbedding_injective K) (fun i => fourteen K (p i))
  have he : (fun i => kernelVolumeEmbedding K (fourteen K (p i))) =
      fun i => kernelVolume K (p i) := funext fun i => kernelVolumeEmbedding_fourteen K (p i)
  rw [he] at h
  exact h

theorem linearIndependent_kernelVolume_iff_fourteen {ι : Type u}
    (p : ι → (Spec (.of K) ⟶ LagrangianGrassmannian.space K)) :
    LinearIndependent K (fun i => kernelVolume K (p i)) ↔
      LinearIndependent K (fun i => fourteen K (p i)) := by
  have h := (kernelVolumeEmbedding K).linearIndependent_iff
    (v := fun i => fourteen K (p i))
    (LinearMap.ker_eq_bot.mpr (kernelVolumeEmbedding_injective K))
  simpa only [Function.comp_def, kernelVolumeEmbedding_fourteen] using h

end M9Native.LagrangianPointVolumeRanks
