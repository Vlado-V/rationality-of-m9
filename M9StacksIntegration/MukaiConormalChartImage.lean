module

public import M9StacksIntegration.MukaiConormalChartRatioData
public import M9StacksIntegration.MukaiConormalChartLinear

/-! The actual original determinant-twisted conormal Euler image is the
kernel of the literal value and universal-derivative tuple on every
actual étale affine-six chart. No image or first-jet equality is assumed. -/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false
set_option maxHeartbeats 1400000
set_option maxRecDepth 4096

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Module

universe u

namespace M9Native.MukaiConormalChartImage

open LagrangianGrassmannian LagrangianPlucker LagrangianPluckerQuotient
open MukaiConormalChartJets MukaiConormalOriginCoordinates

/-- The original native conormal map, computed from the original
primitive determinant sections in a real chart frame, has exactly the
actual value-and-differential kernel. -/
theorem range_formsMap_eq_ker_firstJetMap
    (K : Type u) [Field K] [CharZero K] [IsAlgClosed K]
    (f : chart K ⟶ space K) [Etale f]
    (hf : f ≫ projection K = chartProjection K)
    (z : Spec (.of K) ⟶ chart K)
    (hz : z ≫ chartProjection K = 𝟙 (Spec (.of K)))
    (e : (Scheme.Modules.pullback f).obj (determinantLine K) ≅
      SheafOfModules.unit (chart K).ringCatSheaf) :
    LinearMap.range (MukaiConormalFieldCoordinates.formsMap K (z ≫ f)) =
      LinearMap.ker (firstJetMap K z (fun j =>
        e.hom.app ⊤ (pullbackGlobalSections f (determinantLine K) (primitiveSections K j)))) := by
  let p := z ≫ f
  let v := MukaiConormalChartFrame.sectionTuple K f e
  let τ := MukaiConormalChartFrame.pointDeterminantFrame K f e z
  have hpBase : p ≫ projection K = 𝟙 (Spec (.of K)) := by
    change (z ≫ f) ≫ projection K = _
    rw [Category.assoc, hf, hz]
  obtain ⟨i,hp⟩ := MukaiConormalChartRatioData.pivot_exists K f z
  let r := MukaiConormalChartRatioData.pointRatio K f z i hp
  let b := MukaiConormalChartRatioData.pointBasis K f z e i hp
  let δ := MukaiConormalChartRatioData.inputDifferential K f hf z e
  have hδ : Function.Surjective δ :=
    MukaiConormalChartRatioData.inputDifferential_surjective K f hf z e
  have hi : value K z (v i) ≠ 0 :=
    MukaiConormalChartRatioData.pivot_ne_zero K f z e i hp
  have hv : ∀ j, value K z (v j) = r j * value K z (v i) :=
    MukaiConormalChartRatioData.ratio_values K f z e i hp
  have hd : ∀ j : {j : Fin 14 // j ≠ i},
      derivative K z (v j.1) - r j.1 • derivative K z (v i) =
        value K z (v i) • δ (b j) :=
    MukaiConormalChartRatioData.ratio_derivatives K f hf z e i hp
  have hsurj : Function.Surjective (firstJetMap K z v) :=
    MukaiConormalChartLinear.firstJetMap_surjective_of_ratio_data K z v i r b δ hδ hi hv hd
  let E : MukaiEulerFieldPoint.Source K p →ₗ[K] Module.Dual K (LagrangianField.Primitive K) :=
    (formsCoordinates K).symm.toLinearMap.comp (MukaiConormalLinearJets.eulerMap K r i b)
  have hE₁ : (valueMap K z v).comp E = 0 := by
    ext x
    change valueMap K z v ((formsCoordinates K).symm
      (MukaiConormalLinearJets.eulerMap K r i b x)) = 0
    rw [MukaiConormalChartLinear.valueMap_coordinates]
    exact congrArg (fun t : MukaiEulerFieldPoint.Source K p →ₗ[K] K => t x)
      (MukaiConormalLinearJets.valueMap_comp_eulerMap K (valueVector K z v) r i b hv)
  have hE₂ : (derivativeMap K z v).comp E = value K z (v i) • δ := by
    ext x
    change derivativeMap K z v ((formsCoordinates K).symm
      (MukaiConormalLinearJets.eulerMap K r i b x)) = _
    rw [MukaiConormalChartLinear.derivativeMap_coordinates]
    exact congrArg (fun t : MukaiEulerFieldPoint.Source K p →ₗ[K] PointCotangent K z => t x)
      (MukaiConormalLinearJets.derivativeMap_comp_eulerMap K (derivativeVector K z v) r i b
        δ (value K z (v i)) hd)
  have hle : LinearMap.range (MukaiConormalFieldCoordinates.formsMap K p) ≤
      LinearMap.ker (firstJetMap K z v) := by
    obtain ⟨a,ha,hfactor⟩ := MukaiConormalCoefficientImage.formsMap_factor K p τ i hp
    rintro ell ⟨y,rfl⟩
    change firstJetMap K z v (MukaiConormalFieldCoordinates.formsMap K p y) = 0
    have hx : δ (MukaiEulerFieldPoint.conormalInput K p y) = 0 :=
      MukaiConormalChartRatioData.inputDifferential_conormal_zero K f hf z e y
    have hzero : firstJetMap K z v (E (MukaiEulerFieldPoint.conormalInput K p y)) = 0 := by
      apply Prod.ext
      · exact congrArg (fun t : MukaiEulerFieldPoint.Source K p →ₗ[K] K =>
          t (MukaiEulerFieldPoint.conormalInput K p y)) hE₁
      · have h := congrArg (fun t : MukaiEulerFieldPoint.Source K p →ₗ[K] PointCotangent K z =>
          t (MukaiEulerFieldPoint.conormalInput K p y)) hE₂
        change derivativeMap K z v (E (MukaiEulerFieldPoint.conormalInput K p y)) = 0
        calc
          _ = value K z (v i) • δ (MukaiEulerFieldPoint.conormalInput K p y) := h
          _ = 0 := by rw [hx, smul_zero]
    rw [hfactor y]
    change firstJetMap K z v (a • E (MukaiEulerFieldPoint.conormalInput K p y)) = 0
    rw [map_smul, hzero, smul_zero]
  obtain ⟨hfinite,hT⟩ := MukaiConormalChartDifferential.target_finite_and_finrank K f hf z
  let : Module.Finite K (PointCotangent K z) := hfinite
  have hker : finrank K (LinearMap.ker (firstJetMap K z v)) = 7 :=
    MukaiConormalChartLinear.finrank_ker_firstJetMap K z v hT hsurj
  have hrange : finrank K (LinearMap.range (MukaiConormalFieldCoordinates.formsMap K p)) = 7 :=
    MukaiConormalFieldCoordinates.finrank_range_formsMap K p
  change LinearMap.range (MukaiConormalFieldCoordinates.formsMap K p) =
    LinearMap.ker (firstJetMap K z v)
  exact Submodule.eq_of_le_of_finrank_eq hle (hrange.trans hker.symm)

end M9Native.MukaiConormalChartImage
