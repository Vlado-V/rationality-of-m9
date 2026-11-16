module

public import M9StacksIntegration.ConicFrameChartActionComparison

/-! The two actual generic-stalk chart restrictions preserve the same named
matrix ratios. This binds the conic coordinate homomorphism to the frozen
native right-frame action. -/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory Opposite

namespace M9Native.ConicFrameNativeActionCoordinates

open ConicFrameProjective ConicFrameSourceAlgebra ConicFrameCoordinates
open ConicFrameNativeGeometry ConicFrameFieldComparison ConicFrameGammaAction
open ConicFrameChartActionComparison

instance sourceInclusion_isDominant : IsDominant (sourceInclusion ℂ) :=
  ⟨sourceInclusion_dense ℂ⟩

instance legacyChart_isDominant : IsDominant (M9.ProjectiveFunctionField.chartMap 8 0) :=
  ⟨(M9.ProjectiveFunctionField.chartMap 8 0).isOpenEmbedding.isOpen_range.dense
    (Set.range_nonempty _)⟩

theorem map_congr {X Y : Scheme} [IrreducibleSpace X] [IrreducibleSpace Y]
    {f g : X ⟶ Y} [IsDominant f] [IsDominant g] (h : f = g) :
    NativeDominantFunctionField.map f = NativeDominantFunctionField.map g := by
  subst g
  rfl

theorem sourceInclusion_to_legacy :
    sourceInclusion ℂ ≫ nativeSchemeIso.hom =
      Spec.map (CommRingCat.ofHom (algebraMap (polynomial ℂ) (sourceRing ℂ))) ≫
        Spec.map (CommRingCat.ofHom (M9.ProjectiveFunctionField.chartCoordinatesEquiv 8 0).toRingHom) ≫
          M9.ProjectiveFunctionField.chartMap 8 0 := by
  rw [sourceInclusion,Category.assoc,nativeChart_eq_legacy]

theorem nativeFieldEquiv_eq_map : nativeFieldEquiv.toRingHom =
    NativeDominantFunctionField.map nativeSchemeIso.hom := by
  exact openIso_eq_map nativeSchemeIso.hom

theorem sourceRestriction_eq_map : (sourceRestrictionEquiv ℂ).toRingHom =
    NativeDominantFunctionField.map (sourceInclusion ℂ) := by
  have : IsDominant (sourceInclusion ℂ) := ⟨sourceInclusion_dense ℂ⟩
  exact openIso_eq_map (sourceInclusion ℂ)

theorem legacyChart_eq_map : (M9.ProjectiveFunctionField.chartFunctionFieldEquiv 8 0).toRingHom =
    NativeDominantFunctionField.map (M9.ProjectiveFunctionField.chartMap 8 0) := by
  have : IsDominant (M9.ProjectiveFunctionField.chartMap 8 0) :=
    ⟨(M9.ProjectiveFunctionField.chartMap 8 0).isOpenEmbedding.isOpen_range.dense
      (Set.range_nonempty _)⟩
  exact openIso_eq_map (M9.ProjectiveFunctionField.chartMap 8 0)

theorem namedFieldEquiv (z : M9.ProjectiveFunctionField.matrixFunctionField) :
    projectiveNativeEquiv ℂ (nativeFieldEquiv z) =
      M9.ProjectiveFunctionField.functionFieldEquiv 8 0 z := by
  have hdomSource : IsDominant (sourceInclusion ℂ) := ⟨sourceInclusion_dense ℂ⟩
  have hdomChart : IsDominant (M9.ProjectiveFunctionField.chartMap 8 0) :=
    ⟨(M9.ProjectiveFunctionField.chartMap 8 0).isOpenEmbedding.isOpen_range.dense
      (Set.range_nonempty _)⟩
  have hdomLocal : IsDominant
      (Spec.map (CommRingCat.ofHom (algebraMap (polynomial ℂ) (sourceRing ℂ)))) :=
    ⟨(Spec.map (CommRingCat.ofHom (algebraMap (polynomial ℂ) (sourceRing ℂ)))).isOpenEmbedding.isOpen_range.dense
      (Set.range_nonempty _)⟩
  have hrename : IsIso (CommRingCat.ofHom
      (M9.ProjectiveFunctionField.chartCoordinatesEquiv 8 0).toRingHom) :=
    (M9.ProjectiveFunctionField.chartCoordinatesEquiv 8 0).toRingEquiv.toCommRingCatIso.isIso_hom
  have h : (projectiveNativeEquiv ℂ).toRingHom.comp
      (nativeFieldEquiv.toRingHom.comp
        (M9.ProjectiveFunctionField.chartFunctionFieldEquiv 8 0).symm.toRingHom) =
      (M9.ProjectiveFunctionField.chartFractionCoordinatesEquiv 8 0).toRingHom.comp
        (M9.ProjectiveFunctionField.chartFractionEquiv 8 0).toRingHom := by
    apply IsFractionRing.ringHom_ext
      (A := M9.ProjectiveFunctionField.chartPolynomial 8 0)
    intro p
    change sourceNativeEquiv ℂ (sourceRestrictionEquiv ℂ
        (nativeFieldEquiv ((M9.ProjectiveFunctionField.chartFunctionFieldEquiv 8 0).symm
          (algebraMap (M9.ProjectiveFunctionField.chartPolynomial 8 0)
            (M9.ProjectiveFunctionField.chartScheme 8 0).functionField p)))) = _
    change sourceNativeEquiv ℂ
      (((sourceRestrictionEquiv ℂ).toRingHom.comp nativeFieldEquiv.toRingHom)
        ((M9.ProjectiveFunctionField.chartFunctionFieldEquiv 8 0).symm
          (algebraMap (M9.ProjectiveFunctionField.chartPolynomial 8 0)
            (M9.ProjectiveFunctionField.chartScheme 8 0).functionField p))) = _
    rw [sourceRestriction_eq_map,nativeFieldEquiv_eq_map,← NativeFunctionFieldFunctor.map_comp,
      map_congr sourceInclusion_to_legacy,NativeFunctionFieldFunctor.map_comp,
      NativeFunctionFieldFunctor.map_comp,← legacyChart_eq_map]
    change sourceNativeEquiv ℂ
      (NativeDominantFunctionField.map
        (Spec.map (CommRingCat.ofHom (algebraMap (polynomial ℂ) (sourceRing ℂ))))
          (NativeDominantFunctionField.map
            (Spec.map (CommRingCat.ofHom
              (M9.ProjectiveFunctionField.chartCoordinatesEquiv 8 0).toRingHom))
              ((M9.ProjectiveFunctionField.chartFunctionFieldEquiv 8 0)
                ((M9.ProjectiveFunctionField.chartFunctionFieldEquiv 8 0).symm
                  (algebraMap (M9.ProjectiveFunctionField.chartPolynomial 8 0)
                    (M9.ProjectiveFunctionField.chartScheme 8 0).functionField p))))) = _
    rw [AlgEquiv.apply_symm_apply]
    rw [NativeFunctionFieldFunctor.affine_map_algebraMap,
      NativeFunctionFieldFunctor.affine_map_algebraMap,sourceNativeEquiv_algebraMap]
    rw [ConicFrameSourceAlgebra.toRational_algebraMap]
    change algebraMap (polynomial ℂ) (rationalField ℂ)
        (M9.ProjectiveFunctionField.chartCoordinatesEquiv 8 0 p) = _
    change _ = M9.ProjectiveFunctionField.chartFractionCoordinatesEquiv 8 0
      ((FractionRing.algEquiv (M9.ProjectiveFunctionField.chartPolynomial 8 0)
        (M9.ProjectiveFunctionField.chartScheme 8 0).functionField).symm
          (algebraMap (M9.ProjectiveFunctionField.chartPolynomial 8 0)
            (M9.ProjectiveFunctionField.chartScheme 8 0).functionField p))
    rw [AlgEquiv.commutes]
    exact (IsFractionRing.algEquivOfAlgEquiv_algebraMap
      (M9.ProjectiveFunctionField.chartCoordinatesEquiv 8 0) p).symm
  have hz := DFunLike.congr_fun h
    (M9.ProjectiveFunctionField.chartFunctionFieldEquiv 8 0 z)
  change projectiveNativeEquiv ℂ (nativeFieldEquiv
      ((M9.ProjectiveFunctionField.chartFunctionFieldEquiv 8 0).symm
        (M9.ProjectiveFunctionField.chartFunctionFieldEquiv 8 0 z))) =
    M9.ProjectiveFunctionField.functionFieldEquiv 8 0 z at hz
  rw [AlgEquiv.symm_apply_apply] at hz
  exact hz

end M9Native.ConicFrameNativeActionCoordinates
