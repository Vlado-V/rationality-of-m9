module

public import M9StacksIntegration.ConicFramePairDegree
public import M9StacksIntegration.GrassmannianProductCharts
public import M9StacksIntegration.ConicFrameFieldComparison

/-! The genuine product conic morphism and its exact native generic-stalk
pullback, in the original independent tensor-chart coordinates. -/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 500000

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open scoped TensorProduct

namespace M9Native.ConicFramePairFieldComparison

open ConicFrameSourceAlgebra ConicFramePairRings ConicFrameCoordinateIndex

abbrev source : Scheme := Spec (.of (sourcePair ℂ))
abbrev target : Scheme := GrassmannianProductCharts.productSpace ℂ 4 6

def sourceProjection : source ⟶ Spec (.of ℂ) :=
  Spec.map (CommRingCat.ofHom (algebraMap ℂ (sourcePair ℂ)))

instance sourceField_algebra : Algebra ℂ source.functionField :=
  (GrassmannianCharts.structureScalarMap ℂ sourceProjection).toAlgebra

def targetChart : Spec (.of (targetPair ℂ)) ⟶ target :=
  GrassmannianProductCharts.chartSpecMap ℂ 4 6 pivotEmbedding pivotEmbedding

instance targetChart_isOpenImmersion : IsOpenImmersion targetChart := by
  unfold targetChart
  infer_instance

instance targetChart_isDominant : IsDominant targetChart :=
  ⟨GrassmannianProductCharts.chartSpecMap_dense ℂ 4 6 pivotEmbedding pivotEmbedding⟩

def targetNativeEquiv : target.functionField ≃ₐ[ℂ] targetPairField ℂ :=
  GrassmannianProductCharts.chartFunctionFieldEquiv ℂ 4 6 pivotEmbedding pivotEmbedding

def sourceNativeEquiv : source.functionField ≃ₐ[ℂ] sourcePairField ℂ := by
  let e := (FractionRing.algEquiv (sourcePair ℂ) source.functionField).symm
  refine { __ := e.toRingEquiv, commutes' := fun c => ?_ }
  change e (algebraMap ℂ source.functionField c) = _
  have hc : algebraMap ℂ source.functionField c =
      algebraMap (sourcePair ℂ) source.functionField (algebraMap ℂ (sourcePair ℂ) c) :=
    DFunLike.congr_fun (GrassmannianCharts.affine_structureScalarMap ℂ (sourcePair ℂ)) c
  rw [hc, e.commutes]
  exact (IsScalarTower.algebraMap_apply ℂ (sourcePair ℂ) (sourcePairField ℂ) c).symm

@[simp] theorem sourceNativeEquiv_algebraMap (b : sourcePair ℂ) :
    sourceNativeEquiv (algebraMap (sourcePair ℂ) source.functionField b) =
      algebraMap (sourcePair ℂ) (sourcePairField ℂ) b := by
  change (FractionRing.algEquiv (sourcePair ℂ) source.functionField).symm _ = _
  exact (FractionRing.algEquiv (sourcePair ℂ) source.functionField).symm.commutes b

def affineCoordinateMap : source ⟶ Spec (.of (targetPair ℂ)) :=
  Spec.map (CommRingCat.ofHom (coordinatePairMap ℂ).toRingHom)

instance affineCoordinateMap_isDominant : IsDominant affineCoordinateMap :=
  NativeDominantFunctionField.specMap_isDominant _ (coordinatePairMap_injective ℂ)

/-- This is the actual product of the two original conic-cover morphisms
on their independent chart source. -/
def conicPairMap : source ⟶ target := affineCoordinateMap ≫ targetChart

instance conicPairMap_isDominant : IsDominant conicPairMap := by
  unfold conicPairMap
  infer_instance

def leftSourceProjection : source ⟶ ConicFrameNativeGeometry.source ℂ :=
  Spec.map (CommRingCat.ofHom
    (Algebra.TensorProduct.includeLeft : sourceRing ℂ →ₐ[ℂ] sourcePair ℂ).toRingHom)

def rightSourceProjection : source ⟶ ConicFrameNativeGeometry.source ℂ :=
  Spec.map (CommRingCat.ofHom
    (Algebra.TensorProduct.includeRight : sourceRing ℂ →ₐ[ℂ] sourcePair ℂ).toRingHom)

theorem affineCoordinateMap_left :
    affineCoordinateMap ≫ Spec.map (CommRingCat.ofHom
      (Algebra.TensorProduct.includeLeft : targetRing ℂ →ₐ[ℂ] targetPair ℂ).toRingHom) =
      leftSourceProjection ≫ ConicFrameNativeGeometry.affineCoordinateMap ℂ := by
  rw [affineCoordinateMap, leftSourceProjection,
    ConicFrameNativeGeometry.affineCoordinateMap, ← Spec.map_comp, ← Spec.map_comp]
  apply congrArg Spec.map
  apply CommRingCat.hom_ext
  exact congrArg AlgHom.toRingHom
    (Algebra.TensorProduct.map_comp_includeLeft (coordinateMap ℂ) (coordinateMap ℂ))

theorem affineCoordinateMap_right :
    affineCoordinateMap ≫ Spec.map (CommRingCat.ofHom
      (Algebra.TensorProduct.includeRight : targetRing ℂ →ₐ[ℂ] targetPair ℂ).toRingHom) =
      rightSourceProjection ≫ ConicFrameNativeGeometry.affineCoordinateMap ℂ := by
  rw [affineCoordinateMap, rightSourceProjection,
    ConicFrameNativeGeometry.affineCoordinateMap, ← Spec.map_comp, ← Spec.map_comp]
  apply congrArg Spec.map
  apply CommRingCat.hom_ext
  exact congrArg AlgHom.toRingHom
    (Algebra.TensorProduct.map_comp_includeRight (coordinateMap ℂ) (coordinateMap ℂ))

@[reassoc] theorem conicPairMap_fst :
    conicPairMap ≫ pullback.fst _ _ =
      leftSourceProjection ≫ ConicFrameNativeGeometry.conicMap ℂ := by
  rw [conicPairMap, Category.assoc]
  change affineCoordinateMap ≫
    (GrassmannianProductCharts.chartSpecMap ℂ 4 6 pivotEmbedding pivotEmbedding ≫ _) = _
  rw [GrassmannianProductCharts.chartSpecMap_fst, ← Category.assoc, affineCoordinateMap_left,
    Category.assoc]
  rfl

@[reassoc] theorem conicPairMap_snd :
    conicPairMap ≫ pullback.snd _ _ =
      rightSourceProjection ≫ ConicFrameNativeGeometry.conicMap ℂ := by
  rw [conicPairMap, Category.assoc]
  change affineCoordinateMap ≫
    (GrassmannianProductCharts.chartSpecMap ℂ 4 6 pivotEmbedding pivotEmbedding ≫ _) = _
  rw [GrassmannianProductCharts.chartSpecMap_snd, ← Category.assoc, affineCoordinateMap_right,
    Category.assoc]
  rfl

def functionFieldEmbedding : target.functionField →ₐ[ℂ] sourcePairField ℂ :=
  (pairFieldEmbedding ℂ).comp targetNativeEquiv.toAlgHom

theorem affine_pullback_eq (z : (Spec (.of (targetPair ℂ))).functionField) :
    sourceNativeEquiv (NativeDominantFunctionField.map affineCoordinateMap z) =
      pairFieldEmbedding ℂ
        ((FractionRing.algEquiv (targetPair ℂ)
          (Spec (.of (targetPair ℂ))).functionField).symm z) := by
  have : IsDominant (Spec.map (CommRingCat.ofHom (coordinatePairMap ℂ).toRingHom)) :=
    affineCoordinateMap_isDominant
  have h : sourceNativeEquiv.toRingHom.comp
        (NativeDominantFunctionField.map affineCoordinateMap) =
      (pairFieldEmbedding ℂ).toRingHom.comp
        (FractionRing.algEquiv (targetPair ℂ)
          (Spec (.of (targetPair ℂ))).functionField).symm.toRingHom := by
    apply IsFractionRing.ringHom_ext (A := targetPair ℂ)
    intro a
    change sourceNativeEquiv
      (NativeDominantFunctionField.map
        (Spec.map (CommRingCat.ofHom (coordinatePairMap ℂ).toRingHom))
          (algebraMap (targetPair ℂ) (Spec (.of (targetPair ℂ))).functionField a)) =
      pairFieldEmbedding ℂ ((FractionRing.algEquiv (targetPair ℂ)
        (Spec (.of (targetPair ℂ))).functionField).symm
          (algebraMap (targetPair ℂ) (Spec (.of (targetPair ℂ))).functionField a))
    rw [NativeFunctionFieldFunctor.affine_map_algebraMap, sourceNativeEquiv_algebraMap,
      AlgEquiv.commutes, pairFieldEmbedding_algebraMap]
    rfl
  exact DFunLike.congr_fun h z

/-- The coordinate-field embedding is literally the pullback on the actual
generic stalks of the product conic morphism. -/
theorem embedding_comparison (z : target.functionField) :
    sourceNativeEquiv (NativeDominantFunctionField.map conicPairMap z) =
      functionFieldEmbedding z := by
  change sourceNativeEquiv (NativeDominantFunctionField.map
    (affineCoordinateMap ≫ targetChart) z) = _
  rw [NativeFunctionFieldFunctor.map_comp, RingHom.comp_apply, affine_pullback_eq]
  have h := ConicFrameFieldComparison.openIso_eq_map targetChart
  rw [← h]
  rfl

end M9Native.ConicFramePairFieldComparison
