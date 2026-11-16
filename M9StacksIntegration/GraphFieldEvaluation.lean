module

public import M9StacksIntegration.ReducedGraphGenericPoint
public import M9StacksIntegration.GrassmannianFieldKernels

/-! Literal evaluation of the actual native graph generic point in a field
extension, including its free quotient matrix and generic-stalk pullback. -/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000
set_option maxRecDepth 10000

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite Matrix

universe u

namespace M9Native.GraphFieldEvaluation

open M9.GraphBundleDescent GraphGrassmannianChart ReducedGraphGenericPoint
open AlgebraicGeometry.Grassmannian LagrangianMatrixChart

variable (K L : Type u) [Field K] [Field L] [Algebra K L]

abbrev FF := ChartFunctionField K
abbrev fieldSpec : Scheme.{u} := Spec (.of L)

def specMap (e : FF K →ₐ[K] L) : fieldSpec L ⟶ GenericSpec K :=
  Spec.map (CommRingCat.ofHom e.toRingHom)

instance specMap_isDominant (e : FF K →ₐ[K] L) : IsDominant (specMap K L e) :=
  NativeDominantFunctionField.specMap_isDominant _ e.injective

def point (e : FF K →ₐ[K] L) : fieldSpec L ⟶ GrassmannianCharts.space K 4 12 :=
  specMap K L e ≫ nativeGraphPoint K

instance point_isDominant (e : FF K →ₐ[K] L) : IsDominant (point K L e) := by
  unfold point
  infer_instance

def fieldAffineEquiv : (fieldSpec L).functionField ≃+* L :=
  (IsFractionRing.algEquiv L L (fieldSpec L).functionField).symm.toRingEquiv

@[simp] theorem fieldAffineEquiv_algebraMap (z : L) :
    fieldAffineEquiv L (algebraMap L (fieldSpec L).functionField z) = z :=
  (IsFractionRing.algEquiv L L (fieldSpec L).functionField).symm.commutes z

theorem specMap_pullback (e : FF K →ₐ[K] L) (z : (GenericSpec K).functionField) :
    fieldAffineEquiv L (NativeDominantFunctionField.map (specMap K L e) z) =
      e (affineFieldEquiv K z) := by
  have hh : (fieldAffineEquiv L).toRingHom.comp
      (NativeDominantFunctionField.map (specMap K L e)) =
        e.toRingHom.comp (affineFieldEquiv K).toRingHom := by
    apply IsFractionRing.ringHom_ext (A := FF K)
    intro b
    change fieldAffineEquiv L (NativeDominantFunctionField.map
      (Spec.map (CommRingCat.ofHom e.toRingHom))
        (algebraMap (FF K) (GenericSpec K).functionField b)) = _
    rw [NativeFunctionFieldFunctor.affine_map_algebraMap, fieldAffineEquiv_algebraMap]
    change e b = e (affineFieldEquiv K
      (algebraMap (FF K) (GenericSpec K).functionField b))
    rw [affineFieldEquiv_algebraMap]
  exact DFunLike.congr_fun hh z

/-- Pullback is evaluation of the original thirty-two graph coordinates. -/
theorem point_pullback (e : FF K →ₐ[K] L)
    (z : (GrassmannianCharts.space K 4 12).functionField) :
    fieldAffineEquiv L (NativeDominantFunctionField.map (point K L e) z) =
      e (graphFunctionFieldEquiv K z) := by
  change fieldAffineEquiv L (NativeDominantFunctionField.map
    (specMap K L e ≫ nativeGraphPoint K) z) = _
  rw [NativeFunctionFieldFunctor.map_comp, RingHom.comp_apply,
    specMap_pullback, nativeGraphPoint_pullback]

def base (e : FF K →ₐ[K] L) (s : Fin 2) : BaseMatrix L :=
  (genericBase K s).map e.toRingHom

def isomorphism (e : FF K →ₐ[K] L) : Matrix.GeneralLinearGroup (Fin 4) L :=
  Matrix.GeneralLinearGroup.map e.toRingHom (genericIsomorphism K)

def quotientMatrix (e : FF K →ₐ[K] L) : Matrix (Fin 8) (Fin 12) L :=
  kernelMatrix (blockRows (base K L e 0) (isomorphism K L e).val
    (base K L e 1 * (isomorphism K L e).val))

theorem quotientMatrix_map (e : FF K →ₐ[K] L) :
    quotientMatrix K L e = (kernelMatrix (blockRows (genericBase K 0)
      (genericIsomorphism K).val (genericBase K 1 * (genericIsomorphism K).val))).map e.toRingHom := by
  rw [kernelMatrix_map, blockRows_map, Matrix.map_mul]
  rfl

theorem quotientMatrix_surjective (e : FF K →ₐ[K] L) :
    Function.Surjective (quotientMatrix K L e).mulVec := by
  intro y
  refine ⟨Fin.append 0 y, ?_⟩
  rw [quotientMatrix, kernelMatrix_mulVec]
  have hh : (Fin.append (0 : Fin 4 → L) y) ∘ head = 0 := by
    ext j
    exact Fin.append_left 0 y j
  have hp : (Fin.append (0 : Fin 4 → L) y) ∘ pivot = y := by
    ext j
    exact Fin.append_right 0 y j
  rw [hh, hp, Matrix.mulVec_zero, sub_zero]

def presentation (e : FF K →ₐ[K] L) : QuotientPresentation (fieldSpec L) 4 12 := by
  let q := pullbackPresentation (specMap K L e) (genericPresentation K)
  let : Epi q.map := q.map_epi
  exact { target := freeOn (fieldSpec L) 8
          map := q.map ≫ (pullbackFreeIso (specMap K L e) 8).hom
          map_epi := inferInstance
          finiteLocallyFree := free_isFiniteLocallyFreeOfRank (fieldSpec L) 8 }

theorem presentation_isomorphic (e : FF K →ₐ[K] L) :
    (pullbackPresentation (specMap K L e) (genericPresentation K)).Isomorphic
      (presentation K L e) :=
  ⟨pullbackFreeIso (specMap K L e) 8, rfl⟩

theorem point_class (e : FF K →ₐ[K] L) :
    GraphGrassmannianLinearAction.pointClass K (point K L e) =
      ⟦presentation K L e⟧ := by
  rw [point, GraphGrassmannianLinearAction.pointClass_comp, nativeGraphPoint_class]
  exact Quotient.sound (.rel _ _ (presentation_isomorphic K L e))

theorem presentation_matrix (e : FF K →ₐ[K] L) :
    Stacks.FreeSheafMatrix.toMatrix (presentation K L e).map =
      (quotientMatrix K L e).map (Scheme.ΓSpecIso (.of L)).inv.hom := by
  change Stacks.FreeSheafMatrix.toMatrix
    (ConicFrameLeftEquivariance.pulledFreeMap (specMap K L e) 12 8
      (genericPresentation K).map) = _
  rw [ConicFrameLeftEquivariance.pulledFreeMap_matrix,
    genericPresentation_matrix_actual, quotientMatrix_map]
  ext i j
  change (specMap K L e).appTop
      ((Scheme.ΓSpecIso (.of (FF K))).inv _) =
    (Scheme.ΓSpecIso (.of L)).inv (e _)
  change ((Scheme.ΓSpecIso (.of (FF K))).inv ≫
    (Spec.map (CommRingCat.ofHom e.toRingHom)).appTop) _ = _
  rw [← Scheme.ΓSpecIso_inv_naturality]
  rfl

theorem presentation_isomorphic_fieldPresentation (e : FF K →ₐ[K] L) :
    (presentation K L e).Isomorphic
      (SplitMatrixGrassmannian.fieldPresentation 4 12 L (quotientMatrix K L e)
        (quotientMatrix_surjective K L e)) := by
  refine ⟨Iso.refl _, ?_⟩
  change (presentation K L e).map ≫ 𝟙 _ = _
  rw [Category.comp_id]
  apply Stacks.FreeSheafMatrix.toMatrix_injective
  rw [presentation_matrix, SplitMatrixGrassmannian.fieldPresentation_matrix]

theorem point_class_fieldPresentation (e : FF K →ₐ[K] L) :
    GraphGrassmannianLinearAction.pointClass K (point K L e) =
      ⟦SplitMatrixGrassmannian.fieldPresentation 4 12 L (quotientMatrix K L e)
        (quotientMatrix_surjective K L e)⟧ := by
  rw [point_class]
  exact Quotient.sound (.rel _ _ (presentation_isomorphic_fieldPresentation K L e))

theorem point_projection (e : FF K →ₐ[K] L) :
    point K L e ≫ GrassmannianCharts.projection K 4 12 =
      Spec.map (CommRingCat.ofHom (algebraMap K L)) := by
  rw [point, nativeGraphPoint, Category.assoc, Category.assoc, graphMap_projection]
  change Spec.map (CommRingCat.ofHom e.toRingHom) ≫
    Spec.map (CommRingCat.ofHom (chartLocalizationToField K).toRingHom) ≫
      Spec.map (CommRingCat.ofHom (algebraMap K (IsomChartRing K))) = _
  rw [← Spec.map_comp, ← Spec.map_comp]
  congr 1
  ext c
  exact (e.comp (chartLocalizationToField K)).commutes c

end M9Native.GraphFieldEvaluation
