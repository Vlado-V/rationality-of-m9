module

public import M9StacksIntegration.ConicFrameSourceAlgebra
public import M9StacksIntegration.ConicFrameBaseChange
public import M9StacksIntegration.ConicFrameSourceMatrix
public import M9StacksIntegration.ConicFrameChartFactor
public import M9StacksIntegration.NativeDominantFunctionField

/-!
# The actual dominant conic-frame rational map and its generic-stalk embedding

The native Grassmannian map is formed from the literal normalized quotient
coordinates. Its equality with the polynomial quotient classifying map is
proved by the chart universal property. Injectivity of its coordinate ring
map is the previously proved explicit Jacobian computation.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace M9Native.ConicFrameNativeGeometry

open M9Native.ConicFrame M9Native.ConicFrameProjective M9Native.ConicFrameCoordinates
open M9Native.ConicFrameCoordinateIndex M9Native.ConicFrameSourceAlgebra
open M9Native.ConicFrameChartFactor M9Native.ConicFrameSourceMatrix

variable (K : Type u) [Field K]

abbrev source : Scheme.{u} := Spec (.of (sourceRing K))
def sourceProjection : source K ⟶ Spec (.of K) :=
  Spec.map (CommRingCat.ofHom (algebraMap K (sourceRing K)))

def sourceInclusion : source K ⟶ ConicFrameProjective.space K :=
  Spec.map (CommRingCat.ofHom (algebraMap (polynomial K) (sourceRing K))) ≫ ConicFrameProjective.chart K

instance sourceInclusion_isOpenImmersion : IsOpenImmersion (sourceInclusion K) := by
  unfold sourceInclusion sourceRing
  infer_instance

theorem sourceInclusion_dense : DenseRange (sourceInclusion K) :=
  (sourceInclusion K).isOpenEmbedding.isOpen_range.dense (Set.range_nonempty _)

@[reassoc (attr := simp)] theorem sourceInclusion_projection :
    sourceInclusion K ≫ ConicFrameProjective.projection K = sourceProjection K := by
  rw [sourceInclusion,Category.assoc,ConicFrameProjective.chart_projection,← Spec.map_comp]
  congr 1

def globalFrame : Mat3 Γ(source K, ⊤) :=
  (sourceFrame K).map (Scheme.ΓSpecIso (.of (sourceRing K))).inv.hom

theorem globalFrame_det_unit : IsUnit (globalFrame K).det := by
  rw [globalFrame,← RingHom.mapMatrix_apply,← RingHom.map_det]
  exact (sourceFrame_det_unit K).map _

theorem globalPivot_det_unit :
    IsUnit ((quotientMatrix (globalFrame K)).submatrix id pivotEmbedding).det := by
  rw [globalFrame,← quotientMatrix_map,Matrix.submatrix_map,← RingHom.mapMatrix_apply,← RingHom.map_det]
  exact (sourcePivot_det_unit K).map _

theorem globalNormalizedMatrix_eq :
    normalizedMatrix (source K) pivotEmbedding (quotientMatrix (globalFrame K)) =
      ((((quotientMatrix (sourceFrame K)).submatrix id pivotEmbedding)⁻¹ *
        quotientMatrix (sourceFrame K)).map (Scheme.ΓSpecIso (.of (sourceRing K))).inv.hom) := by
  rw [normalizedMatrix,globalFrame,← quotientMatrix_map,Matrix.map_mul,
    matrixInverse_map _ _ (sourcePivot_det_unit K),Matrix.submatrix_map]

def affineCoordinateMap : source K ⟶ Spec (.of (targetRing K)) :=
  Spec.map (CommRingCat.ofHom (coordinateMap K).toRingHom)

def affineFactor : source K ⟶ GrassmannianCharts.chartSpace K 4 6 pivotEmbedding :=
  affineCoordinateMap K ≫ (AffineSpace.SpecIso _ (.of K)).inv

theorem affineFactor_eq : affineFactor K =
    ConicFrameChartFactor.affineFactor (source K) pivotEmbedding K (sourceProjection K)
      (normalizedMatrix (source K) pivotEmbedding (quotientMatrix (globalFrame K))) := by
  change affineFactor K = AffineSpace.homOfVector (sourceProjection K)
    (fun a => normalizedMatrix (source K) pivotEmbedding
      (quotientMatrix (globalFrame K)) a.down.2 a.down.1.val)
  apply AffineSpace.hom_ext
  · rw [AffineSpace.homOfVector_over,affineFactor,Category.assoc,AffineSpace.SpecIso_inv_over]
    change Spec.map (CommRingCat.ofHom (coordinateMap K).toRingHom) ≫
      Spec.map (CommRingCat.ofHom (algebraMap K (targetRing K))) =
      Spec.map (CommRingCat.ofHom (algebraMap K (sourceRing K)))
    rw [← Spec.map_comp]
    apply congrArg (fun f : CommRingCat.of K ⟶ CommRingCat.of (sourceRing K) => Spec.map f)
    apply CommRingCat.hom_ext
    exact (coordinateMap K).comp_algebraMap
  · intro a
    change (affineFactor K).appTop (AffineSpace.coord (Spec (.of K)) a) = _
    rw [affineFactor,Scheme.Hom.comp_appTop,CommRingCat.comp_apply,AffineSpace.SpecIso_inv_appTop_coord]
    change (Spec.map (CommRingCat.ofHom (coordinateMap K).toRingHom)).appTop
      ((Scheme.ΓSpecIso (.of (targetRing K))).inv (MvPolynomial.X a)) = _
    rw [← CommRingCat.comp_apply,← Scheme.ΓSpecIso_inv_naturality,CommRingCat.comp_apply]
    simp only [ConcreteCategory.hom_ofHom,AlgHom.toRingHom_eq_coe,AlgHom.coe_toRingHom,
      coordinateMap,MvPolynomial.aeval_X]
    change (Scheme.ΓSpecIso (.of (sourceRing K))).inv (sourceCoordinate K (coordinateEquiv a)) =
      (AffineSpace.homOfVector _ _).appTop (AffineSpace.coord (Spec (.of K)) a)
    rw [AffineSpace.homOfVector_appTop_coord,globalNormalizedMatrix_eq,Matrix.map_apply,
      sourceCoordinate_eq_entry]

/-- The actual rational-map representative, in the genuine native quotient chart. -/
def conicMap : source K ⟶ GrassmannianCharts.space K 4 6 :=
  affineCoordinateMap K ≫ GrassmannianCharts.chartSpecMap K 4 6 pivotEmbedding

theorem conicMap_eq_classifying : conicMap K =
    ConicFrame.map (source K) K (sourceProjection K) (globalFrame K) (globalFrame_det_unit K) := by
  rw [conicMap,GrassmannianCharts.chartSpecMap,← Category.assoc]
  change affineFactor K ≫ _ = _
  rw [affineFactor_eq,← ConicFrameChartFactor.map_eq_chartOver _ _ _ _ _ _ (globalPivot_det_unit K)]

@[reassoc (attr := simp)] theorem conicMap_projection :
    conicMap K ≫ GrassmannianCharts.projection K 4 6 = sourceProjection K := by
  rw [conicMap_eq_classifying,ConicFrame.map_projection]

variable [CharZero K]

instance affineCoordinateMap_isDominant : IsDominant (affineCoordinateMap K) :=
  NativeDominantFunctionField.specMap_isDominant _ (coordinateMap_injective K)

instance conicMap_isDominant : IsDominant (conicMap K) := by
  have : IsDominant (GrassmannianCharts.chartSpecMap K 4 6 pivotEmbedding) :=
    ⟨GrassmannianCharts.chartSpecMap_dense K 4 6 pivotEmbedding⟩
  unfold conicMap
  infer_instance

instance sourceFunctionField_algebra : Algebra K (source K).functionField :=
  (GrassmannianCharts.structureScalarMap K (sourceProjection K)).toAlgebra

def sourceRestrictionEquiv :
    (ConicFrameProjective.space K).functionField ≃ₐ[K] (source K).functionField where
  __ := (GrassmannianCharts.openImmersionFunctionFieldIso (sourceInclusion K)).commRingCatIsoToRingEquiv
  commutes' c := by
    have h := GrassmannianCharts.openImmersionFunctionFieldIso_scalar K (sourceInclusion K)
      (ConicFrameProjective.projection K)
    rw [sourceInclusion_projection] at h
    exact DFunLike.congr_fun h c

/-- The actual dominant conic-frame morphism induces this embedding of
native generic stalk fields. -/
def functionFieldEmbedding :
    (GrassmannianCharts.space K 4 6).functionField →ₐ[K]
      (ConicFrameProjective.space K).functionField :=
  (sourceRestrictionEquiv K).symm.toAlgHom.comp
    { __ := NativeDominantFunctionField.map (conicMap K)
      commutes' c := by
        have h := NativeDominantFunctionField.map_scalar K (conicMap K)
          (GrassmannianCharts.projection K 4 6)
        rw [conicMap_projection] at h
        exact DFunLike.congr_fun h c }

theorem functionFieldEmbedding_injective : Function.Injective (functionFieldEmbedding K) :=
  (functionFieldEmbedding K).injective

end M9Native.ConicFrameNativeGeometry
