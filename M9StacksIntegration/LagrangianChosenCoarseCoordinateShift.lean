module

public import M9StacksIntegration.LagrangianChosenCoarseFamily
public import M9StacksIntegration.LagrangianFamilyOrbitIsomorphism
public import M9StacksIntegration.AllOriginalCoarseClassifierFibre
public import Mathlib.AlgebraicGeometry.Restrict

@[expose] public section

/-! The actual chosen coarse classifier in the frozen native primitive
coordinates. Its domain is the inverse image of the original raw good open
under the proved coordinate isomorphism. All source bounds, maps and
precomposition triangles are derived from the actual original family. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
attribute [local instance] Space.pointTopology
attribute [local implicit_reducible] CategoryTheory.BasedCategory.ofFunctor

namespace M9Native.LagrangianChosenCoarseCoordinateShift

open M9StacksIntegration.AllTestBoundedCharts
  M9StacksIntegration.AllTestNativeOriginalFunctor
  M9StacksIntegration.AllTestNativeOriginalPullbacks

abbrev goodOpen : PrimitiveGrassmannianAction.space.Opens :=
  LagrangianFamilyOrbitIsomorphism.coordinateGoodOpen

/-- The source change is the actual restriction of the original C-isomorphism. -/
def coordinateIso : goodOpen.toScheme ≅
    (LagrangianLinearSectionGenericSmooth.goodOpen ℂ).toScheme :=
  LagrangianParameterCoordinates.coordinateChange.hom.preimageIso
    (LagrangianLinearSectionGenericSmooth.goodOpen ℂ)

theorem coordinateIso_hom_eq :
    coordinateIso.hom = LagrangianFamilyOrbitIsomorphism.coordinateGoodMap := by
  apply (cancel_mono (LagrangianLinearSectionGenericSmooth.goodOpen ℂ).ι).mp
  exact (Scheme.Hom.preimageIso_hom_ι
    LagrangianParameterCoordinates.coordinateChange.hom
    (LagrangianLinearSectionGenericSmooth.goodOpen ℂ)).trans
      LagrangianFamilyOrbitIsomorphism.coordinateGoodMap_inclusion.symm

/-- The original complex structure map is retained on the shifted open. -/
def baseProjection : goodOpen.toScheme ⟶ Spec (.of ℂ) :=
  goodOpen.ι ≫ PrimitiveGrassmannianAction.projection

@[reassoc] theorem coordinateGoodMap_over_base :
    LagrangianFamilyOrbitIsomorphism.coordinateGoodMap ≫
        LagrangianNativeGenusNineFamily.baseProjection ℂ = baseProjection := by
  change LagrangianFamilyOrbitIsomorphism.coordinateGoodMap ≫
    ((LagrangianLinearSectionGenericSmooth.goodOpen ℂ).ι ≫
      LagrangianLinearSections.parameterProjection ℂ) = _
  rw [← Category.assoc, LagrangianFamilyOrbitIsomorphism.coordinateGoodMap_inclusion,
    Category.assoc, LagrangianParameterCoordinates.coordinateChange_projection]
  rfl

variable (B : BigFppfSite) (hC : B.Contains (Spec (.of ℂ)))

include hC in
/-- Actual projectivity of Gr(9,14) and openness derive the shifted source bound. -/
theorem contains_goodOpen : B.Contains goodOpen.toScheme := by
  letI : IsProper PrimitiveGrassmannianAction.projection :=
    isProper_of_isProjectiveMorphism _
      (Grassmannian.isProjectiveMorphism_schemeOver 9 14 (Spec (.of ℂ)))
  have hP : B.Contains PrimitiveGrassmannianAction.space :=
    Scheme.size_lt_of_locallyOfFiniteType_of_quasiCompact
      PrimitiveGrassmannianAction.projection hC
  exact Scheme.size_lt_of_isOpenImmersion goodOpen.ι hP

/-- The actual shifted source object over the original complex field. -/
def base : BigFppfOver B (Spec (.of ℂ)) hC :=
  siteObject B (Spec (.of ℂ)) hC (contains_goodOpen B hC) baseProjection

/-- Its literal actual map to Root's raw parameter source. -/
def toRaw : base B hC ⟶ LagrangianNativeGenusNineFamily.base ℂ B hC :=
  Over.homMk (ObjectProperty.homMk LagrangianFamilyOrbitIsomorphism.coordinateGoodMap)
    (ObjectProperty.hom_ext _ coordinateGoodMap_over_base)

theorem toRaw_toScheme :
    (BigFppfOver.toScheme B (Spec (.of ℂ)) hC).map (toRaw B hC) =
      LagrangianFamilyOrbitIsomorphism.coordinateGoodMap := rfl

/-- The coordinate restriction is also an actual isomorphism inside the same site. -/
def baseIso : base B hC ≅ LagrangianNativeGenusNineFamily.base ℂ B hC :=
  Over.isoMk (ObjectProperty.isoMk _ coordinateIso) (by
    apply ObjectProperty.hom_ext
    change coordinateIso.hom ≫ LagrangianNativeGenusNineFamily.baseProjection ℂ =
      baseProjection
    rw [coordinateIso_hom_eq]
    exact coordinateGoodMap_over_base)

theorem baseIso_hom : (baseIso B hC).hom = toRaw B hC := by
  apply Over.OverMorphism.ext
  apply ObjectProperty.hom_ext
  exact coordinateIso_hom_eq

instance toRaw_isIso : IsIso (toRaw B hC) := by
  rw [← baseIso_hom B hC]
  infer_instance

variable (hZ : B.Contains integerBase)

abbrev target : AlgebraicSpaces B (Spec (.of ℂ)) hC :=
  LagrangianChosenCoarseFamily.target ℂ B hC hZ

/-- The actual chosen field classifier, precomposed by the actual site map. -/
def classifier :
    BasedCategory.ofFunctor (Over.forget (base B hC)) ⥤ᵇ
      (M9StacksIntegration.GenusNineCoarseOverField.smoothStack
        B hZ ℂ hC 9 (by decide)).val.val :=
  BasedFunctor.comp (PresheafValuedClassifierReflection.sliceMap (toRaw B hC))
    (LagrangianChosenCoarseFamily.fieldClassifier ℂ B hC hZ)

/-- The induced map to the SAME actual chosen coarse target. -/
def nativeMap : schemeSpace (base B hC) ⟶ target B hC hZ :=
  ASClassifierGeometricLift.nativeMap B (Spec (.of ℂ)) hC
    (M9StacksIntegration.GenusNineCoarseOverField.coarseMap B hZ ℂ hC 9 (by decide))
    (classifier B hC hZ)

/-- The coordinate-shifted classifier is actual native precomposition. -/
theorem nativeMap_eq_precompose :
    nativeMap B hC hZ = schemeSpaceMap (toRaw B hC) ≫
      LagrangianChosenCoarseFamily.nativeMap ℂ B hC hZ :=
  AllOriginalCoarseClassifierFibre.nativeMap_precompose ℂ B hC
    (M9StacksIntegration.GenusNineCoarseOverField.coarseMap B hZ ℂ hC 9 (by decide))
    (LagrangianChosenCoarseFamily.fieldClassifier ℂ B hC hZ) (toRaw B hC)

/-- The SAME actual source map on every original complex test scheme. -/
def originalToRaw :
    (boundedInclusion B ℂ hC).obj (base B hC) ⟶
      (boundedInclusion B ℂ hC).obj (LagrangianNativeGenusNineFamily.base ℂ B hC) :=
  (boundedInclusion B ℂ hC).map (toRaw B hC)

theorem originalToRaw_left :
    (originalToRaw B hC).left = LagrangianFamilyOrbitIsomorphism.coordinateGoodMap := rfl

/-- The actual chosen native map extended to all original tests. -/
def originalMap :
    yoneda.obj ((boundedInclusion B ℂ hC).obj (base B hC)) ⟶
      (originalPresheafFunctor ℂ B hC).obj (target B hC hZ) :=
  originalChart ℂ B hC (target B hC hZ) (base B hC) (nativeMap B hC hZ).hom

/-- Literal all-original Yoneda precomposition; no compatibility premise. -/
theorem originalMap_eq_precompose :
    originalMap B hC hZ = yoneda.map (originalToRaw B hC) ≫
      LagrangianChosenCoarseFamily.originalMap ℂ B hC hZ := by
  change AlgebraicSpaceValuedClassifierReflection.originalMap ℂ B hC
      (ASClassifierGeometricLift.coarseFunctor B (Spec (.of ℂ)) hC
        (M9StacksIntegration.GenusNineCoarseOverField.coarseMap B hZ ℂ hC 9 (by decide)))
      (BasedFunctor.comp (PresheafValuedClassifierReflection.sliceMap (toRaw B hC))
        (ASClassifierGeometricLift.classifier B (Spec (.of ℂ)) hC
          (LagrangianChosenCoarseFamily.fieldClassifier ℂ B hC hZ))) = _
  exact AlgebraicSpaceValuedClassifierReflection.originalMap_precompose ℂ B hC
    (ASClassifierGeometricLift.coarseFunctor B (Spec (.of ℂ)) hC
      (M9StacksIntegration.GenusNineCoarseOverField.coarseMap B hZ ℂ hC 9 (by decide)))
    (ASClassifierGeometricLift.classifier B (Spec (.of ℂ)) hC
      (LagrangianChosenCoarseFamily.fieldClassifier ℂ B hC hZ)) (toRaw B hC)

theorem originalMap_app_precompose (T : M9StandaloneDraft.Schemes ℂ)
    (x : T ⟶ (boundedInclusion B ℂ hC).obj (base B hC)) :
    (originalMap B hC hZ).app (op T) x =
      (LagrangianChosenCoarseFamily.originalMap ℂ B hC hZ).app (op T)
        (x ≫ originalToRaw B hC) := by
  rw [originalMap_eq_precompose]
  rfl

/-- Actual coordinate precomposition preserves the entire native point image. -/
theorem nativeMap_points_range :
    Set.range (Space.pointsMap B (Spec (.of ℂ)) hC _ (nativeMap B hC hZ).hom) =
      Set.range (Space.pointsMap B (Spec (.of ℂ)) hC _
        (LagrangianChosenCoarseFamily.nativeMap ℂ B hC hZ).hom) := by
  rw [nativeMap_eq_precompose]
  change Set.range (Space.pointsMap B (Spec (.of ℂ)) hC _
    (yoneda.map (toRaw B hC) ≫
      (LagrangianChosenCoarseFamily.nativeMap ℂ B hC hZ).hom)) = _
  rw [Space.pointsMap_comp]
  exact (Space.pointsMap_surjective_of_isIso B (Spec (.of ℂ)) hC
    (yoneda.map (toRaw B hC))).range_comp _

/-- Density is transported through the actual coordinate source isomorphism. -/
theorem nativeMap_dense_iff :
    DenseRange (Space.pointsMap B (Spec (.of ℂ)) hC _ (nativeMap B hC hZ).hom) ↔
      DenseRange (Space.pointsMap B (Spec (.of ℂ)) hC _
        (LagrangianChosenCoarseFamily.nativeMap ℂ B hC hZ).hom) := by
  change Dense _ ↔ Dense _
  rw [nativeMap_points_range B hC hZ]

end M9Native.LagrangianChosenCoarseCoordinateShift
