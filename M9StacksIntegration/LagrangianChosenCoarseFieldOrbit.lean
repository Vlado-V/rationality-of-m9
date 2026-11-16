module

public import M9StacksIntegration.LagrangianGoodFieldOrbit
public import M9StacksIntegration.LagrangianChosenCoarseCurveIso

@[expose] public section

/-! Actual chosen-coarse equalities give native Sp6(L) orbits over every
original algebraically closed extension field. The physical whole-fibre
isomorphism and coefficient identities are derived. Source no5 remains
the honest separate input. The coordinate-good native domain is retained. -/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 2200000
set_option maxRecDepth 4096
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

namespace M9Native.LagrangianChosenCoarseFieldOrbit
open M9StacksIntegration.AllTestBoundedCharts
open LagrangianLinearSections LagrangianLinearSectionGenericSmooth
open LagrangianGoodFieldOrbit LagrangianGoodFieldParameterAction

variable (B : BigFppfSite) (hC : B.Contains (Spec (.of ℂ))) (hZ : B.Contains integerBase)
  (L : Type) [Field L] [Algebra ℂ L] [IsAlgClosed L]

/-- The actual original Over morphism already contains the coefficient
triangle; it is not a new compatibility hypothesis. -/
theorem fieldPoint_projection
    (x : M9StandaloneDraft.FieldPoint ℂ L ⟶
      (boundedInclusion B ℂ hC).obj (LagrangianNativeGenusNineFamily.base ℂ B hC)) :
    (x.left ≫ (goodOpen ℂ).ι) ≫ parameterProjection ℂ =
      Spec.map (CommRingCat.ofHom (algebraMap ℂ L)) := by
  have h := Over.w x
  change x.left ≫ (goodOpen ℂ).ι ≫ parameterProjection ℂ =
    Spec.map (CommRingCat.ofHom (algebraMap ℂ L)) at h
  simpa only [Category.assoc] using h

/-- No physical isomorphism, model, genus, transversality or target no5
premise is supplied: the actual chosen coarse equality supplies the
whole original physical isomorphism over the same original Spec L. -/
theorem exists_native_and_raw_orbit_of_coarseEq
    (x y : M9StandaloneDraft.FieldPoint ℂ L ⟶
      (boundedInclusion B ℂ hC).obj (LagrangianNativeGenusNineFamily.base ℂ B hC))
    (hxy : LagrangianChosenCoarseFamily.pointValue ℂ B hC hZ L x =
      LagrangianChosenCoarseFamily.pointValue ℂ B hC hZ L y)
    (hnp : SourceNoFivePencil L x.left) :
    ∃ g : M9.PrimitiveStabilizer.Sp6 L,
      PrimitiveFieldMatrixAction.actPoint L g (originalCoordinates L (x.left ≫ (goodOpen ℂ).ι))
        (originalCoordinates_projection L _ (fieldPoint_projection B hC L x)) =
      originalCoordinates L (y.left ≫ (goodOpen ℂ).ι) ∧
      rawActPoint L g (x.left ≫ (goodOpen ℂ).ι) (fieldPoint_projection B hC L x) =
        y.left ≫ (goodOpen ℂ).ι :=
  exists_native_and_raw_orbit_of_curveIso L x.left y.left
    (fieldPoint_projection B hC L x) (fieldPoint_projection B hC L y)
    (LagrangianChosenCoarseCurveIso.physicalIso ℂ B hC hZ L x y hxy)
    (LagrangianChosenCoarseCurveIso.physicalIso_hom_snd ℂ B hC hZ L x y hxy) hnp

/-- The actual original field point obtained from the coordinate-good
native domain by its established raw classifier map. No field cutoff. -/
def coordinateFieldPoint
    (z : Spec (.of L) ⟶ LagrangianFamilyOrbitIsomorphism.coordinateGoodOpen.toScheme)
    (hz : (z ≫ LagrangianFamilyOrbitIsomorphism.coordinateGoodOpen.ι) ≫ parameterProjection ℂ =
      Spec.map (CommRingCat.ofHom (algebraMap ℂ L))) :
    M9StandaloneDraft.FieldPoint ℂ L ⟶
      (boundedInclusion B ℂ hC).obj (LagrangianNativeGenusNineFamily.base ℂ B hC) :=
  Over.homMk (z ≫ LagrangianFamilyOrbitIsomorphism.coordinateGoodMap) (by
    change (z ≫ LagrangianFamilyOrbitIsomorphism.coordinateGoodMap) ≫
      (goodOpen ℂ).ι ≫ parameterProjection ℂ = Spec.map (CommRingCat.ofHom (algebraMap ℂ L))
    simpa only [Category.assoc] using coordinateGoodPoint_projection L z hz)

/-- The exact native quotient fibre statement on the genuine native
coordinate-good domain, under the actual chosen coarse classifier. -/
theorem exists_coordinate_native_orbit_of_coarseEq
    (z w : Spec (.of L) ⟶ LagrangianFamilyOrbitIsomorphism.coordinateGoodOpen.toScheme)
    (hz : (z ≫ LagrangianFamilyOrbitIsomorphism.coordinateGoodOpen.ι) ≫ parameterProjection ℂ =
      Spec.map (CommRingCat.ofHom (algebraMap ℂ L)))
    (hw : (w ≫ LagrangianFamilyOrbitIsomorphism.coordinateGoodOpen.ι) ≫ parameterProjection ℂ =
      Spec.map (CommRingCat.ofHom (algebraMap ℂ L)))
    (hzw : LagrangianChosenCoarseFamily.pointValue ℂ B hC hZ L (coordinateFieldPoint B hC L z hz) =
      LagrangianChosenCoarseFamily.pointValue ℂ B hC hZ L (coordinateFieldPoint B hC L w hw))
    (hnp : SourceNoFivePencil L (z ≫ LagrangianFamilyOrbitIsomorphism.coordinateGoodMap)) :
    ∃ g : M9.PrimitiveStabilizer.Sp6 L,
      PrimitiveFieldMatrixAction.actPoint L g
        (z ≫ LagrangianFamilyOrbitIsomorphism.coordinateGoodOpen.ι) hz =
      w ≫ LagrangianFamilyOrbitIsomorphism.coordinateGoodOpen.ι :=
  exists_coordinate_native_orbit_of_curveIso L z w hz hw
    (LagrangianChosenCoarseCurveIso.physicalIso ℂ B hC hZ L
      (coordinateFieldPoint B hC L z hz) (coordinateFieldPoint B hC L w hw) hzw)
    (LagrangianChosenCoarseCurveIso.physicalIso_hom_snd ℂ B hC hZ L
      (coordinateFieldPoint B hC L z hz) (coordinateFieldPoint B hC L w hw) hzw) hnp

end M9Native.LagrangianChosenCoarseFieldOrbit
