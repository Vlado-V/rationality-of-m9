module

public import M9StacksIntegration.LagrangianChosenCoarseCoordinateShift
public import M9StacksIntegration.NativeSmoothGenusPhysicalCoarseMap
public import M9StacksIntegration.LagrangianGoodOpenConstantAction
public import M9StacksIntegration.SimultaneousNativeGeometricModel

@[expose] public section

/-! Constant original Sp6 invariance of the ACTUAL chosen coarse map.
The genuine C-conjugated physical family Iso constructs the raw chosen-unit
arrow, then actual source fullness and unit reflection identify the maps.
The resulting equality is an equality of original presheaf morphisms, so
the final invariant assertion holds on all original tests without Contains.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
attribute [local implicit_reducible] CategoryTheory.BasedCategory.ofFunctor

namespace M9Native.LagrangianChosenCoarseAction
open M9StacksIntegration.AllTestBoundedCharts
  M9StacksIntegration.AllTestNativeOriginalFunctor
  M9StacksIntegration.AllTestNativeOriginalPullbacks
open LagrangianFamilyOrbitIsomorphism LagrangianParameterCoordinates

variable (B : BigFppfSite) (hC : B.Contains (Spec (.of ℂ)))

/-- The exact original constant action on the same derived bounded source. -/
def nativeAction (g : PrimitiveConstantFieldAction.Sp6) :
    LagrangianChosenCoarseCoordinateShift.base B hC ⟶
      LagrangianChosenCoarseCoordinateShift.base B hC :=
  Over.homMk (ObjectProperty.homMk (LagrangianGoodOpenConstantAction.coordinateAction g))
    (ObjectProperty.hom_ext _ (LagrangianGoodOpenConstantAction.coordinateAction_projection g))

theorem nativeAction_toScheme (g : PrimitiveConstantFieldAction.Sp6) :
    (BigFppfOver.toScheme B (Spec (.of ℂ)) hC).map (nativeAction B hC g) =
      LagrangianGoodOpenConstantAction.coordinateAction g := rfl

/-- The same actual endomorphism on the full original site. -/
def originalAction (g : PrimitiveConstantFieldAction.Sp6) :
    (boundedInclusion B ℂ hC).obj (LagrangianChosenCoarseCoordinateShift.base B hC) ⟶
      (boundedInclusion B ℂ hC).obj (LagrangianChosenCoarseCoordinateShift.base B hC) :=
  (boundedInclusion B ℂ hC).map (nativeAction B hC g)

theorem originalAction_eq_overAction (g : PrimitiveConstantFieldAction.Sp6) :
    originalAction B hC g = LagrangianGoodOpenConstantAction.overAction g := rfl

variable (hZ : B.Contains integerBase)

/-- The original RAW chosen map is invariant after the true coordinate
precomposition; the actual C-conjugation is used in the physical Iso. -/
theorem nativeRawMap_coordinate_action (g : PrimitiveConstantFieldAction.Sp6) :
    schemeSpaceMap (nativeAction B hC g ≫ LagrangianChosenCoarseCoordinateShift.toRaw B hC) ≫
      LagrangianChosenCoarseFamily.nativeMap ℂ B hC hZ =
    schemeSpaceMap (LagrangianChosenCoarseCoordinateShift.toRaw B hC) ≫
      LagrangianChosenCoarseFamily.nativeMap ℂ B hC hZ := by
  have hpq :
      (coordinateGoodMap ≫ (LagrangianLinearSectionGenericSmooth.goodOpen ℂ).ι) ≫
          rawAction (PrimitiveRingFieldBridge.fromOriginal g) =
        (LagrangianGoodOpenConstantAction.coordinateAction g ≫ coordinateGoodMap) ≫
          (LagrangianLinearSectionGenericSmooth.goodOpen ℂ).ι := by
    calc
      _ = (coordinateGoodOpen.ι ≫ coordinateChange.hom) ≫
          rawAction (PrimitiveRingFieldBridge.fromOriginal g) := by
        rw [coordinateGoodMap_inclusion]
      _ = (coordinateGoodOpen.ι ≫ PrimitiveConstantFieldAction.schemeMap g) ≫
          coordinateChange.hom := by
        rw [Category.assoc, ← schemeMap_coordinateChange, ← Category.assoc]
      _ = (LagrangianGoodOpenConstantAction.coordinateAction g ≫ coordinateGoodOpen.ι) ≫
          coordinateChange.hom := by
        rw [LagrangianGoodOpenConstantAction.coordinateAction_comp]
      _ = _ := by simp only [Category.assoc, coordinateGoodMap_inclusion]
  let e := rawGoodPullbackIso coordinateGoodMap
    (LagrangianGoodOpenConstantAction.coordinateAction g ≫ coordinateGoodMap)
    (PrimitiveRingFieldBridge.fromOriginal g) hpq
  have he := rawGoodPullbackIso_hom_snd coordinateGoodMap
    (LagrangianGoodOpenConstantAction.coordinateAction g ≫ coordinateGoodMap)
    (PrimitiveRingFieldBridge.fromOriginal g) hpq
  have h := NativeSmoothGenusPhysicalCoarseMap.classifyingMaps_eq_of_physicalIso
    B hZ ℂ hC 9 (by decide)
    (LagrangianNativeGenusNineFamily.integerProjection ℂ B hC hZ)
    (LagrangianNativeGenusNineFamily.integerProjection ℂ B hC hZ)
    (LagrangianNativeGenusNineFamily.original_schemeCurve ℂ B hC hZ)
    (LagrangianNativeGenusNineFamily.original_schemeCurve ℂ B hC hZ)
    (LagrangianChosenCoarseCoordinateShift.toRaw B hC)
    (nativeAction B hC g ≫ LagrangianChosenCoarseCoordinateShift.toRaw B hC) e he
  change schemeSpaceMap (LagrangianChosenCoarseCoordinateShift.toRaw B hC) ≫
      LagrangianChosenCoarseFamily.nativeMap ℂ B hC hZ =
    schemeSpaceMap (nativeAction B hC g ≫ LagrangianChosenCoarseCoordinateShift.toRaw B hC) ≫
      LagrangianChosenCoarseFamily.nativeMap ℂ B hC hZ at h
  exact h.symm

/-- Invariance is proved for the ACTUAL coordinate-shifted chosen map. -/
theorem nativeMap_action (g : PrimitiveConstantFieldAction.Sp6) :
    schemeSpaceMap (nativeAction B hC g) ≫ LagrangianChosenCoarseCoordinateShift.nativeMap B hC hZ =
      LagrangianChosenCoarseCoordinateShift.nativeMap B hC hZ := by
  calc
    _ = schemeSpaceMap (nativeAction B hC g) ≫
        (schemeSpaceMap (LagrangianChosenCoarseCoordinateShift.toRaw B hC) ≫
          LagrangianChosenCoarseFamily.nativeMap ℂ B hC hZ) :=
      congrArg (fun f => schemeSpaceMap (nativeAction B hC g) ≫ f)
        (LagrangianChosenCoarseCoordinateShift.nativeMap_eq_precompose B hC hZ)
    _ = schemeSpaceMap (nativeAction B hC g ≫ LagrangianChosenCoarseCoordinateShift.toRaw B hC) ≫
        LagrangianChosenCoarseFamily.nativeMap ℂ B hC hZ := by
      rw [schemeSpaceMap_comp, Category.assoc]
    _ = _ := nativeRawMap_coordinate_action B hC hZ g
    _ = _ := (LagrangianChosenCoarseCoordinateShift.nativeMap_eq_precompose B hC hZ).symm

/-- Equality of actual original presheaf morphisms retains all original tests. -/
theorem originalMap_action (g : PrimitiveConstantFieldAction.Sp6) :
    yoneda.map (originalAction B hC g) ≫ LagrangianChosenCoarseCoordinateShift.originalMap B hC hZ =
      LagrangianChosenCoarseCoordinateShift.originalMap B hC hZ := by
  have h := congrArg (fun f : schemeSpace (LagrangianChosenCoarseCoordinateShift.base B hC) ⟶
      LagrangianChosenCoarseCoordinateShift.target B hC hZ =>
    originalChart ℂ B hC (LagrangianChosenCoarseCoordinateShift.target B hC hZ)
      (LagrangianChosenCoarseCoordinateShift.base B hC) f.hom) (nativeMap_action B hC hZ g)
  change originalChart ℂ B hC (LagrangianChosenCoarseCoordinateShift.target B hC hZ)
    (LagrangianChosenCoarseCoordinateShift.base B hC)
    (yoneda.map (nativeAction B hC g) ≫ (LagrangianChosenCoarseCoordinateShift.nativeMap B hC hZ).hom) =
    originalChart ℂ B hC (LagrangianChosenCoarseCoordinateShift.target B hC hZ)
      (LagrangianChosenCoarseCoordinateShift.base B hC)
      (LagrangianChosenCoarseCoordinateShift.nativeMap B hC hZ).hom at h
  rw [SimultaneousNativeGeometricModel.originalChart_precompose ℂ B hC
    (nativeAction B hC g) (LagrangianChosenCoarseCoordinateShift.nativeMap B hC hZ)] at h
  exact h

/-- The exact frozen invariant-field constant-action assertion holds on
EVERY original complex test scheme; no site containment is assumed. -/
theorem originalMap_orbit_all_tests (T : Over PrimitiveFamilyFreeAction.base)
    (x y : T ⟶ PrimitiveGenericOpenPoints.openOver LagrangianChosenCoarseCoordinateShift.goodOpen)
    (g : PrimitiveConstantFieldAction.Sp6)
    (hxy : x ≫ PrimitiveGenericOpenPoints.inclusionOver LagrangianChosenCoarseCoordinateShift.goodOpen ≫
        PrimitiveConstantFieldAction.overMap g =
      y ≫ PrimitiveGenericOpenPoints.inclusionOver LagrangianChosenCoarseCoordinateShift.goodOpen) :
    (LagrangianChosenCoarseCoordinateShift.originalMap B hC hZ).app (op T) x =
      (LagrangianChosenCoarseCoordinateShift.originalMap B hC hZ).app (op T) y := by
  have hy : x ≫ originalAction B hC g = y :=
    LagrangianGoodOpenConstantAction.eq_overAction_of_relation T x y g hxy
  have h := congrArg (fun f => f.app (op T) x) (originalMap_action B hC hZ g)
  change (LagrangianChosenCoarseCoordinateShift.originalMap B hC hZ).app (op T)
      (x ≫ originalAction B hC g) =
    (LagrangianChosenCoarseCoordinateShift.originalMap B hC hZ).app (op T) x at h
  rw [hy] at h
  exact h.symm

end M9Native.LagrangianChosenCoarseAction
