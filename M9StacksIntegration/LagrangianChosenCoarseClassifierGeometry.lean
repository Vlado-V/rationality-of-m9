module

public import M9StacksIntegration.LagrangianChosenCoarseAction
public import M9StacksIntegration.LagrangianChosenCoarseFieldOrbit
public import M9StacksIntegration.PrimitiveNativeClassifierRationalOpen

@[expose] public section

/-! Exact classifier geometry on the SAME actual chosen M9 target and
its genuine coordinate-good source. Constant invariance and actual
chosen-coarse orbit fibres are proved providers. Only the explicit
all-original-field source no5 condition remains in this intermediate;
no desired classifier geometry, chart, quotient or rationality is assumed. -/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 2200000
set_option maxRecDepth 4096
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open MonoidalCategory CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

namespace M9Native.LagrangianChosenCoarseClassifierGeometry
open PrimitiveGrassmannianAction PrimitiveGenericOpenPoints PrimitiveUniversalExtensionPoints
open M9StacksIntegration.AllTestBoundedCharts
  M9StacksIntegration.AllTestNativeOriginalPullbacks

/-- The honest curve condition, on every original ACL complex-algebra
field point of the unchanged coordinate-good source. No site cutoff. -/
def AllFieldSourceNoFive : Prop :=
  ∀ (L : Type) [Field L] [IsAlgClosed L] [Algebra ℂ L]
    (x : overField L ⟶ openOver LagrangianChosenCoarseCoordinateShift.goodOpen),
    LagrangianGoodFieldOrbit.SourceNoFivePencil L
      (x.left ≫ LagrangianFamilyOrbitIsomorphism.coordinateGoodMap)

section FieldPoints
variable (L : Type) [Field L] [Algebra ℂ L]
  (x : overField L ⟶ openOver LagrangianChosenCoarseCoordinateShift.goodOpen)

/-- The original Over morphism supplies the actual coefficient triangle. -/
theorem field_projection :
    (x.left ≫ LagrangianChosenCoarseCoordinateShift.goodOpen.ι) ≫
      LagrangianLinearSections.parameterProjection ℂ =
      Spec.map (CommRingCat.ofHom (algebraMap ℂ L)) := by
  have h := Over.w x
  change x.left ≫ (LagrangianChosenCoarseCoordinateShift.goodOpen.ι ≫
    LagrangianLinearSections.parameterProjection ℂ) =
    Spec.map (CommRingCat.ofHom (algebraMap ℂ L)) at h
  simpa only [Category.assoc] using h

/-- The frozen field action receives the SAME original ambient point,
including its genuine dependent coefficient-map proof. -/
theorem overPoint_eq_ambient :
    PrimitiveFieldMatrixAction.overPoint L
      (x.left ≫ LagrangianChosenCoarseCoordinateShift.goodOpen.ι) (field_projection L x) =
      x ≫ inclusionOver LagrangianChosenCoarseCoordinateShift.goodOpen := by
  apply Over.OverMorphism.ext
  rfl
end FieldPoints

variable (B : BigFppfSite) (hC : B.Contains (Spec (.of ℂ))) (hZ : B.Contains integerBase)

/-- The criterion's original classifier is literally Root's SAME actual
shifted original classifier; this is not a compatibility hypothesis. -/
theorem originalClassifier_eq :
    PrimitiveNativeClassifierRationalOpen.originalClassifier B hC
      (LagrangianChosenCoarseFamily.target ℂ B hC hZ)
      LagrangianChosenCoarseCoordinateShift.goodOpen
      (LagrangianChosenCoarseCoordinateShift.nativeMap B hC hZ).hom =
      LagrangianChosenCoarseCoordinateShift.originalMap B hC hZ := rfl

section FieldValues
variable (L : Type) [Field L] [IsAlgClosed L] [Algebra ℂ L]
  (x : overField L ⟶ openOver LagrangianChosenCoarseCoordinateShift.goodOpen)

/-- Precomposition gives the exact actual raw original field point
already used by the chosen-coarse orbit theorem. -/
theorem rawFieldPoint_eq :
    x ≫ LagrangianChosenCoarseCoordinateShift.originalToRaw B hC =
      LagrangianChosenCoarseFieldOrbit.coordinateFieldPoint B hC L x.left (field_projection L x) := by
  apply Over.OverMorphism.ext
  rfl

/-- Literal all-original classifier evaluation is the same chosen raw
pointValue after the genuine C coordinate map. -/
theorem classifier_value :
    (PrimitiveNativeClassifierRationalOpen.originalClassifier B hC
      (LagrangianChosenCoarseFamily.target ℂ B hC hZ)
      LagrangianChosenCoarseCoordinateShift.goodOpen
      (LagrangianChosenCoarseCoordinateShift.nativeMap B hC hZ).hom).app (op (overField L)) x =
    LagrangianChosenCoarseFamily.pointValue ℂ B hC hZ L
      (LagrangianChosenCoarseFieldOrbit.coordinateFieldPoint B hC L x.left (field_projection L x)) := by
  change (LagrangianChosenCoarseCoordinateShift.originalMap B hC hZ).app (op (overField L)) x = _
  calc
    _ = (LagrangianChosenCoarseFamily.originalMap ℂ B hC hZ).app (op (overField L))
        (x ≫ LagrangianChosenCoarseCoordinateShift.originalToRaw B hC) :=
      LagrangianChosenCoarseCoordinateShift.originalMap_app_precompose B hC hZ (overField L) x
    _ = (LagrangianChosenCoarseFamily.originalMap ℂ B hC hZ).app (op (overField L))
        (LagrangianChosenCoarseFieldOrbit.coordinateFieldPoint B hC L x.left (field_projection L x)) :=
      congrArg (fun q => (LagrangianChosenCoarseFamily.originalMap ℂ B hC hZ).app
        (op (overField L)) q) (rawFieldPoint_eq B hC L x)
end FieldValues

/-- The exact chosen-source ClassifierGeometry, derived from actual
all-original invariance and actual chosen-coarse orbit fibres. The sole
honest intermediate input is the explicit original-field source no5. -/
theorem classifierGeometry_of_sourceNoFive (hnp : AllFieldSourceNoFive) :
    PrimitiveNativeClassifierRationalOpen.ClassifierGeometry B hC
      (LagrangianChosenCoarseFamily.target ℂ B hC hZ)
      LagrangianChosenCoarseCoordinateShift.goodOpen
      (LagrangianChosenCoarseCoordinateShift.nativeMap B hC hZ).hom := by
  refine ⟨?_,?_⟩
  · intro T x y g hxy
    rw [originalClassifier_eq]
    exact LagrangianChosenCoarseAction.originalMap_orbit_all_tests B hC hZ T x y g hxy
  · intro L _ _ _ x y hxy
    have hv := (classifier_value B hC hZ L x).symm.trans
      (hxy.trans (classifier_value B hC hZ L y))
    obtain ⟨g,hg⟩ := LagrangianChosenCoarseFieldOrbit.exists_coordinate_native_orbit_of_coarseEq
      B hC hZ L x.left y.left (field_projection L x) (field_projection L y) hv (hnp L x)
    refine ⟨g,?_⟩
    have hc : PrimitiveFieldMatrixAction.actPoint L g
        (x.left ≫ LagrangianChosenCoarseCoordinateShift.goodOpen.ι) (field_projection L x) =
        (lift (PrimitiveOriginalExtensionAction.nativeGroupPoint g)
          (x ≫ inclusionOver LagrangianChosenCoarseCoordinateShift.goodOpen) ≫ nativeAction.act).left := by
      unfold PrimitiveFieldMatrixAction.actPoint
      rw [overPoint_eq_ambient]
    exact hc.symm.trans hg

end M9Native.LagrangianChosenCoarseClassifierGeometry
