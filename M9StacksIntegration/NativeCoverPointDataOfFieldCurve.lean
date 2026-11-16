module

public import M9StacksIntegration.NativeCoverFamilyAtlasArrow
public import M9StacksIntegration.NativeSmoothGenusPhysicalIsoArrow
public import M9StacksIntegration.NativeSmoothGenusSourceFullness
public import M9StacksIntegration.NativeGenusNineFieldObjectCurve

/-! Actual PointData from an original field-curve pullback.

The target curve and its recovery are extracted from the actual target
classifier value. A genuine original pullback to the source family then
constructs the native comparison over the same coefficient field.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
attribute [local implicit_reducible] CategoryTheory.BasedCategory.ofFunctor

universe u

namespace M9Native.NativeCoverPointDataOfFieldCurve

variable (B : BigFppfSite.{u}) (hZ : B.Contains integerBase)
  (K : Type u) [Field K] (hK : B.Contains (Spec (.of K)))

abbrev schemeFunctor := BigFppfOver.toScheme B integerBase hZ
abbrev posted := Over.map (NativeSmoothGenusCoarseClassifier.coefficientArrow B hZ K hK)
abbrev rawProjection := NativeSmoothGenusCoarseClassifier.originalProjection
  B hZ K hK 9 (by decide)

section SourceFamily
variable (Y : BigFppfOver B (Spec (.of K)) hK)
  {Z : BigFppfOver B integerBase hZ}
  (q : Z ⟶ (posted B hZ K hK).obj Y)
  (hq : M9StandaloneDraft.SchemeCurve ((schemeFunctor B hZ).map q) 9)
  {T : BigFppfOver B (Spec (.of K)) hK} (u : T ⟶ Y)

/-- Recovery of the actual source classifier at the specified source point. -/
def sourceValueIso :
    (rawProjection B hZ K hK).obj
        ((NativeCoverFamilyAtlasArrow.sourceClassifier B hZ K hK Y q hq).hom.hom.toFunctor.obj
          (Over.mk u)) ≅
      NativeSmoothGenusClassifierCurveIso.pulledFamily B hZ q 9 hq
        ((posted B hZ K hK).map u) :=
  NativeSmoothGenusCoarseClassifier.originalValueIso B hZ K hK Y q 9 (by decide) hq
      (Over.mk u) ≪≫
    NativeSmoothGenusClassifierCurveIso.valueIso B hZ q 9 hq
      ((posted B hZ K hK).map u)

theorem sourceValueIso_lift :
    (curvesProjectionOver B hZ).IsHomLift (𝟙 ((posted B hZ K hK).obj T))
      (sourceValueIso B hZ K hK Y q hq u).hom := by
  let raw := ((NativeSmoothGenusCurveClassifier.classifyingMor B hZ q 9 hq).toFunctor.obj
    ((Over.post (posted B hZ K hK)).obj (Over.mk u))).obj
  have hr : raw.base = (posted B hZ K hK).obj T :=
    Functor.congr_obj (NativeSmoothGenusCurveClassifier.classifyingMor B hZ q 9 hq).w
      ((Over.post (posted B hZ K hK)).obj (Over.mk u))
  have h₁ := (curvesSmallEquivalenceOver B hZ).isHomLift_unitIso_inv_app raw
  change (curvesProjectionOver B hZ).IsHomLift (𝟙 raw.base)
    (NativeSmoothGenusCoarseClassifier.originalValueIso B hZ K hK Y q 9 (by decide) hq
      (Over.mk u)).hom at h₁
  rw [hr] at h₁
  haveI : (curvesProjectionOver B hZ).IsHomLift (𝟙 ((posted B hZ K hK).obj T))
      (NativeSmoothGenusCoarseClassifier.originalValueIso B hZ K hK Y q 9 (by decide) hq
        (Over.mk u)).hom := h₁
  haveI : (curvesProjectionOver B hZ).IsHomLift (𝟙 ((posted B hZ K hK).obj T))
      (NativeSmoothGenusClassifierCurveIso.valueIso B hZ q 9 hq
        ((posted B hZ K hK).map u)).hom :=
    NativeSmoothGenusClassifierCurveIso.valueIso_hom_lift B hZ q 9 hq
      ((posted B hZ K hK).map u)
  change (curvesProjectionOver B hZ).IsHomLift (𝟙 ((posted B hZ K hK).obj T))
    ((NativeSmoothGenusCoarseClassifier.originalValueIso B hZ K hK Y q 9 (by decide) hq
      (Over.mk u)).hom ≫
      (NativeSmoothGenusClassifierCurveIso.valueIso B hZ q 9 hq
        ((posted B hZ K hK).map u)).hom)
  exact IsHomLift.comp_lift_id_left _ (𝟙 ((posted B hZ K hK).obj T)) _ _

section PhysicalPullback
variable {W : BigFppfOver B integerBase hZ}
  (ρ : W ⟶ (posted B hZ K hK).obj T)
  (hρ : M9StandaloneDraft.SchemeCurve ((schemeFunctor B hZ).map ρ) 9)
  (r : (schemeFunctor B hZ).obj W ⟶ (schemeFunctor B hZ).obj Z)
  (sq : IsPullback r ((schemeFunctor B hZ).map ρ) ((schemeFunctor B hZ).map q)
    ((schemeFunctor B hZ).map ((posted B hZ K hK).map u)))

/-- The native total-space isomorphism is constructed from the genuine
original square and the native pullback's genuine original square. -/
def sitePullbackIso : W ≅ pullback q ((posted B hZ K hK).map u) :=
  NativeSmoothGenusPhysicalIsoArrow.siteIso B hZ
    (sq.isoPullback ≪≫
      (NativeSmoothGenusClassifierCurveIso.physicalPullbackIso B hZ q
        ((posted B hZ K hK).map u)).symm)

theorem sitePullbackIso_projection :
    (sitePullbackIso B hZ K hK Y q u ρ r sq).hom ≫
        NativeSmoothGenusClassifierCurveIso.pulledProjection B hZ q
          ((posted B hZ K hK).map u) = ρ := by
  apply (schemeFunctor B hZ).map_injective
  rw [Functor.map_comp]
  change (sq.isoPullback.hom ≫
      (NativeSmoothGenusClassifierCurveIso.physicalPullbackIso B hZ q
        ((posted B hZ K hK).map u)).inv) ≫
      (schemeFunctor B hZ).map (NativeSmoothGenusClassifierCurveIso.pulledProjection B hZ q
        ((posted B hZ K hK).map u)) = (schemeFunctor B hZ).map ρ
  rw [Category.assoc]
  have hi :
      (NativeSmoothGenusClassifierCurveIso.physicalPullbackIso B hZ q
        ((posted B hZ K hK).map u)).inv ≫
          (schemeFunctor B hZ).map (NativeSmoothGenusClassifierCurveIso.pulledProjection B hZ q
            ((posted B hZ K hK).map u)) =
        pullback.snd ((schemeFunctor B hZ).map q)
          ((schemeFunctor B hZ).map ((posted B hZ K hK).map u)) := by
    rw [Iso.inv_comp_eq]
    exact (NativeSmoothGenusClassifierCurveIso.physicalPullbackIso_hom_snd B hZ q
      ((posted B hZ K hK).map u)).symm
  rw [hi]
  exact sq.isoPullback_hom_snd

/-- The actual curve families are isomorphic; cartesianity follows from
the original pullback and the total-space isomorphism. -/
def physicalFamilyIso :
    M9StacksIntegration.NativeSchematicCurveFamily.schemeCurveFamily B hZ ρ 9 hρ ≅
      NativeSmoothGenusClassifierCurveIso.pulledFamily B hZ q 9 hq
        ((posted B hZ K hK).map u) :=
  NativeSmoothGenusPhysicalIsoArrow.rawFamilyIso B hZ
    (Iso.refl ((posted B hZ K hK).obj T))
    ((schemeSpaceFunctor B integerBase hZ).mapIso
      (sitePullbackIso B hZ K hK Y q u ρ r sq)) (by
      change schemeSpaceMap (sitePullbackIso B hZ K hK Y q u ρ r sq).hom ≫
          schemeSpaceMap (NativeSmoothGenusClassifierCurveIso.pulledProjection B hZ q
            ((posted B hZ K hK).map u)) = schemeSpaceMap ρ ≫ schemeSpaceMap (𝟙 _)
      rw [show schemeSpaceMap (𝟙 ((posted B hZ K hK).obj T)) = 𝟙 _ from
          (schemeSpaceFunctor B integerBase hZ).map_id _, Category.comp_id,
        ← schemeSpaceMap_comp, sitePullbackIso_projection])

theorem physicalFamilyIso_lift :
    (curvesProjectionOver B hZ).IsHomLift (𝟙 ((posted B hZ K hK).obj T))
      (physicalFamilyIso B hZ K hK Y q hq u ρ hρ r sq).hom := by
  have h := IsHomLift.map (curvesProjectionOver B hZ)
    (physicalFamilyIso B hZ K hK Y q hq u ρ hρ r sq).hom
  change (curvesProjectionOver B hZ).IsHomLift (𝟙 ((posted B hZ K hK).obj T))
    (physicalFamilyIso B hZ K hK Y q hq u ρ hρ r sq).hom at h
  exact h

/-- A genuine original pullback identifies the source classifier value
with the same native original model, without a comparison premise. -/
def sourceModelIso :
    (rawProjection B hZ K hK).obj
        ((NativeCoverFamilyAtlasArrow.sourceClassifier B hZ K hK Y q hq).hom.hom.toFunctor.obj
          (Over.mk u)) ≅
      M9StacksIntegration.NativeSchematicCurveFamily.schemeCurveFamily B hZ ρ 9 hρ :=
  sourceValueIso B hZ K hK Y q hq u ≪≫
    (physicalFamilyIso B hZ K hK Y q hq u ρ hρ r sq).symm

theorem sourceModelIso_lift :
    (curvesProjectionOver B hZ).IsHomLift (𝟙 ((posted B hZ K hK).obj T))
      (sourceModelIso B hZ K hK Y q hq u ρ hρ r sq).hom := by
  haveI := sourceValueIso_lift B hZ K hK Y q hq u
  haveI := physicalFamilyIso_lift B hZ K hK Y q hq u ρ hρ r sq
  haveI : (curvesProjectionOver B hZ).IsHomLift (𝟙 ((posted B hZ K hK).obj T))
      (physicalFamilyIso B hZ K hK Y q hq u ρ hρ r sq).inv := inferInstance
  change (curvesProjectionOver B hZ).IsHomLift (𝟙 ((posted B hZ K hK).obj T))
    ((sourceValueIso B hZ K hK Y q hq u).hom ≫
      (physicalFamilyIso B hZ K hK Y q hq u ρ hρ r sq).inv)
  exact IsHomLift.comp_lift_id_left _ _ _ _

end PhysicalPullback
end SourceFamily

section ExtractedTarget
variable (Y V : BigFppfOver B (Spec (.of K)) hK)
  {Z : BigFppfOver B integerBase hZ}
  (q : Z ⟶ (posted B hZ K hK).obj Y)
  (hq : M9StandaloneDraft.SchemeCurve ((schemeFunctor B hZ).map q) 9)
  (b : Stack.schemeStack.{u,u+1} B (Spec (.of K)) hK V ⟶
    CoverFamilyStackPullback.sourceStack B hZ K hK)
  (L : Type u) [Field L] (hL : B.Contains (Spec (.of L))) (coefficient : K →+* L)

abbrev testBase := NativeGenusNineFieldObjectCurve.fieldBase B K hK L hL coefficient

variable (v : testBase B K hK L hL coefficient ⟶ V)

abbrev targetObject := b.hom.hom.toFunctor.obj (Over.mk v)

theorem targetObject_base :
    (CoverFamilyStackPullback.sourceStack B hZ K hK).val.val.p.obj
        (targetObject B hZ K hK V b L hL coefficient v) =
      testBase B K hK L hL coefficient :=
  Functor.congr_obj b.hom.hom.w (Over.mk v)

/-- This is the actual original curve extracted from the actual target
classifier value, rather than a model supplied to the client. -/
abbrev originalCurve := NativeGenusNineFieldObjectCurve.original B hZ K hK L hL coefficient
  (targetObject B hZ K hK V b L hL coefficient v)
  (targetObject_base B hZ K hK V b L hL coefficient v)

abbrev modelProjection := NativeGenusNineFieldObjectCurve.nativeProjection
  B hZ K hK L hL coefficient (targetObject B hZ K hK V b L hL coefficient v)
  (targetObject_base B hZ K hK V b L hL coefficient v)

variable (u : testBase B K hK L hL coefficient ⟶ Y)
  (r : (originalCurve B hZ K hK V b L hL coefficient v).left ⟶
    (schemeFunctor B hZ).obj Z)
  (sq : IsPullback r (originalCurve B hZ K hK V b L hL coefficient v).hom
    ((schemeFunctor B hZ).map q)
    ((schemeFunctor B hZ).map ((posted B hZ K hK).map u)))

include sq in
theorem modelPullbackSquare :
    IsPullback r ((schemeFunctor B hZ).map
      (modelProjection B hZ K hK V b L hL coefficient v))
      ((schemeFunctor B hZ).map q)
      ((schemeFunctor B hZ).map ((posted B hZ K hK).map u)) := by
  rw [NativeGenusNineFieldObjectCurve.nativeProjection_original]
  exact sq

/-- Both raw values are compared to the SAME genuinely extracted model. -/
def rawComparisonIso :
    (rawProjection B hZ K hK).obj
        ((NativeCoverFamilyAtlasArrow.sourceClassifier B hZ K hK Y q hq).hom.hom.toFunctor.obj
          (Over.mk u)) ≅
      (rawProjection B hZ K hK).obj (targetObject B hZ K hK V b L hL coefficient v) :=
  sourceModelIso B hZ K hK Y q hq u
    (modelProjection B hZ K hK V b L hL coefficient v)
    (NativeGenusNineFieldObjectCurve.nativeProjection_schemeCurve B hZ K hK L hL coefficient
      (targetObject B hZ K hK V b L hL coefficient v)
      (targetObject_base B hZ K hK V b L hL coefficient v)) r
    (modelPullbackSquare B hZ K hK Y V q b L hL coefficient v u r sq) ≪≫
    (NativeGenusNineFieldObjectCurve.rawModelIso B hZ K hK L hL coefficient
      (targetObject B hZ K hK V b L hL coefficient v)
      (targetObject_base B hZ K hK V b L hL coefficient v)).symm

theorem rawComparisonIso_lift :
    (curvesProjectionOver B hZ).IsHomLift
      (𝟙 ((posted B hZ K hK).obj (testBase B K hK L hL coefficient)))
      (rawComparisonIso B hZ K hK Y V q hq b L hL coefficient v u r sq).hom :=
  NativeFieldSchemeModelEndpoints.recovery_comp_symm_lift B hZ
    ((posted B hZ K hK).obj (testBase B K hK L hL coefficient))
    (sourceModelIso B hZ K hK Y q hq u
      (modelProjection B hZ K hK V b L hL coefficient v)
      (NativeGenusNineFieldObjectCurve.nativeProjection_schemeCurve B hZ K hK L hL coefficient
        (targetObject B hZ K hK V b L hL coefficient v)
        (targetObject_base B hZ K hK V b L hL coefficient v)) r
      (modelPullbackSquare B hZ K hK Y V q b L hL coefficient v u r sq))
    (NativeGenusNineFieldObjectCurve.rawModelIso B hZ K hK L hL coefficient
      (targetObject B hZ K hK V b L hL coefficient v)
      (targetObject_base B hZ K hK V b L hL coefficient v))
    (sourceModelIso_lift B hZ K hK Y q hq u
      (modelProjection B hZ K hK V b L hL coefficient v)
      (NativeGenusNineFieldObjectCurve.nativeProjection_schemeCurve B hZ K hK L hL coefficient
        (targetObject B hZ K hK V b L hL coefficient v)
        (targetObject_base B hZ K hK V b L hL coefficient v)) r
      (modelPullbackSquare B hZ K hK Y V q b L hL coefficient v u r sq))
    (NativeGenusNineFieldObjectCurve.rawModelIso_lift B hZ K hK L hL coefficient
      (targetObject B hZ K hK V b L hL coefficient v)
      (targetObject_base B hZ K hK V b L hL coefficient v))

/-- The true native fibre-product point is constructed from the genuine
original curve pullback and the target's derived original field model. -/
def pointData : CoverFamilyStackPullback.PointData B hZ K hK Y V
    (NativeCoverFamilyAtlasArrow.sourceClassifier B hZ K hK Y q hq) b
    (P := testBase B K hK L hL coefficient) := by
  let α := (rawComparisonIso B hZ K hK Y V q hq b L hL coefficient v u r sq).hom
  have hα := rawComparisonIso_lift B hZ K hK Y V q hq b L hL coefficient v u r sq
  have hx : (CoverFamilyStackPullback.sourceStack B hZ K hK).val.val.p.obj
      ((NativeCoverFamilyAtlasArrow.sourceClassifier B hZ K hK Y q hq).hom.hom.toFunctor.obj
        (Over.mk u)) = testBase B K hK L hL coefficient :=
    Functor.congr_obj
      (NativeCoverFamilyAtlasArrow.sourceClassifier B hZ K hK Y q hq).hom.hom.w (Over.mk u)
  have hy := targetObject_base B hZ K hK V b L hL coefficient v
  let a := NativeSmoothGenusSourceFullness.liftRawArrow B hZ 9 (by decide) K hK
    (testBase B K hK L hL coefficient) hx hy α hα
  have ha := NativeSmoothGenusSourceFullness.liftRawArrow_isHomLift B hZ 9 (by decide) K hK
    (testBase B K hK L hL coefficient) hx hy α hα
  haveI : (CoverFamilyStackPullback.sourceStack B hZ K hK).val.val.p.IsHomLift
      (𝟙 (testBase B K hK L hL coefficient)) a := ha
  haveI : (CoverFamilyStackPullback.sourceStack B hZ K hK).val.val.p.IsStronglyCartesian
      (𝟙 (testBase B K hK L hL coefficient)) a :=
    (CoverFamilyStackPullback.sourceStack B hZ K hK).val.property.isStronglyCartesian_homLift
      (𝟙 (testBase B K hK L hL coefficient)) a
  haveI : IsIso a := Functor.IsStronglyCartesian.isIso_of_base_isIso
    (p := (CoverFamilyStackPullback.sourceStack B hZ K hK).val.val.p)
    (f := 𝟙 (testBase B K hK L hL coefficient)) a
  exact ⟨u,v,asIso a,ha⟩

theorem pointData_left :
    (pointData B hZ K hK Y V q hq b L hL coefficient v u r sq).left = u := rfl

theorem pointData_right :
    (pointData B hZ K hK Y V q hq b L hL coefficient v u r sq).right = v := rfl

include sq in
theorem exists_pointData :
    ∃ D : CoverFamilyStackPullback.PointData B hZ K hK Y V
        (NativeCoverFamilyAtlasArrow.sourceClassifier B hZ K hK Y q hq) b
        (P := testBase B K hK L hL coefficient), D.left = u ∧ D.right = v :=
  ⟨pointData B hZ K hK Y V q hq b L hL coefficient v u r sq, rfl, rfl⟩

end ExtractedTarget
end M9Native.NativeCoverPointDataOfFieldCurve
end
