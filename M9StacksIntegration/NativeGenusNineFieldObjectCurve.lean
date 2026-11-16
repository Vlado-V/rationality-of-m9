module

public import M9StacksIntegration.NativeFieldSchemeModelEndpoints
public import M9StacksIntegration.NativeSmoothGenusCoarseRecovery
public import M9StacksIntegration.AllTestNativeFieldSchemeCurve

/-! The original field-model and classifier-unit branch, using the
separately checked membership/base core. All geometry and recovery data
are constructed from the actual source object. -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
attribute [local implicit_reducible] CategoryTheory.BasedCategory.ofFunctor
universe u
namespace M9Native.NativeGenusNineFieldObjectCurve
variable (B : BigFppfSite.{u}) (hZ : B.Contains integerBase)
  (K : Type u) [Field K] (hK : B.Contains (Spec (.of K)))
  (L : Type u) [Field L] (hL : B.Contains (Spec (.of L))) (coefficient : K →+* L)
  (z : (source B hZ K hK).val.val.obj)
  (hz : (source B hZ K hK).val.val.p.obj z = fieldBase B K hK L hL coefficient)

/-- Original proper scheme model on the same original field, with the
complete original all-field curve predicate and same-base recovery. -/
structure Model where
  original : Over (Spec (.of L))
  proper : IsProper original.hom
  dimension : topologicalKrullDim original.left ≤ 1
  schemeCurve : M9StandaloneDraft.SchemeCurve original.hom 9
  recovery : (rawProjection B hZ K hK).obj z ≅
    @curveFamilyOfScheme L _ original proper B hZ hL dimension
  recovery_base : recovery.hom.baseMap =
    eqToHom (rawFamily_integerBase B hZ K hK L hL coefficient z hz)

/-- Construct the model from the actual chosen source object alone. -/
def model : Model B hZ K hK L hL coefficient z hz :=
  Classical.choice (by
    obtain ⟨X, hp, hd, hc, e, he⟩ :=
      M9StacksIntegration.AllTestNativeFieldSchemeCurve.exists_original_schemeCurve_of_native_field_family B hZ hL
          ((rawProjection B hZ K hK).obj z)
          (rawFamily_integerBase B hZ K hK L hL coefficient z hz) 9
          (originalProjection_membership B hZ K hK 9 (by decide) z)
    exact ⟨⟨X, hp, hd, hc, e, he⟩⟩)

abbrev original := (model B hZ K hK L hL coefficient z hz).original

/-- The extracted original model has its actual proper native bound. -/
theorem original_contains : B.Contains (original B hZ K hK L hL coefficient z hz).left :=
  NativeFieldSchemeModelEndpoints.contains B L hL
    (original B hZ K hK L hL coefficient z hz)
    (model B hZ K hK L hL coefficient z hz).proper

abbrev nativeTotal : BigFppfOver B integerBase hZ :=
  NativeFieldSchemeModelEndpoints.total B hZ L hL
    (original B hZ K hK L hL coefficient z hz)
    (model B hZ K hK L hL coefficient z hz).proper

abbrev nativeProjection : nativeTotal B hZ K hK L hL coefficient z hz ⟶
    integerFieldBase B hZ K hK L hL coefficient :=
  NativeFieldSchemeModelEndpoints.projection B hZ K hK L hL coefficient
    (original B hZ K hK L hL coefficient z hz)
    (model B hZ K hK L hL coefficient z hz).proper

theorem nativeProjection_original :
    (BigFppfOver.toScheme B integerBase hZ).map
      (nativeProjection B hZ K hK L hL coefficient z hz) =
    (original B hZ K hK L hL coefficient z hz).hom :=
  NativeFieldSchemeModelEndpoints.projection_original B hZ K hK L hL coefficient
    (original B hZ K hK L hL coefficient z hz)
    (model B hZ K hK L hL coefficient z hz).proper

theorem nativeProjection_schemeCurve : M9StandaloneDraft.SchemeCurve
    ((BigFppfOver.toScheme B integerBase hZ).map
      (nativeProjection B hZ K hK L hL coefficient z hz)) 9 :=
  NativeFieldSchemeModelEndpoints.projection_schemeCurve B hZ K hK L hL coefficient
    (original B hZ K hK L hL coefficient z hz)
    (model B hZ K hK L hL coefficient z hz).proper 9
    (model B hZ K hK L hL coefficient z hz).schemeCurve

abbrev nativeFamily : CurveFamily B hZ :=
  NativeFieldSchemeModelEndpoints.family B hZ K hK L hL coefficient
    (original B hZ K hK L hL coefficient z hz)
    (model B hZ K hK L hL coefficient z hz).proper 9
    (model B hZ K hK L hL coefficient z hz).schemeCurve

def modelFamilyIso :
    @curveFamilyOfScheme L _ (original B hZ K hK L hL coefficient z hz)
      (model B hZ K hK L hL coefficient z hz).proper B hZ hL
      (model B hZ K hK L hL coefficient z hz).dimension ≅
    nativeFamily B hZ K hK L hL coefficient z hz :=
  NativeFieldSchemeModelEndpoints.comparison B hZ K hK L hL coefficient
    (original B hZ K hK L hL coefficient z hz)
    (model B hZ K hK L hL coefficient z hz).proper 9
    (model B hZ K hK L hL coefficient z hz).schemeCurve
    (model B hZ K hK L hL coefficient z hz).dimension

def rawModelIso : (rawProjection B hZ K hK).obj z ≅
    nativeFamily B hZ K hK L hL coefficient z hz :=
  (model B hZ K hK L hL coefficient z hz).recovery ≪≫
    modelFamilyIso B hZ K hK L hL coefficient z hz

theorem rawModelIso_base :
    (rawModelIso B hZ K hK L hL coefficient z hz).hom.baseMap =
      eqToHom (rawFamily_base B hZ K hK L hL coefficient z hz) :=
  NativeFieldSchemeModelEndpoints.recovery_comp_base B hZ
    (model B hZ K hK L hL coefficient z hz).recovery
    (modelFamilyIso B hZ K hK L hL coefficient z hz)
    (rawFamily_integerBase B hZ K hK L hL coefficient z hz)
    (integerFieldBase_eq B hZ K hK L hL coefficient).symm
    (model B hZ K hK L hL coefficient z hz).recovery_base
    (NativeFieldSchemeModelEndpoints.comparison_base B hZ K hK L hL coefficient
      (original B hZ K hK L hL coefficient z hz)
      (model B hZ K hK L hL coefficient z hz).proper 9
      (model B hZ K hK L hL coefficient z hz).schemeCurve
      (model B hZ K hK L hL coefficient z hz).dimension)

theorem rawModelIso_lift :
    (curvesProjectionOver B hZ).IsHomLift
      (𝟙 (integerFieldBase B hZ K hK L hL coefficient))
      (rawModelIso B hZ K hK L hL coefficient z hz).hom :=
  NativeFieldSchemeModelEndpoints.homLift_id_of_base B hZ
    (integerFieldBase B hZ K hK L hL coefficient)
    (rawModelIso B hZ K hK L hL coefficient z hz).hom
    (rawFamily_base B hZ K hK L hL coefficient z hz) rfl
    (rawModelIso_base B hZ K hK L hL coefficient z hz)

section ClassifierUnit
variable (g : ℕ) (hg : 2 ≤ g)
  (V : BigFppfOver B (Spec (.of K)) hK) {Z : BigFppfOver B integerBase hZ}
  (q : Z ⟶ (Over.map (NativeSmoothGenusCoarseClassifier.coefficientArrow B hZ K hK)).obj V)
  (hq : M9StandaloneDraft.SchemeCurve ((BigFppfOver.toScheme B integerBase hZ).map q) g)

/-- The actual identity index is compared inside its genuine slice. -/
def unitIndexIso :
    (Over.post (Over.map (NativeSmoothGenusCoarseClassifier.coefficientArrow B hZ K hK))).obj
        (Functor.FiberedMor.unit V) ≅
      Functor.FiberedMor.unit
        ((Over.map (NativeSmoothGenusCoarseClassifier.coefficientArrow B hZ K hK)).obj V) :=
  Over.isoMk (Iso.refl _) (by simp)

/-- Original family recovery at the actual chosen classifier's unit. -/
def classifierUnitFamilyIso :
    (NativeSmoothGenusCoarseClassifier.originalProjection B hZ K hK g hg).obj
      ((NativeSmoothGenusCoarseClassifier.classifyingMor B hZ K hK V q g hg hq).obj
        (Functor.FiberedMor.unit V)) ≅
    M9StacksIntegration.NativeSchematicCurveFamily.schemeCurveFamily B hZ q g hq :=
  NativeSmoothGenusCoarseRecovery.originalValueIso B hZ K hK g hg V
      (NativeSmoothGenusCurveClassifier.classifyingMor B hZ q g hq)
      (Functor.FiberedMor.unit V) ≪≫
    (show ObjectProperty (CurveFamily B hZ) from
      IsSmoothH0FamilyOfFibreGenus B hZ g).ι.mapIso
      ((NativeSmoothGenusCurveClassifier.classifyingMor B hZ q g hq).toFunctor.mapIso
        (unitIndexIso B hZ K hK V)) ≪≫
    (show ObjectProperty (CurveFamily B hZ) from
      IsSmoothH0FamilyOfFibreGenus B hZ g).ι.mapIso
      (NativeSmoothGenusCurveClassifier.classifiesOriginalFamily B hZ q g hq)

theorem classifierUnitFamilyIso_lift :
    (curvesProjectionOver B hZ).IsHomLift
      (𝟙 ((Over.map (NativeSmoothGenusCoarseClassifier.coefficientArrow B hZ K hK)).obj V))
      (classifierUnitFamilyIso B hZ K hK g hg V q hq).hom := by
  let F := NativeSmoothGenusCurveClassifier.classifyingMor B hZ q g hq
  let ι := (show ObjectProperty (CurveFamily B hZ) from
    IsSmoothH0FamilyOfFibreGenus B hZ g).ι
  let T := (Over.map (NativeSmoothGenusCoarseClassifier.coefficientArrow B hZ K hK)).obj V
  have h₁ : (curvesProjectionOver B hZ).IsHomLift (𝟙 T)
      (NativeSmoothGenusCoarseRecovery.originalValueIso B hZ K hK g hg V F
        (Functor.FiberedMor.unit V)).hom :=
    NativeSmoothGenusCoarseRecovery.originalValueIso_lift
      B hZ K hK g hg V F (Functor.FiberedMor.unit V)
  have hindex : (Over.forget T).IsHomLift (𝟙 T) (unitIndexIso B hZ K hK V).hom :=
    IsHomLift.of_fac' _ _ _ rfl rfl (by simp [unitIndexIso])
  have hw : (F.toFunctor ⋙ ι) ⋙ curvesProjectionOver B hZ = Over.forget T := F.w
  have h₂ : (curvesProjectionOver B hZ).IsHomLift (𝟙 T)
      (ι.map (F.toFunctor.map (unitIndexIso B hZ K hK V).hom)) :=
    Functor.isHomLift_map_of_comp_eq hw (𝟙 T) (unitIndexIso B hZ K hK V).hom
  have hgen : (moduliSmoothCurvesOfGenus B hZ g).val.p.IsHomLift (𝟙 T)
      (NativeSmoothGenusCurveClassifier.classifiesOriginalFamily B hZ q g hq).hom := by
    dsimp only [NativeSmoothGenusCurveClassifier.classifiesOriginalFamily]
    change (moduliSmoothCurvesOfGenus B hZ g).val.p.IsHomLift (𝟙 T)
      (Functor.Fiber.fiberInclusion.map _)
    infer_instance
  have h₃ : (curvesProjectionOver B hZ).IsHomLift (𝟙 T)
      (ι.map (NativeSmoothGenusCurveClassifier.classifiesOriginalFamily B hZ q g hq).hom) :=
    (Functor.isHomLift_comp_iff ι (curvesProjectionOver B hZ) _ _).mp hgen
  letI := h₂
  letI := h₃
  have : (curvesProjectionOver B hZ).IsHomLift (𝟙 T)
      (ι.map (F.toFunctor.map (unitIndexIso B hZ K hK V).hom) ≫
        ι.map (NativeSmoothGenusCurveClassifier.classifiesOriginalFamily B hZ q g hq).hom) :=
    IsHomLift.comp_lift_id_left _ _ _ _
  letI := h₁
  change (curvesProjectionOver B hZ).IsHomLift (𝟙 T)
    ((NativeSmoothGenusCoarseRecovery.originalValueIso B hZ K hK g hg V F
      (Functor.FiberedMor.unit V)).hom ≫
      ι.map (F.toFunctor.map (unitIndexIso B hZ K hK V).hom) ≫
      ι.map (NativeSmoothGenusCurveClassifier.classifiesOriginalFamily B hZ q g hq).hom)
  exact IsHomLift.comp_lift_id_left _ _ _ _
end ClassifierUnit

abbrev modelClassifier :=
  NativeSmoothGenusCoarseClassifier.classifyingMor B hZ K hK
    (fieldBase B K hK L hL coefficient)
    (nativeProjection B hZ K hK L hL coefficient z hz) 9 (by decide)
    (nativeProjection_schemeCurve B hZ K hK L hL coefficient z hz)

/-- The actual raw source object is identified with the actual model
classifier at its unit, retaining the original coefficient base. -/
def rawClassifierIso : (rawProjection B hZ K hK).obj z ≅
    (rawProjection B hZ K hK).obj
      ((modelClassifier B hZ K hK L hL coefficient z hz).obj
        (Functor.FiberedMor.unit (fieldBase B K hK L hL coefficient))) :=
  rawModelIso B hZ K hK L hL coefficient z hz ≪≫
    (classifierUnitFamilyIso B hZ K hK 9 (by decide)
      (fieldBase B K hK L hL coefficient)
      (nativeProjection B hZ K hK L hL coefficient z hz)
      (nativeProjection_schemeCurve B hZ K hK L hL coefficient z hz)).symm

theorem rawClassifierIso_lift :
    (curvesProjectionOver B hZ).IsHomLift
      (𝟙 (integerFieldBase B hZ K hK L hL coefficient))
      (rawClassifierIso B hZ K hK L hL coefficient z hz).hom :=
  NativeFieldSchemeModelEndpoints.recovery_comp_symm_lift B hZ
    (integerFieldBase B hZ K hK L hL coefficient)
    (rawModelIso B hZ K hK L hL coefficient z hz)
    (classifierUnitFamilyIso B hZ K hK 9 (by decide)
      (fieldBase B K hK L hL coefficient)
      (nativeProjection B hZ K hK L hL coefficient z hz)
      (nativeProjection_schemeCurve B hZ K hK L hL coefficient z hz))
    (rawModelIso_lift B hZ K hK L hL coefficient z hz)
    (classifierUnitFamilyIso_lift B hZ K hK 9 (by decide)
      (fieldBase B K hK L hL coefficient)
      (nativeProjection B hZ K hK L hL coefficient z hz)
      (nativeProjection_schemeCurve B hZ K hK L hL coefficient z hz))

end M9Native.NativeGenusNineFieldObjectCurve
end
