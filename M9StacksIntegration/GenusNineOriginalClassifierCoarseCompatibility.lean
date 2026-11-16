module

public import M9StacksIntegration.GenusNineOriginalClassifierNativeRestriction
public import M9StacksIntegration.BoundedOriginalFamilyCoarseRecovery
public import M9StacksIntegration.NativeSmoothGenusSourceFullness

/-! Agreement on all original families over bounded bases forces the restriction
of the original classifier to equal the actual chosen coarse functor. The
comparison is recovered on every native source object through the genuine
original-family recovery arrows and chosen-source fullness. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Opposite
open CategoryTheory.PresheafOfCategories
attribute [local implicit_reducible] CategoryTheory.BasedCategory.ofFunctor

namespace M9Native.GenusNineOriginalClassifierCoarseCompatibility

open M9StacksIntegration M9StacksIntegration.AllTestBoundedCharts
  M9StacksIntegration.AllTestNativeCurveFamily
  M9StacksIntegration.AllTestNativeOriginalFunctor
  M9StacksIntegration.AllTestBoundedOriginalRecovery

universe u
variable (B : BigFppfSite.{u}) (hZ : B.Contains integerBase)
  (K : Type u) [Field K] (hK : B.Contains (Spec (.of K)))
  (g : ℕ) (hg : 2 ≤ g)

/-- Forward conversion of the actual recovered original family returns an
object with the same raw family as the original chosen-source object. -/
def rawRecoveryIso
    (x : (GenusNineCoarseOverField.smoothStack B hZ K hK g hg).val.val.obj) :
    (NativeSmoothGenusCoarseClassifier.originalProjection B hZ K hK g hg).obj
      (BoundedOriginalFamilyCoarseValue.sourceObject B hZ K hK g hg
        ((GenusNineOriginalFamilyFunctor.toOriginal B hZ K hK g hg).obj x).family) ≅
      (NativeSmoothGenusCoarseClassifier.originalProjection B hZ K hK g hg).obj x :=
  BoundedOriginalFamilyCoarseRecovery.sourceObject_originalIso B hZ K hK g hg
    ((GenusNineOriginalFamilyFunctor.toOriginal B hZ K hK g hg).obj x).family ≪≫
      GenusNineOriginalFamilyFunctor.recoveryIso B hZ K hK g hg x

/-- The complete raw recovery arrow lies over the identity of the actual base. -/
theorem rawRecoveryIso_lift
    (x : (GenusNineCoarseOverField.smoothStack B hZ K hK g hg).val.val.obj) :
    (curvesProjectionOver B hZ).IsHomLift
      (𝟙 ((Over.map (NativeSmoothGenusCoarseClassifier.coefficientArrow B hZ K hK)).obj
        ((GenusNineOriginalFamilyFunctor.baseProjection B hZ K hK g hg).obj x)))
      (rawRecoveryIso B hZ K hK g hg x).hom := by
  rw [GenusNineOriginalFamilyFunctor.coefficientArrow_eq_fieldToInteger B hZ K hK]
  refine IsHomLift.of_fac' (curvesProjectionOver B hZ)
    (𝟙 (nativeBase B hZ K hK
      ((GenusNineOriginalFamilyFunctor.baseProjection B hZ K hK g hg).obj x)))
    (rawRecoveryIso B hZ K hK g hg x).hom
    (BoundedOriginalFamilyCoarseRecovery.sourceObject_original_base B hZ K hK g hg
      ((GenusNineOriginalFamilyFunctor.toOriginal B hZ K hK g hg).obj x).family)
    (Functor.congr_obj (GenusNineOriginalFamilyFunctor.structuralSquare B hZ K hK g hg) x) ?_
  change
    (BoundedOriginalFamilyCoarseRecovery.sourceObject_originalIso B hZ K hK g hg
        ((GenusNineOriginalFamilyFunctor.toOriginal B hZ K hK g hg).obj x).family).hom.baseMap ≫
      (GenusNineOriginalFamilyFunctor.recoveryIso B hZ K hK g hg x).hom.baseMap = _
  rw [BoundedOriginalFamilyCoarseRecovery.sourceObject_originalIso_baseMap,
    GenusNineOriginalFamilyFunctor.recoveryIso_baseMap]
  simp only [Category.id_comp, eqToHom_trans]

/-- Chosen-source fullness lifts the genuine raw recovery arrow over the
identity of the same native base, with no chosen-source comparison premise. -/
def sourceRecoveryArrow
    (x : (GenusNineCoarseOverField.smoothStack B hZ K hK g hg).val.val.obj) :
    BoundedOriginalFamilyCoarseValue.sourceObject B hZ K hK g hg
        ((GenusNineOriginalFamilyFunctor.toOriginal B hZ K hK g hg).obj x).family ⟶ x :=
  NativeSmoothGenusSourceFullness.liftRawArrow B hZ g hg K hK
    ((GenusNineOriginalFamilyFunctor.baseProjection B hZ K hK g hg).obj x)
    (x := BoundedOriginalFamilyCoarseValue.sourceObject B hZ K hK g hg
      ((GenusNineOriginalFamilyFunctor.toOriginal B hZ K hK g hg).obj x).family)
    (y := x)
    rfl rfl (rawRecoveryIso B hZ K hK g hg x).hom
    (rawRecoveryIso_lift B hZ K hK g hg x)

theorem sourceRecoveryArrow_lift
    (x : (GenusNineCoarseOverField.smoothStack B hZ K hK g hg).val.val.obj) :
    (GenusNineOriginalFamilyFunctor.baseProjection B hZ K hK g hg).IsHomLift
      (𝟙 ((GenusNineOriginalFamilyFunctor.baseProjection B hZ K hK g hg).obj x))
      (sourceRecoveryArrow B hZ K hK g hg x) :=
  NativeSmoothGenusSourceFullness.liftRawArrow_isHomLift B hZ g hg K hK
    ((GenusNineOriginalFamilyFunctor.baseProjection B hZ K hK g hg).obj x)
    (x := BoundedOriginalFamilyCoarseValue.sourceObject B hZ K hK g hg
      ((GenusNineOriginalFamilyFunctor.toOriginal B hZ K hK g hg).obj x).family)
    (y := x)
    rfl rfl (rawRecoveryIso B hZ K hK g hg x).hom
    (rawRecoveryIso_lift B hZ K hK g hg x)

/-- The forward family's native coarse value is the literal named value of
the actual chosen coarse functor at every original native source object. -/
theorem nativeValue_recovery
    (x : (GenusNineCoarseOverField.smoothStack B hZ K hK g hg).val.val.obj) :
    BoundedOriginalFamilyCoarseValue.nativeValue B hZ K hK g hg
        ((GenusNineOriginalFamilyFunctor.toOriginal B hZ K hK g hg).obj x).family =
      sectionOfBasedFunctor
        (ASClassifierGeometricLift.coarseFunctor B (Spec (.of K)) hK
          (GenusNineCoarseOverField.coarseMap B hZ K hK g hg)).toFunctor
        (ASClassifierGeometricLift.coarseFunctor B (Spec (.of K)) hK
          (GenusNineCoarseOverField.coarseMap B hZ K hK g hg)).w x := by
  let κ := ASClassifierGeometricLift.coarseFunctor B (Spec (.of K)) hK
    (GenusNineCoarseOverField.coarseMap B hZ K hK g hg)
  let a := sourceRecoveryArrow B hZ K hK g hg x
  have : (BasedCategory.ofFunctor
      (GenusNineCoarseOverField.smoothStack B hZ K hK g hg).val.val.p).p.IsHomLift
      (𝟙 ((GenusNineOriginalFamilyFunctor.baseProjection B hZ K hK g hg).obj x)) a :=
    sourceRecoveryArrow_lift B hZ K hK g hg x
  have hκ := Functor.isHomLift_map_of_comp_eq κ.w
    (𝟙 ((GenusNineOriginalFamilyFunctor.baseProjection B hZ K hK g hg).obj x)) a
  have h := elementOf_eq_map
    (P := (GenusNineCoarseOverField.coarseSpace B hZ K hK g hg).obj)
    (Functor.congr_obj κ.w
      (BoundedOriginalFamilyCoarseValue.sourceObject B hZ K hK g hg
        ((GenusNineOriginalFamilyFunctor.toOriginal B hZ K hK g hg).obj x).family))
    (Functor.congr_obj κ.w x)
    (𝟙 ((GenusNineOriginalFamilyFunctor.baseProjection B hZ K hK g hg).obj x))
    (κ.map a) hκ
  change _ = (GenusNineCoarseOverField.coarseSpace B hZ K hK g hg).obj.map
    (𝟙 (op ((GenusNineOriginalFamilyFunctor.baseProjection B hZ K hK g hg).obj x))) _ at h
  rw [Functor.map_id_apply] at h
  exact h

variable
  (c : M9StandaloneDraft.Classifier K g
    ((originalPresheafFunctor K B hK).obj
      (GenusNineCoarseOverField.coarseSpace B hZ K hK g hg)))
  (hB : ∀ (T : BigFppfOver B (Spec (.of K)) hK)
    (F : M9StandaloneDraft.Family K ((boundedInclusion B K hK).obj T) g),
    c.value ((boundedInclusion B K hK).obj T) F =
      BoundedOriginalFamilyCoarseValue.originalValue B hZ K hK g hg F)

include hB in
/-- Bounded-base agreement on ALL original families determines the named
value at every actual chosen-source object. -/
theorem classifier_namedValue_eq
    (x : (GenusNineCoarseOverField.smoothStack B hZ K hK g hg).val.val.obj) :
    sectionOfBasedFunctor
        (GenusNineOriginalClassifierNativeRestriction.classifier B hZ K hK g hg
          (GenusNineCoarseOverField.coarseSpace B hZ K hK g hg) c).toFunctor
        (GenusNineOriginalClassifierNativeRestriction.classifier B hZ K hK g hg
          (GenusNineCoarseOverField.coarseSpace B hZ K hK g hg) c).w x =
      sectionOfBasedFunctor
        (ASClassifierGeometricLift.coarseFunctor B (Spec (.of K)) hK
          (GenusNineCoarseOverField.coarseMap B hZ K hK g hg)).toFunctor
        (ASClassifierGeometricLift.coarseFunctor B (Spec (.of K)) hK
          (GenusNineCoarseOverField.coarseMap B hZ K hK g hg)).w x := by
  rw [GenusNineOriginalClassifierNativeRestriction.classifier_namedValue,
    GenusNineOriginalClassifierNativeRestriction.nativeValue_eq]
  change
    (originalNativeRestrictionSmallIso K B hK
      (GenusNineCoarseOverField.coarseSpace B hZ K hK g hg).obj
      (GenusNineCoarseOverField.coarseSpace B hZ K hK g hg).property).hom.app _
        (c.value _ ((GenusNineOriginalFamilyFunctor.toOriginal B hZ K hK g hg).obj x).family) = _
  rw [hB ((GenusNineOriginalFamilyFunctor.baseProjection B hZ K hK g hg).obj x)]
  exact (ConcreteCategory.congr_hom (NatTrans.congr_app
    (originalNativeRestrictionSmallIso K B hK
      (GenusNineCoarseOverField.coarseSpace B hZ K hK g hg).obj
      (GenusNineCoarseOverField.coarseSpace B hZ K hK g hg).property).inv_hom_id
    (op ((GenusNineOriginalFamilyFunctor.baseProjection B hZ K hK g hg).obj x)))
    (BoundedOriginalFamilyCoarseValue.nativeValue B hZ K hK g hg
      ((GenusNineOriginalFamilyFunctor.toOriginal B hZ K hK g hg).obj x).family)).trans
      (nativeValue_recovery B hZ K hK g hg x)

include hB in
/-- The original classifier restriction is the actual chosen coarse functor. -/
theorem classifier_eq :
    GenusNineOriginalClassifierNativeRestriction.classifier B hZ K hK g hg
        (GenusNineCoarseOverField.coarseSpace B hZ K hK g hg) c =
      ASClassifierGeometricLift.coarseFunctor B (Spec (.of K)) hK
        (GenusNineCoarseOverField.coarseMap B hZ K hK g hg) :=
  BasedCategory.BasedFunctor.ext' (eq_of_sections_eq _ _ _ _
    (classifier_namedValue_eq B hZ K hK g hg c hB))

/-- The required vertical based natural isomorphism is derived, rather than
assumed as compatibility of the full original classifier. -/
def comparisonIso :
    GenusNineOriginalClassifierNativeRestriction.classifier B hZ K hK g hg
        (GenusNineCoarseOverField.coarseSpace B hZ K hK g hg) c ≅
      ASClassifierGeometricLift.coarseFunctor B (Spec (.of K)) hK
        (GenusNineCoarseOverField.coarseMap B hZ K hK g hg) :=
  eqToIso (classifier_eq B hZ K hK g hg c hB)

/-- Every component preserves the actual native base by the identity. -/
theorem comparison_hom_isHomLift
    (x : (GenusNineCoarseOverField.smoothStack B hZ K hK g hg).val.val.obj) :
    (discreteProjection (GenusNineCoarseOverField.coarseSpace B hZ K hK g hg).obj).IsHomLift
      (𝟙 ((GenusNineOriginalFamilyFunctor.baseProjection B hZ K hK g hg).obj x))
      ((comparisonIso B hZ K hK g hg c hB).hom.toNatTrans.app x) :=
  (comparisonIso B hZ K hK g hg c hB).hom.isHomLift' x

end M9Native.GenusNineOriginalClassifierCoarseCompatibility
