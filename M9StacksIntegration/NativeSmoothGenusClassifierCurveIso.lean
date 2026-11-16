module

public import M9StacksIntegration.NativeSmoothGenusCurveClassifier
public import M9StacksIntegration.NativeSchematicCurveIdentityIso
public import M9StacksIntegration.FiberedClassifierCartesianValue
public import StacksFrontier.CategoryTheory.FiberedCategory.HomLift

/-! A vertical arrow between the actual original genus-classifier values
gives an isomorphism of the SAME physical scheme pullbacks. The classifier
values are compared with the genuine pullbacks by their cartesian universal
property. Ordinary Scheme pullback retains arbitrary original test schemes
and all specified recovered parameter maps. -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

namespace M9Native.NativeSmoothGenusClassifierCurveIso

open M9StacksIntegration.NativeSchematicCurveFamily

universe u
variable (B : BigFppfSite.{u}) (hZ : B.Contains integerBase)

abbrev schemeFunctor := BigFppfOver.toScheme B integerBase hZ

section OneFamily
variable {Z U T : BigFppfOver B integerBase hZ} (q : Z ⟶ U) (g : ℕ)
  (hq : M9StandaloneDraft.SchemeCurve ((schemeFunctor B hZ).map q) g)
  (a : T ⟶ U)

abbrev pulledProjection : pullback q a ⟶ T := pullback.snd q a

/-- The actual native pullback represents the pullback of the SAME
original scheme morphisms. -/
theorem physicalPullback : IsPullback
    ((schemeFunctor B hZ).map (pullback.fst q a))
    ((schemeFunctor B hZ).map (pulledProjection B hZ q a))
    ((schemeFunctor B hZ).map q) ((schemeFunctor B hZ).map a) :=
  (IsPullback.of_hasPullback q a).map (schemeFunctor B hZ)

def physicalPullbackIso : (schemeFunctor B hZ).obj (pullback q a) ≅
    pullback ((schemeFunctor B hZ).map q) ((schemeFunctor B hZ).map a) :=
  (physicalPullback B hZ q a).isoPullback

theorem physicalPullbackIso_hom_snd :
    (physicalPullbackIso B hZ q a).hom ≫
        pullback.snd ((schemeFunctor B hZ).map q) ((schemeFunctor B hZ).map a) =
      (schemeFunctor B hZ).map (pulledProjection B hZ q a) :=
  (physicalPullback B hZ q a).isoPullback_hom_snd

include hq in
theorem pulled_proper :
    IsProper ((schemeFunctor B hZ).map (pulledProjection B hZ q a)) :=
  MorphismProperty.of_isPullback (P := @IsProper) (physicalPullback B hZ q a) hq.1

include hq in
theorem pulled_smooth :
    SmoothOfRelativeDimension 1 ((schemeFunctor B hZ).map (pulledProjection B hZ q a)) :=
  MorphismProperty.of_isPullback (P := @SmoothOfRelativeDimension 1)
    (physicalPullback B hZ q a) hq.2.1

def pulledFamily : CurveFamily B hZ :=
  properSmoothSchemeFamily B hZ (pulledProjection B hZ q a)
    (pulled_proper B hZ q g hq a) (pulled_smooth B hZ q g hq a)

def pulledToOriginal : pulledFamily B hZ q g hq a ⟶
    schemeCurveFamily B hZ q g hq :=
  NativeSchematicCurveCartesianArrow.arrow B hZ q (pulledProjection B hZ q a) a
    (pullback.fst q a) hq.1 hq.2.1
    (pulled_proper B hZ q g hq a) (pulled_smooth B hZ q g hq a)
    (physicalPullback B hZ q a)

def pulledModuliObject : (moduliSmoothCurvesOfGenus B hZ g).val.obj :=
  ⟨pulledFamily B hZ q g hq a,
    CurveFamily.isSmoothH0FamilyOfFibreGenus_of_hom
      (pulledToOriginal B hZ q g hq a)
      (NativeSmoothGenusCurveClassifier.schemeCurveFamily_membership B hZ q g hq)⟩

def pulledModuliToOriginal : pulledModuliObject B hZ q g hq a ⟶
    NativeSmoothGenusCurveClassifier.moduliObject B hZ q g hq :=
  ObjectProperty.homMk (pulledToOriginal B hZ q g hq a)

def moduliValueIso :
    (NativeSmoothGenusCurveClassifier.classifyingMor B hZ q g hq).toFunctor.obj
        (Over.mk a) ≅ pulledModuliObject B hZ q g hq a := by
  let : (moduliSmoothCurvesOfGenus B hZ g).val.p.IsFibered :=
    (moduliSmoothCurvesOfGenus B hZ g).property.isFibered
  have : (moduliSmoothCurvesOfGenus B hZ g).val.p.IsHomLift (Over.mk a).hom
      (pulledModuliToOriginal B hZ q g hq a) :=
    IsHomLift.map _ (pulledModuliToOriginal B hZ q g hq a)
  have : (moduliSmoothCurvesOfGenus B hZ g).val.p.IsStronglyCartesian (Over.mk a).hom
      (pulledModuliToOriginal B hZ q g hq a) :=
    (moduliSmoothCurvesOfGenus B hZ g).property.isStronglyCartesian_homLift _ _
  exact FiberedClassifierCartesianValue.valueIso
    (moduliSmoothCurvesOfGenus B hZ g).val.p U
    (show (moduliSmoothCurvesOfGenus B hZ g).val.p.obj
      (NativeSmoothGenusCurveClassifier.moduliObject B hZ q g hq) = U from rfl)
    (Over.mk a) (pulledModuliToOriginal B hZ q g hq a)

/-- The actual classifier value recovers the actual schematic pullback. -/
def valueIso :
    ((NativeSmoothGenusCurveClassifier.classifyingMor B hZ q g hq).toFunctor.obj
        (Over.mk a)).obj ≅ pulledFamily B hZ q g hq a :=
  (show ObjectProperty (CurveFamily B hZ) from IsSmoothH0FamilyOfFibreGenus B hZ g).ι.mapIso
    (moduliValueIso B hZ q g hq a)

theorem valueIso_hom_lift :
    (curvesProjectionOver B hZ).IsHomLift (𝟙 T) (valueIso B hZ q g hq a).hom := by
  let : (moduliSmoothCurvesOfGenus B hZ g).val.p.IsFibered :=
    (moduliSmoothCurvesOfGenus B hZ g).property.isFibered
  have : (moduliSmoothCurvesOfGenus B hZ g).val.p.IsHomLift (Over.mk a).hom
      (pulledModuliToOriginal B hZ q g hq a) :=
    IsHomLift.map _ (pulledModuliToOriginal B hZ q g hq a)
  have : (moduliSmoothCurvesOfGenus B hZ g).val.p.IsStronglyCartesian (Over.mk a).hom
      (pulledModuliToOriginal B hZ q g hq a) :=
    (moduliSmoothCurvesOfGenus B hZ g).property.isStronglyCartesian_homLift _ _
  have h := FiberedClassifierCartesianValue.valueIso_hom_lift
    (moduliSmoothCurvesOfGenus B hZ g).val.p U
    (show (moduliSmoothCurvesOfGenus B hZ g).val.p.obj
      (NativeSmoothGenusCurveClassifier.moduliObject B hZ q g hq) = U from rfl)
    (Over.mk a) (pulledModuliToOriginal B hZ q g hq a)
  change ((show ObjectProperty (CurveFamily B hZ) from
      IsSmoothH0FamilyOfFibreGenus B hZ g).ι ⋙ curvesProjectionOver B hZ).IsHomLift
    (𝟙 T) (moduliValueIso B hZ q g hq a).hom at h
  exact (Functor.isHomLift_comp_iff
    (show ObjectProperty (CurveFamily B hZ) from
      IsSmoothH0FamilyOfFibreGenus B hZ g).ι
    (curvesProjectionOver B hZ) (𝟙 T) (moduliValueIso B hZ q g hq a).hom).mp h
end OneFamily

variable {Z₀ U₀ Z₁ U₁ T : BigFppfOver B integerBase hZ}
  (q₀ : Z₀ ⟶ U₀) (q₁ : Z₁ ⟶ U₁) (g : ℕ)
  (hq₀ : M9StandaloneDraft.SchemeCurve ((schemeFunctor B hZ).map q₀) g)
  (hq₁ : M9StandaloneDraft.SchemeCurve ((schemeFunctor B hZ).map q₁) g)
  (a₀ : T ⟶ U₀) (a₁ : T ⟶ U₁)
  (α : ((NativeSmoothGenusCurveClassifier.classifyingMor B hZ q₀ g hq₀).toFunctor.obj
      (Over.mk a₀)).obj ⟶
    ((NativeSmoothGenusCurveClassifier.classifyingMor B hZ q₁ g hq₁).toFunctor.obj
      (Over.mk a₁)).obj)
  (hα : (curvesProjectionOver B hZ).IsHomLift (𝟙 T) α)

def pulledArrow : pulledFamily B hZ q₀ g hq₀ a₀ ⟶ pulledFamily B hZ q₁ g hq₁ a₁ :=
  (valueIso B hZ q₀ g hq₀ a₀).inv ≫ α ≫ (valueIso B hZ q₁ g hq₁ a₁).hom

include hα in
theorem pulledArrow_base :
    (pulledArrow B hZ q₀ q₁ g hq₀ hq₁ a₀ a₁ α).baseMap = 𝟙 T := by
  have := hα
  have := valueIso_hom_lift B hZ q₀ g hq₀ a₀
  have := valueIso_hom_lift B hZ q₁ g hq₁ a₁
  have : (curvesProjectionOver B hZ).IsHomLift (𝟙 T)
      (valueIso B hZ q₀ g hq₀ a₀).inv := inferInstance
  have : (curvesProjectionOver B hZ).IsHomLift (𝟙 T)
      (α ≫ (valueIso B hZ q₁ g hq₁ a₁).hom) :=
    IsHomLift.comp_lift_id_left _ (𝟙 T) _ _
  have : (curvesProjectionOver B hZ).IsHomLift (𝟙 T)
      (pulledArrow B hZ q₀ q₁ g hq₀ hq₁ a₀ a₁ α) :=
    IsHomLift.comp_lift_id_left _ (𝟙 T) _ _
  change (curvesProjectionOver B hZ).map
    (pulledArrow B hZ q₀ q₁ g hq₀ hq₁ a₀ a₁ α) = 𝟙 T
  exact (IsHomLift.eq_of_isHomLift
    (a := pulledFamily B hZ q₀ g hq₀ a₀) (b := pulledFamily B hZ q₁ g hq₁ a₁)
    (curvesProjectionOver B hZ) (𝟙 T)
    (pulledArrow B hZ q₀ q₁ g hq₀ hq₁ a₀ a₁ α)).symm

/-- The vertical original-family arrow yields an actual physical Iso. -/
def physicalIso :
    pullback ((schemeFunctor B hZ).map q₀) ((schemeFunctor B hZ).map a₀) ≅
      pullback ((schemeFunctor B hZ).map q₁) ((schemeFunctor B hZ).map a₁) :=
  (physicalPullbackIso B hZ q₀ a₀).symm ≪≫
    NativeSchematicCurveIdentityIso.physicalIso B hZ
      (pulledProjection B hZ q₀ a₀) (pulledProjection B hZ q₁ a₁)
      (pulled_proper B hZ q₀ g hq₀ a₀) (pulled_smooth B hZ q₀ g hq₀ a₀)
      (pulled_proper B hZ q₁ g hq₁ a₁) (pulled_smooth B hZ q₁ g hq₁ a₁)
      (pulledArrow B hZ q₀ q₁ g hq₀ hq₁ a₀ a₁ α)
      (pulledArrow_base B hZ q₀ q₁ g hq₀ hq₁ a₀ a₁ α hα) ≪≫
    physicalPullbackIso B hZ q₁ a₁

theorem physicalIso_hom_snd :
    (physicalIso B hZ q₀ q₁ g hq₀ hq₁ a₀ a₁ α hα).hom ≫
        pullback.snd ((schemeFunctor B hZ).map q₁) ((schemeFunctor B hZ).map a₁) =
      pullback.snd ((schemeFunctor B hZ).map q₀) ((schemeFunctor B hZ).map a₀) := by
  have h₀ : (physicalPullbackIso B hZ q₀ a₀).inv ≫
      (schemeFunctor B hZ).map (pulledProjection B hZ q₀ a₀) =
        pullback.snd ((schemeFunctor B hZ).map q₀) ((schemeFunctor B hZ).map a₀) := by
    rw [Iso.inv_comp_eq, physicalPullbackIso_hom_snd]
  simp only [physicalIso, Iso.trans_hom, Iso.symm_hom, Category.assoc,
    physicalPullbackIso_hom_snd,
    NativeSchematicCurveIdentityIso.physicalIso_hom_snd, h₀]

variable {W : Scheme.{u}} (w : W ⟶ (schemeFunctor B hZ).obj T)

/-- Pull back over ANY original scheme, without site containment. -/
def baseChangeIso :
    pullback ((schemeFunctor B hZ).map q₀) (w ≫ (schemeFunctor B hZ).map a₀) ≅
      pullback ((schemeFunctor B hZ).map q₁) (w ≫ (schemeFunctor B hZ).map a₁) :=
  (pullbackLeftPullbackSndIso ((schemeFunctor B hZ).map q₀)
    ((schemeFunctor B hZ).map a₀) w).symm ≪≫
    PhysicalCurveIsoPullback.baseChangeIso
      (pullback.snd ((schemeFunctor B hZ).map q₀) ((schemeFunctor B hZ).map a₀))
      (pullback.snd ((schemeFunctor B hZ).map q₁) ((schemeFunctor B hZ).map a₁))
      (physicalIso B hZ q₀ q₁ g hq₀ hq₁ a₀ a₁ α hα)
      (physicalIso_hom_snd B hZ q₀ q₁ g hq₀ hq₁ a₀ a₁ α hα) w ≪≫
    pullbackLeftPullbackSndIso ((schemeFunctor B hZ).map q₁)
      ((schemeFunctor B hZ).map a₁) w

theorem baseChangeIso_hom_snd :
    (baseChangeIso B hZ q₀ q₁ g hq₀ hq₁ a₀ a₁ α hα w).hom ≫
        pullback.snd ((schemeFunctor B hZ).map q₁) (w ≫ (schemeFunctor B hZ).map a₁) =
      pullback.snd ((schemeFunctor B hZ).map q₀) (w ≫ (schemeFunctor B hZ).map a₀) := by
  simp only [baseChangeIso, Iso.trans_hom, Iso.symm_hom, Category.assoc,
    pullbackLeftPullbackSndIso_hom_snd, PhysicalCurveIsoPullback.baseChangeIso_hom_snd,
    pullbackLeftPullbackSndIso_inv_snd_snd]

/-- Both specified original parameter maps are recovered along the SAME w. -/
def originalIso
    (x : W ⟶ (schemeFunctor B hZ).obj U₀) (y : W ⟶ (schemeFunctor B hZ).obj U₁)
    (hx : w ≫ (schemeFunctor B hZ).map a₀ = x)
    (hy : w ≫ (schemeFunctor B hZ).map a₁ = y) :
    pullback ((schemeFunctor B hZ).map q₀) x ≅
      pullback ((schemeFunctor B hZ).map q₁) y := by
  subst x
  subst y
  exact baseChangeIso B hZ q₀ q₁ g hq₀ hq₁ a₀ a₁ α hα w

theorem originalIso_hom_snd
    (x : W ⟶ (schemeFunctor B hZ).obj U₀) (y : W ⟶ (schemeFunctor B hZ).obj U₁)
    (hx : w ≫ (schemeFunctor B hZ).map a₀ = x)
    (hy : w ≫ (schemeFunctor B hZ).map a₁ = y) :
    (originalIso B hZ q₀ q₁ g hq₀ hq₁ a₀ a₁ α hα w x y hx hy).hom ≫
        pullback.snd ((schemeFunctor B hZ).map q₁) y =
      pullback.snd ((schemeFunctor B hZ).map q₀) x := by
  subst x
  subst y
  exact baseChangeIso_hom_snd B hZ q₀ q₁ g hq₀ hq₁ a₀ a₁ α hα w

end M9Native.NativeSmoothGenusClassifierCurveIso
