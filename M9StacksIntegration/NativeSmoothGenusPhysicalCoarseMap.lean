module

public import M9StacksIntegration.NativeSmoothGenusPhysicalIsoArrow
public import M9StacksIntegration.NativeSmoothGenusCoarseRecovery
public import M9StacksIntegration.NativeSmoothGenusSourceFullness
public import M9StacksIntegration.SliceClassifierUnitIndexIso
public import M9StacksIntegration.AllOriginalCoarseClassifierFibre

/-! Physical isomorphisms of the original schematic fibres identify the
actual chosen coarse maps. The true slice-index isomorphism, original
hom-shrink recovery and raw-source fullness construct the chosen unit
arrow. No classifier natural Iso, coarse equality, or compatibility
premise is supplied. -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
attribute [local implicit_reducible] CategoryTheory.BasedCategory.ofFunctor
universe u

namespace M9Native.NativeSmoothGenusPhysicalCoarseMap

variable (B : BigFppfSite.{u}) (hZ : B.Contains integerBase)
  (K : Type u) [Field K] (hK : B.Contains (Spec (.of K)))
  (g : ℕ) (hg : 2 ≤ g)

abbrev relocalize :=
  Over.map (NativeSmoothGenusCoarseClassifier.coefficientArrow B hZ K hK)

section OneFamily
variable (U : BigFppfOver B (Spec (.of K)) hK)
  {Z : BigFppfOver B integerBase hZ}
  (q : Z ⟶ (relocalize B hZ K hK).obj U)
  (hq : M9StandaloneDraft.SchemeCurve
    ((NativeSmoothGenusClassifierCurveIso.schemeFunctor B hZ).map q) g)
  {T : BigFppfOver B (Spec (.of K)) hK} (a : T ⟶ U)

/-- Original recovery at the actual precomposed unit, with the literal
original parameter arrow in the endpoint. -/
def rawUnitIso :
    (NativeSmoothGenusCoarseClassifier.originalProjection B hZ K hK g hg).obj
      ((BasedFunctor.comp (PresheafValuedClassifierReflection.sliceMap a)
        (NativeSmoothGenusCoarseClassifier.classifyingMor B hZ K hK U q g hg hq)).obj
          (Functor.FiberedMor.unit T)) ≅
    ((NativeSmoothGenusCurveClassifier.classifyingMor B hZ q g hq).toFunctor.obj
      (Over.mk ((relocalize B hZ K hK).map a))).obj :=
  (NativeSmoothGenusCoarseClassifier.originalProjection B hZ K hK g hg).mapIso
    (SliceClassifierUnitIndexIso.valueIso
      (NativeSmoothGenusCoarseClassifier.classifyingMor B hZ K hK U q g hg hq) a) ≪≫
    NativeSmoothGenusCoarseRecovery.originalValueIso B hZ K hK g hg U
      (NativeSmoothGenusCurveClassifier.classifyingMor B hZ q g hq) (Over.mk a)

/-- The recovery retains the identity of the original coefficient base. -/
theorem rawUnitIso_hom_lift :
    (curvesProjectionOver B hZ).IsHomLift (𝟙 ((relocalize B hZ K hK).obj T))
      (rawUnitIso B hZ K hK g hg U q hq a).hom := by
  have hi := SliceClassifierUnitIndexIso.valueIso_hom_lift
    (NativeSmoothGenusCoarseClassifier.classifyingMor B hZ K hK U q g hg hq) a
  have hp := NativeSmoothGenusCoarseClassifier.original_isHomLift_id B hZ K hK g hg T
    (SliceClassifierUnitIndexIso.valueIso
      (NativeSmoothGenusCoarseClassifier.classifyingMor B hZ K hK U q g hg hq) a).hom hi
  have hr : (curvesProjectionOver B hZ).IsHomLift (𝟙 ((relocalize B hZ K hK).obj T))
      (NativeSmoothGenusCoarseRecovery.originalValueIso B hZ K hK g hg U
        (NativeSmoothGenusCurveClassifier.classifyingMor B hZ q g hq) (Over.mk a)).hom :=
    NativeSmoothGenusCoarseRecovery.originalValueIso_lift B hZ K hK g hg U
      (NativeSmoothGenusCurveClassifier.classifyingMor B hZ q g hq) (Over.mk a)
  letI := hr
  change (curvesProjectionOver B hZ).IsHomLift (𝟙 ((relocalize B hZ K hK).obj T))
    ((NativeSmoothGenusCoarseClassifier.originalProjection B hZ K hK g hg).map
      (SliceClassifierUnitIndexIso.valueIso
        (NativeSmoothGenusCoarseClassifier.classifyingMor B hZ K hK U q g hg hq) a).hom ≫
      (NativeSmoothGenusCoarseRecovery.originalValueIso B hZ K hK g hg U
        (NativeSmoothGenusCurveClassifier.classifyingMor B hZ q g hq) (Over.mk a)).hom)
  exact IsHomLift.comp_lift_id_left _ (𝟙 ((relocalize B hZ K hK).obj T)) _ _
end OneFamily

variable {U₀ U₁ T : BigFppfOver B (Spec (.of K)) hK}
  {Z₀ Z₁ : BigFppfOver B integerBase hZ}
  (q₀ : Z₀ ⟶ (relocalize B hZ K hK).obj U₀)
  (q₁ : Z₁ ⟶ (relocalize B hZ K hK).obj U₁)
  (hq₀ : M9StandaloneDraft.SchemeCurve
    ((NativeSmoothGenusClassifierCurveIso.schemeFunctor B hZ).map q₀) g)
  (hq₁ : M9StandaloneDraft.SchemeCurve
    ((NativeSmoothGenusClassifierCurveIso.schemeFunctor B hZ).map q₁) g)
  (a₀ : T ⟶ U₀) (a₁ : T ⟶ U₁)
  (e : pullback ((NativeSmoothGenusClassifierCurveIso.schemeFunctor B hZ).map q₀)
      ((NativeSmoothGenusClassifierCurveIso.schemeFunctor B hZ).map
        ((relocalize B hZ K hK).map a₀)) ≅
    pullback ((NativeSmoothGenusClassifierCurveIso.schemeFunctor B hZ).map q₁)
      ((NativeSmoothGenusClassifierCurveIso.schemeFunctor B hZ).map
        ((relocalize B hZ K hK).map a₁)))
  (he : e.hom ≫ pullback.snd
      ((NativeSmoothGenusClassifierCurveIso.schemeFunctor B hZ).map q₁)
      ((NativeSmoothGenusClassifierCurveIso.schemeFunctor B hZ).map
        ((relocalize B hZ K hK).map a₁)) =
    pullback.snd ((NativeSmoothGenusClassifierCurveIso.schemeFunctor B hZ).map q₀)
      ((NativeSmoothGenusClassifierCurveIso.schemeFunctor B hZ).map
        ((relocalize B hZ K hK).map a₀)))

/-- The actual raw chosen-unit arrow is constructed from physical geometry. -/
def rawUnitArrow :
    (NativeSmoothGenusCoarseClassifier.originalProjection B hZ K hK g hg).obj
      ((BasedFunctor.comp (PresheafValuedClassifierReflection.sliceMap a₀)
        (NativeSmoothGenusCoarseClassifier.classifyingMor B hZ K hK U₀ q₀ g hg hq₀)).obj
          (Functor.FiberedMor.unit T)) ⟶
    (NativeSmoothGenusCoarseClassifier.originalProjection B hZ K hK g hg).obj
      ((BasedFunctor.comp (PresheafValuedClassifierReflection.sliceMap a₁)
        (NativeSmoothGenusCoarseClassifier.classifyingMor B hZ K hK U₁ q₁ g hg hq₁)).obj
          (Functor.FiberedMor.unit T)) :=
  (rawUnitIso B hZ K hK g hg U₀ q₀ hq₀ a₀).hom ≫
    NativeSmoothGenusPhysicalIsoArrow.classifierArrow B hZ q₀ q₁
      ((relocalize B hZ K hK).map a₀) ((relocalize B hZ K hK).map a₁) e he g hq₀ hq₁ ≫
      (rawUnitIso B hZ K hK g hg U₁ q₁ hq₁ a₁).inv

theorem rawUnitArrow_lift :
    (curvesProjectionOver B hZ).IsHomLift (𝟙 ((relocalize B hZ K hK).obj T))
      (rawUnitArrow B hZ K hK g hg q₀ q₁ hq₀ hq₁ a₀ a₁ e he) := by
  have := rawUnitIso_hom_lift B hZ K hK g hg U₀ q₀ hq₀ a₀
  have := rawUnitIso_hom_lift B hZ K hK g hg U₁ q₁ hq₁ a₁
  have := NativeSmoothGenusPhysicalIsoArrow.classifierArrow_lift B hZ q₀ q₁
    ((relocalize B hZ K hK).map a₀) ((relocalize B hZ K hK).map a₁) e he g hq₀ hq₁
  have : (curvesProjectionOver B hZ).IsHomLift (𝟙 ((relocalize B hZ K hK).obj T))
      (rawUnitIso B hZ K hK g hg U₁ q₁ hq₁ a₁).inv := inferInstance
  have : (curvesProjectionOver B hZ).IsHomLift (𝟙 ((relocalize B hZ K hK).obj T))
      (NativeSmoothGenusPhysicalIsoArrow.classifierArrow B hZ q₀ q₁
        ((relocalize B hZ K hK).map a₀) ((relocalize B hZ K hK).map a₁) e he g hq₀ hq₁ ≫
        (rawUnitIso B hZ K hK g hg U₁ q₁ hq₁ a₁).inv) :=
    IsHomLift.comp_lift_id_left _ (𝟙 ((relocalize B hZ K hK).obj T)) _ _
  exact IsHomLift.comp_lift_id_left _ (𝟙 ((relocalize B hZ K hK).obj T)) _ _

include e he in
/-- The literal chosen coarse maps of physically isomorphic original
fibres are equal on the SAME native test base. No coarse equality is input. -/
theorem classifyingMaps_eq_of_physicalIso :
    schemeSpaceMap a₀ ≫ ASClassifierGeometricLift.nativeMap B (Spec (.of K)) hK
      (M9StacksIntegration.GenusNineCoarseOverField.coarseMap B hZ K hK g hg)
      (NativeSmoothGenusCoarseClassifier.classifyingMor B hZ K hK U₀ q₀ g hg hq₀) =
    schemeSpaceMap a₁ ≫ ASClassifierGeometricLift.nativeMap B (Spec (.of K)) hK
      (M9StacksIntegration.GenusNineCoarseOverField.coarseMap B hZ K hK g hg)
      (NativeSmoothGenusCoarseClassifier.classifyingMor B hZ K hK U₁ q₁ g hg hq₁) := by
  have h := NativeSmoothGenusSourceFullness.coarseMap_eq_of_raw_unit_arrow
    B hZ g hg K hK T
    (rawUnitArrow B hZ K hK g hg q₀ q₁ hq₀ hq₁ a₀ a₁ e he)
    (rawUnitArrow_lift B hZ K hK g hg q₀ q₁ hq₀ hq₁ a₀ a₁ e he)
  have h₀ := AllOriginalCoarseClassifierFibre.nativeMap_precompose K B hK
    (M9StacksIntegration.GenusNineCoarseOverField.coarseMap B hZ K hK g hg)
    (NativeSmoothGenusCoarseClassifier.classifyingMor B hZ K hK U₀ q₀ g hg hq₀) a₀
  have h₁ := AllOriginalCoarseClassifierFibre.nativeMap_precompose K B hK
    (M9StacksIntegration.GenusNineCoarseOverField.coarseMap B hZ K hK g hg)
    (NativeSmoothGenusCoarseClassifier.classifyingMor B hZ K hK U₁ q₁ g hg hq₁) a₁
  exact h₀.symm.trans (h.trans h₁)

end M9Native.NativeSmoothGenusPhysicalCoarseMap
