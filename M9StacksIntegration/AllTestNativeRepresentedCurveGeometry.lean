module

public import M9StacksIntegration.AllTestNativeSchematicCurveReflection
public import StacksFrontier.AlgebraicGeometry.Picard.HilbertSchemeSmoothness

/-!
# Genuine native represented-curve geometry on ORIGINAL schemes

Native properness and smooth relative dimension reflect to the SAME
underlying original scheme morphism. The dimension proof uses actual
identity etale charts and the actual standard-smooth fibre-dimension
criterion. Thus an actual schematic Cartesian chart of a native smooth-genus
family derives its complete ORIGINAL all-field SchemeCurve condition;
no original properness/smoothness/genus/classifier is assumed in that result.
-/

set_option autoImplicit false
@[expose] public section
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace M9StacksIntegration.AllTestNativeRepresentedCurveGeometry
universe u

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Native properness of an actual represented map reflects to the SAME
original scheme morphism, by the genuine represented-pullback criterion. -/
theorem isProper_of_native_yoneda
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {Z T : BigFppfOver B S hS} (q : Z ⟶ T)
    (hq : Space.IsProper B S hS (yoneda.map q)) :
    IsProper ((BigFppfOver.toScheme B S hS).map q) := by
  let P := MorphismProperty.inverseImage (@IsProper.{u}) (BigFppfOver.toScheme B S hS)
  let : P.IsStableUnderBaseChange :=
    ⟨fun h hp => MorphismProperty.of_isPullback (P := @IsProper)
      (h.map (BigFppfOver.toScheme B S hS)) hp⟩
  have hP : P.presheaf (yoneda.map q) :=
    (Space.presheaf_isProper_iff B S hS (yoneda.map q)
      (isAlgebraicSpace_yoneda B S hS Z) (isAlgebraicSpace_yoneda B S hS T)
      (Functor.relativelyRepresentable.map yoneda q)).mp hq
  exact (MorphismProperty.relative_map_iff (F := yoneda) (P := P)).mp hP

/-- Native smooth relative dimension reflects through actual identity
charts to the ORIGINAL standard-smooth scheme condition. -/
theorem smoothOfRelativeDimension_of_native_yoneda
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {Z T : BigFppfOver B S hS} (q : Z ⟶ T) (d : ℕ)
    (hq : Space.IsSmoothOfRelativeDimension B S hS d (yoneda.map q)) :
    SmoothOfRelativeDimension d ((BigFppfOver.toScheme B S hS).map q) := by
  let : Smooth ((BigFppfOver.toScheme B S hS).map q) :=
    (Space.isSmooth_yoneda_map_iff B S hS q).mp hq.1
  apply Stacks.Smooth.smoothOfRelativeDimension_of_fiberDimensionAt_eq _ d
  intro z
  have key := Space.hasRelativeDimensionAt_pointsMap_iff B S hS (d : ℕ∞) (yoneda.map q)
    Z T (𝟙 _) (𝟙 _) q (Space.presheaf_etale_id B S hS Z)
    (Space.presheaf_etale_id B S hS T) (by simp) z
  rw [Space.pointsMap_id] at key
  exact key.mp (hq.2 ((Space.pointsEquivScheme B S hS Z).symm z))

variable (B : BigFppfSite.{u}) (hZ : B.Contains integerBase)

/-- Every actual schematic Cartesian chart of a genuine native smooth-genus
family is proper and smooth relative dimension1 over its ORIGINAL base. -/
theorem proper_smooth_of_native_chart
    (F : CurveFamily B hZ) (g : ℕ) (hF : IsSmoothH0FamilyOfFibreGenus B hZ g F)
    {Z T : BigFppfOver B integerBase hZ} (q : Z ⟶ T) (a : T ⟶ F.base)
    (p : schemeSpace Z ⟶ F.total)
    (hcart : IsPullback p (schemeSpaceMap q) F.toBase (schemeSpaceMap a)) :
    IsProper ((BigFppfOver.toScheme B integerBase hZ).map q) ∧
      SmoothOfRelativeDimension 1 ((BigFppfOver.toScheme B integerBase hZ).map q) := by
  have hp : Space.IsProper B integerBase hZ (yoneda.map q) :=
    (Space.properProperty B integerBase hZ).of_isPullback hcart F.proper
  have hs : Space.IsSmoothOfRelativeDimension B integerBase hZ 1 (yoneda.map q) :=
    (Space.smoothOfRelativeDimensionProperty B integerBase hZ 1).of_isPullback hcart hF.1.1
  exact ⟨isProper_of_native_yoneda B integerBase hZ q hp,
    smoothOfRelativeDimension_of_native_yoneda B integerBase hZ q 1 hs⟩

/-- The ACTUAL native chart derives the literal ORIGINAL all-field curve
condition; no original SchemeCurve or scheme-geometry premise is supplied. -/
theorem schemeCurve_of_native_chart
    (F : CurveFamily B hZ) (g : ℕ) (hF : IsSmoothH0FamilyOfFibreGenus B hZ g F)
    {Z T : BigFppfOver B integerBase hZ} (q : Z ⟶ T) (a : T ⟶ F.base)
    (p : schemeSpace Z ⟶ F.total)
    (hcart : IsPullback p (schemeSpaceMap q) F.toBase (schemeSpaceMap a)) :
    M9StandaloneDraft.SchemeCurve ((BigFppfOver.toScheme B integerBase hZ).map q) g := by
  obtain ⟨hp, hs⟩ := proper_smooth_of_native_chart B hZ F g hF q a p hcart
  let δ : NativeSchematicCurveFamily.properSmoothSchemeFamily B hZ q hp hs ⟶ F :=
    { baseMap := a, totalMap := p, cartesian := hcart }
  exact AllTestNativeSchematicCurveReflection.schemeCurve_of_native_membership B hZ q hp hs g
    (CurveFamily.isSmoothH0FamilyOfFibreGenus_of_hom δ hF)

end M9StacksIntegration.AllTestNativeRepresentedCurveGeometry
