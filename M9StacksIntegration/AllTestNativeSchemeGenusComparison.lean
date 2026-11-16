module

public import M9StacksIntegration.AllTestNativeSchemeFamilyComparison
public import M9StacksIntegration.AllTestNativeSchematicCurveReflection
public import M9StacksIntegration.NativeSmoothGenusCurveClassifier

/-!
# Actual schematic genus-family comparison in both directions

The literal ORIGINAL all-field curve condition gives intrinsic native M_g
membership, including genuine universal H0, for its ACTUAL native image.
Conversely native membership proves the complete original predicate on
exactly the same structural map. The proved family comparison retains the
identity of the original base and coefficient map.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public section
noncomputable section
open CategoryTheory AlgebraicGeometry

namespace M9StacksIntegration.AllTestNativeSchemeGenusComparison
open AllTestBoundedCharts AllTestSchemeFamilies AllTestNativeCurveFamily
  AllTestNativeSchemeFamilyComparison NativeSchematicCurveFamily
universe u
variable (B : BigFppfSite.{u}) (hZ : B.Contains integerBase)

/-- The ACTUAL native image of an original schematic curve family belongs
to the genuine native genus subcategory; universal H0 is derived. -/
theorem nativeSchemeFamily_membership
    (K : Type u) [Field K] (hK : B.Contains (Spec (.of K)))
    {Z T : BigFppfOver B (Spec (.of K)) hK} (q : Z ⟶ T) (g : ℕ)
    (hq : M9StandaloneDraft.SchemeCurve ((BigFppfOver.toScheme B (Spec (.of K)) hK).map q) g) :
    IsSmoothH0FamilyOfFibreGenus B hZ g
      (nativeCurveFamily B hZ K hK
        (standaloneSchemeFamily K ((boundedInclusion B K hK).map q) g hq)) :=
  CurveFamily.isSmoothH0FamilyOfFibreGenus_of_hom
    (nativeSchemeFamilyIso B hZ K hK q g hq).hom
    (M9Native.NativeSmoothGenusCurveClassifier.schemeCurveFamily_membership B hZ
      ((Over.map (fieldToInteger B hZ K hK)).map q) g hq)

/-- Exact two-way comparison on the SAME arbitrary bounded schematic base.
The original predicate still quantifies over EVERY original extension field. -/
theorem schemeCurve_iff_native_membership
    {Z T : BigFppfOver B integerBase hZ} (q : Z ⟶ T)
    (hp : IsProper ((BigFppfOver.toScheme B integerBase hZ).map q))
    (hs : SmoothOfRelativeDimension 1 ((BigFppfOver.toScheme B integerBase hZ).map q))
    (g : ℕ) :
    M9StandaloneDraft.SchemeCurve ((BigFppfOver.toScheme B integerBase hZ).map q) g ↔
      IsSmoothH0FamilyOfFibreGenus B hZ g (properSmoothSchemeFamily B hZ q hp hs) := by
  constructor
  · intro hq
    exact M9Native.NativeSmoothGenusCurveClassifier.schemeCurveFamily_membership B hZ q g hq
  · exact AllTestNativeSchematicCurveReflection.schemeCurve_of_native_membership B hZ q hp hs g

end M9StacksIntegration.AllTestNativeSchemeGenusComparison
