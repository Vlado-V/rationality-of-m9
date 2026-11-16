module

public import M9StacksIntegration.AllTestNativeSpacePresentation
public import M9StacksIntegration.AllTestPresentationAtlas
public import M9StacksIntegration.AllTestLargeSpaceGeometry

/-!
# Actual native algebraic spaces on the full original test category

Starting with an actual native algebraic space, construct its actual
large-valued sheaf extension on ALL original test schemes. Its actual
transported etale presentation proves diagonal representability and the
atlas's scheme properties by genuine original-site descent. Proved section
smallness then constructs the literal standalone original algebraic space,
with a natural isomorphism to the actual extension after value lift.

This compares actual algebraic spaces. It does not assert any coarse moduli
classifier, universality, curve classification, rationality or density.
-/

set_option autoImplicit false
@[expose] public section
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

namespace M9StacksIntegration.AllTestNativeOriginalSpace
open AllTestNativeSpacePresentation AllTestPresentationDiagonal AllTestPresentationAtlas
  AllTestLargeSpaceGeometry AllTestLargeSpaceSmallSections
universe u
variable (K : Type u) [Field K] (B : BigFppfSite.{u})
  (hK : B.Contains (Spec (.of K)))

/-- Every actual native algebraic space constructs an ACTUAL original
algebraic space on all original tests, with its natural universe comparison.
No original-space, diagonal, atlas, section-size or classifier premise occurs. -/
theorem exists_originalSpace_of_native
    (F : (BigFppfOver B (Spec (.of K)) hK)ᵒᵖ ⥤ Type u)
    (hF : IsAlgebraicSpace B (Spec (.of K)) hK F) :
    ∃ G : M9StandaloneDraft.Space K,
      Nonempty ((valueLift K).obj G.obj ≅ (extendedNativeSheaf K B hK F hF).obj) := by
  let E := extendedNativeSheaf K B hK F hF
  obtain ⟨U, R, s, t, a, ha, hker, _, _, hts, hte⟩ :=
    exists_extended_native_presentation K B hK F hF
  have hd := diagonal_representable_of_presentation K E.property
    ((AllTestBoundedCharts.boundedInclusion B K hK).obj U)
    ((AllTestBoundedCharts.boundedInclusion B K hK).obj R)
    ((AllTestBoundedCharts.boundedInclusion B K hK).map s)
    ((AllTestBoundedCharts.boundedInclusion B K hK).map t) a ha hker hte
  let : MorphismProperty.DescendsAlong (@Etale.{u})
      (@Surjective ⊓ @Flat ⊓ @LocallyOfFinitePresentation) :=
    Space.etale_descendsAlong_surjective_inf_flat_inf_locallyOfFinitePresentation
  let : MorphismProperty.DescendsAlong (@Surjective.{u})
      (@Surjective ⊓ @Flat ⊓ @LocallyOfFinitePresentation) :=
    Space.surjective_descendsAlong_surjective_inf_flat_inf_locallyOfFinitePresentation
  have he := atlas_presheafProperty_of_presentation K (@Etale.{u}) E.property
    ((AllTestBoundedCharts.boundedInclusion B K hK).obj U)
    ((AllTestBoundedCharts.boundedInclusion B K hK).obj R)
    ((AllTestBoundedCharts.boundedInclusion B K hK).map s)
    ((AllTestBoundedCharts.boundedInclusion B K hK).map t) a ha hker hd hte
  have hs := atlas_presheafProperty_of_presentation K (@Surjective.{u}) E.property
    ((AllTestBoundedCharts.boundedInclusion B K hK).obj U)
    ((AllTestBoundedCharts.boundedInclusion B K hK).obj R)
    ((AllTestBoundedCharts.boundedInclusion B K hK).map s)
    ((AllTestBoundedCharts.boundedInclusion B K hK).map t) a ha hker hd hts
  let G := originalSpaceOfLargeAtlas K E.obj E.property hd
    ((AllTestBoundedCharts.boundedInclusion B K hK).obj U) a he hs
  exact ⟨G, ⟨originalSpaceOfLargeAtlasIso K E.obj E.property hd
    ((AllTestBoundedCharts.boundedInclusion B K hK).obj U) a he hs⟩⟩

/-- The actual original algebraic space constructed from the native one. -/
def originalSpaceOfNative
    (F : (BigFppfOver B (Spec (.of K)) hK)ᵒᵖ ⥤ Type u)
    (hF : IsAlgebraicSpace B (Spec (.of K)) hK F) : M9StandaloneDraft.Space K :=
  (exists_originalSpace_of_native K B hK F hF).choose

/-- Literal all-test natural comparison with the constructed large extension. -/
def originalSpaceOfNativeIso
    (F : (BigFppfOver B (Spec (.of K)) hK)ᵒᵖ ⥤ Type u)
    (hF : IsAlgebraicSpace B (Spec (.of K)) hK F) :
    (valueLift K).obj (originalSpaceOfNative K B hK F hF).obj ≅
      (extendedNativeSheaf K B hK F hF).obj :=
  Classical.choice (exists_originalSpace_of_native K B hK F hF).choose_spec

end M9StacksIntegration.AllTestNativeOriginalSpace
