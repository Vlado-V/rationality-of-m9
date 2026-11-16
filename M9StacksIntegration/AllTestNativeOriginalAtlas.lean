module

public import M9StacksIntegration.AllTestNativeOriginalRestriction

/-!
# The actual constructed original space has a genuinely bounded atlas

The native presentation, original-site geometric descent, and genuine
value-universe reflection produce an atlas of the literal original space
whose underlying scheme belongs to the ORIGINAL native site. This does
not unfold a choice of original space or assume a presentation of it.
-/

set_option autoImplicit false
@[expose] public section
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

namespace M9StacksIntegration.AllTestNativeOriginalAtlas
open AllTestBoundedCharts AllTestNativeSpacePresentation AllTestNativeOriginalSpace
  AllTestPresentationDiagonal AllTestPresentationAtlas AllTestLargeSpaceGeometry
universe u
variable (K : Type u) [Field K] (B : BigFppfSite.{u})
  (hK : B.Contains (Spec (.of K)))

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- An actual bounded atlas of the SAME constructed original space, with
its genuine original representable surjective-etale properties. -/
theorem exists_bounded_original_atlas
    (F : (BigFppfOver B (Spec (.of K)) hK)ᵒᵖ ⥤ Type u)
    (hF : IsAlgebraicSpace B (Spec (.of K)) hK F) :
    ∃ (U : BigFppfOver B (Spec (.of K)) hK)
      (a : yoneda.obj ((boundedInclusion B K hK).obj U) ⟶
        (originalSpaceOfNative K B hK F hF).obj),
      (MorphismProperty.inverseImage (@Etale.{u})
        (Over.forget (M9StandaloneDraft.Base K))).presheaf a ∧
      (MorphismProperty.inverseImage (@Surjective.{u})
        (Over.forget (M9StandaloneDraft.Base K))).presheaf a := by
  let E := extendedNativeSheaf K B hK F hF
  let G := originalSpaceOfNative K B hK F hF
  let e := originalSpaceOfNativeIso K B hK F hF
  obtain ⟨U, R, s, t, a, ha, hker, _, _, hts, hte⟩ :=
    exists_extended_native_presentation K B hK F hF
  have hd := diagonal_representable_of_presentation K E.property
    ((boundedInclusion B K hK).obj U) ((boundedInclusion B K hK).obj R)
    ((boundedInclusion B K hK).map s) ((boundedInclusion B K hK).map t)
    a ha hker hte
  let : MorphismProperty.DescendsAlong (@Etale.{u})
      (@Surjective ⊓ @Flat ⊓ @LocallyOfFinitePresentation) :=
    Space.etale_descendsAlong_surjective_inf_flat_inf_locallyOfFinitePresentation
  let : MorphismProperty.DescendsAlong (@Surjective.{u})
      (@Surjective ⊓ @Flat ⊓ @LocallyOfFinitePresentation) :=
    Space.surjective_descendsAlong_surjective_inf_flat_inf_locallyOfFinitePresentation
  have he := atlas_presheafProperty_of_presentation K (@Etale.{u}) E.property
    ((boundedInclusion B K hK).obj U) ((boundedInclusion B K hK).obj R)
    ((boundedInclusion B K hK).map s) ((boundedInclusion B K hK).map t)
    a ha hker hd hte
  have hs := atlas_presheafProperty_of_presentation K (@Surjective.{u}) E.property
    ((boundedInclusion B K hK).obj U) ((boundedInclusion B K hK).obj R)
    ((boundedInclusion B K hK).map s) ((boundedInclusion B K hK).map t)
    a ha hker hd hts
  let W := valueLift K
  let : W.Full := (valueLift_fullyFaithful K).full
  let : W.Faithful := (valueLift_fullyFaithful K).faithful
  let aS : yoneda.obj ((boundedInclusion B K hK).obj U) ⟶ G.obj :=
    W.preimage (a ≫ e.inv)
  have hea : W.map aS ≫ e.hom = a := by
    rw [Functor.map_preimage]
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  exact ⟨U, aS, presheafProperty_of_large K _ G.obj E.obj e aS a hea he,
    presheafProperty_of_large K _ G.obj E.obj e aS a hea hs⟩

end M9StacksIntegration.AllTestNativeOriginalAtlas
