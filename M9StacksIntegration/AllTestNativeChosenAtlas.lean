module

public import M9StacksIntegration.AllTestNativeOriginalAtlas

/-!
# Retaining a specified native atlas on the full original site

The actual sheaf extension retains the same original chart scheme and the
same original kernel-pair maps. This allows compactness and finite type of
a chosen atlas to be retained instead of choosing an unrelated atlas.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

namespace M9StacksIntegration.AllTestNativeChosenAtlas
open AllTestBoundedCharts AllTestNativeOriginalSpace AllTestNativeSpacePresentation
  AllTestLargeSiteAtlas AllTestLargeSpaceGeometry AllTestPresentationDiagonal
  AllTestPresentationAtlas
universe u
variable (K : Type u) [Field K] (B : BigFppfSite.{u})
  (hK : B.Contains (Spec (.of K)))

/-- The literal large-valued extension of the specified native chart. -/
def extendedChart
    (F : (BigFppfOver B (Spec (.of K)) hK)ᵒᵖ ⥤ Type u)
    (hF : IsAlgebraicSpace B (Spec (.of K)) hK F)
    (U : BigFppfOver B (Spec (.of K)) hK) (q : yoneda.obj U ⟶ F) :
    (AllTestLargeSpaceSmallSections.largeYoneda K).obj ((boundedInclusion B K hK).obj U) ⟶
      (extendedNativeSheaf K B hK F hF).obj :=
  (extendedAtlas K B hK _ U (nativeLargeAtlas K B hK ⟨F, hF.isSheaf⟩ U q)).hom

/-- The actual specified native chart, on every original test scheme. -/
def originalChart
    (F : (BigFppfOver B (Spec (.of K)) hK)ᵒᵖ ⥤ Type u)
    (hF : IsAlgebraicSpace B (Spec (.of K)) hK F)
    (U : BigFppfOver B (Spec (.of K)) hK) (q : yoneda.obj U ⟶ F) :
    yoneda.obj ((boundedInclusion B K hK).obj U) ⟶
      (originalSpaceOfNative K B hK F hF).obj := by
  let W := valueLift K
  let : W.Full := (valueLift_fullyFaithful K).full
  exact W.preimage (extendedChart K B hK F hF U q ≫
    (originalSpaceOfNativeIso K B hK F hF).inv)

/-- The original chart is the genuine preimage of its actual sheaf extension. -/
theorem originalChart_comparison
    (F : (BigFppfOver B (Spec (.of K)) hK)ᵒᵖ ⥤ Type u)
    (hF : IsAlgebraicSpace B (Spec (.of K)) hK F)
    (U : BigFppfOver B (Spec (.of K)) hK) (q : yoneda.obj U ⟶ F) :
    (valueLift K).map (originalChart K B hK F hF U q) ≫
      (originalSpaceOfNativeIso K B hK F hF).hom = extendedChart K B hK F hF U q := by
  let : (valueLift K).Full := (valueLift_fullyFaithful K).full
  dsimp only [originalChart]
  rw [Functor.map_preimage]
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]

/-- The same pair of original scheme maps is a kernel pair of the
specified original chart on all original tests. -/
theorem originalChart_kernelPair
    (F : (BigFppfOver B (Spec (.of K)) hK)ᵒᵖ ⥤ Type u)
    (hF : IsAlgebraicSpace B (Spec (.of K)) hK F)
    {U R : BigFppfOver B (Spec (.of K)) hK} (s t : R ⟶ U)
    (q : yoneda.obj U ⟶ F) (h : IsPullback (yoneda.map s) (yoneda.map t) q q) :
    IsPullback (yoneda.map ((boundedInclusion B K hK).map s))
      (yoneda.map ((boundedInclusion B K hK).map t))
      (originalChart K B hK F hF U q) (originalChart K B hK F hF U q) := by
  let W := valueLift K
  let : W.Faithful := (valueLift_fullyFaithful K).faithful
  apply IsPullback.of_map_of_faithful W
  have hL := extendedAtlas_presheaf_isPullback K B hK _ s t
    (nativeLargeAtlas K B hK ⟨F, hF.isSheaf⟩ U q)
    (nativeLargeAtlas_isPullback K B hK ⟨F, hF.isSheaf⟩ s t q h)
  have hc : extendedChart K B hK F hF U q ≫
      (originalSpaceOfNativeIso K B hK F hF).inv =
        W.map (originalChart K B hK F hF U q) := by
    rw [← originalChart_comparison K B hK F hF U q]
    simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]
    rfl
  apply hL.of_iso (Iso.refl _) (Iso.refl _) (Iso.refl _)
    (originalSpaceOfNativeIso K B hK F hF).symm
  · simp only [Iso.refl_hom, Category.id_comp, Category.comp_id]
    rfl
  · simp only [Iso.refl_hom, Category.id_comp, Category.comp_id]
    rfl
  · simp only [Iso.refl_hom, Category.id_comp, Iso.symm_hom]
    change extendedChart K B hK F hF U q ≫ (originalSpaceOfNativeIso K B hK F hF).inv =
      W.map (originalChart K B hK F hF U q)
    exact hc
  · simp only [Iso.refl_hom, Category.id_comp, Iso.symm_hom]
    change extendedChart K B hK F hF U q ≫ (originalSpaceOfNativeIso K B hK F hF).inv =
      W.map (originalChart K B hK F hF U q)
    exact hc

/-- A specified genuine surjective etale native atlas remains a surjective
etale atlas of the SAME constructed original space on every original test. -/
theorem originalChart_geometry
    (F : (BigFppfOver B (Spec (.of K)) hK)ᵒᵖ ⥤ Type u)
    (hF : IsAlgebraicSpace B (Spec (.of K)) hK F)
    (U : BigFppfOver B (Spec (.of K)) hK) (q : yoneda.obj U ⟶ F)
    (hs : (MorphismProperty.inverseImage (@Surjective.{u})
      (BigFppfOver.toScheme B (Spec (.of K)) hK)).presheaf q)
    (he : (MorphismProperty.inverseImage (@Etale.{u})
      (BigFppfOver.toScheme B (Spec (.of K)) hK)).presheaf q) :
    (MorphismProperty.inverseImage (@Etale.{u})
      (Over.forget (M9StandaloneDraft.Base K))).presheaf (originalChart K B hK F hF U q) ∧
    (MorphismProperty.inverseImage (@Surjective.{u})
      (Over.forget (M9StandaloneDraft.Base K))).presheaf (originalChart K B hK F hF U q) := by
  let R := he.rep.pullback q
  let s : R ⟶ U := he.rep.fst' q
  let t : R ⟶ U := he.rep.snd q
  have hR : IsPullback (yoneda.map s) (yoneda.map t) q q := he.rep.isPullback' q
  have hte : Etale ((BigFppfOver.toScheme B (Spec (.of K)) hK).map t) :=
    he.property q (yoneda.map s) t hR
  have hts : Surjective ((BigFppfOver.toScheme B (Spec (.of K)) hK).map t) :=
    hs.property q (yoneda.map s) t hR
  let A : Sheaf (BigFppfOver.topology B (Spec (.of K)) hK) (Type u) := ⟨F, hF.isSheaf⟩
  have hls : Presheaf.IsLocallySurjective (BigFppfOver.topology B (Spec (.of K)) hK) q :=
    Space.isLocallySurjective_of_presheaf_surjective_etale B (Spec (.of K)) hK
      (G := A) (a := q) hs he
  have ha : Presheaf.IsLocallySurjective
      (Scheme.fppfTopology.over (M9StandaloneDraft.Base K)) (extendedChart K B hK F hF U q) :=
    extendedAtlas_isLocallySurjective K B hK _ U (nativeLargeAtlas K B hK A U q)
      (nativeLargeAtlas_isLocallySurjective K B hK A U q hls)
  have hker := extendedAtlas_presheaf_isPullback K B hK _ s t
    (nativeLargeAtlas K B hK A U q) (nativeLargeAtlas_isPullback K B hK A s t q hR)
  have hd := diagonal_representable_of_presentation K (extendedNativeSheaf K B hK F hF).property
    ((boundedInclusion B K hK).obj U) ((boundedInclusion B K hK).obj R)
    ((boundedInclusion B K hK).map s) ((boundedInclusion B K hK).map t)
    (extendedChart K B hK F hF U q) ha hker hte
  let : MorphismProperty.DescendsAlong (@Etale.{u})
      (@Surjective ⊓ @Flat ⊓ @LocallyOfFinitePresentation) :=
    Space.etale_descendsAlong_surjective_inf_flat_inf_locallyOfFinitePresentation
  let : MorphismProperty.DescendsAlong (@Surjective.{u})
      (@Surjective ⊓ @Flat ⊓ @LocallyOfFinitePresentation) :=
    Space.surjective_descendsAlong_surjective_inf_flat_inf_locallyOfFinitePresentation
  constructor
  · apply presheafProperty_of_large K _ _ _ (originalSpaceOfNativeIso K B hK F hF)
      _ _ (originalChart_comparison K B hK F hF U q)
    exact atlas_presheafProperty_of_presentation K (@Etale.{u})
      (extendedNativeSheaf K B hK F hF).property
      ((boundedInclusion B K hK).obj U) ((boundedInclusion B K hK).obj R)
      ((boundedInclusion B K hK).map s) ((boundedInclusion B K hK).map t)
      (extendedChart K B hK F hF U q) ha hker hd hte
  · apply presheafProperty_of_large K _ _ _ (originalSpaceOfNativeIso K B hK F hF)
      _ _ (originalChart_comparison K B hK F hF U q)
    exact atlas_presheafProperty_of_presentation K (@Surjective.{u})
      (extendedNativeSheaf K B hK F hF).property
      ((boundedInclusion B K hK).obj U) ((boundedInclusion B K hK).obj R)
      ((boundedInclusion B K hK).map s) ((boundedInclusion B K hK).map t)
      (extendedChart K B hK F hF U q) ha hker hd hts

end M9StacksIntegration.AllTestNativeChosenAtlas
