module

public import M9StacksIntegration.AllTestBoundedAtlasFull
public import M9StacksIntegration.AllTestNativeOriginalAtlas

/-!
# Genuine recovery of every original bounded-atlas algebraic space

The actual extension of the actual bounded restriction is naturally
isomorphic to the SAME original algebraic-space presheaf on ALL tests.
The inverse maps are constructed by actual atlas descent, and their inverse
laws follow from actual bounded-map detection. No desired equivalence or
classifier is an argument. Every original Space admits some such site;
no single cutoff is asserted to contain all original test schemes.
-/

set_option autoImplicit false
@[expose] public section
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

namespace M9StacksIntegration.AllTestBoundedOriginalRecovery
open AllTestBoundedCharts AllTestBoundedRestriction AllTestBoundedCartesian
  AllTestBoundedAlgebraicSpace AllTestBoundedSpaceTargets AllTestBoundedAtlasFull
  AllTestNativeOriginalSpace AllTestNativeOriginalRestriction AllTestNativeOriginalAtlas
universe u
variable (K : Type u) [Field K] (B : BigFppfSite.{u})
  (hK : B.Contains (Spec (.of K)))

/-- The genuine unit comparison in the ORIGINAL Type-u value universe. -/
def originalNativeRestrictionSmallIso
    (F : (BigFppfOver B (Spec (.of K)) hK)ᵒᵖ ⥤ Type u)
    (hF : IsAlgebraicSpace B (Spec (.of K)) hK F) :
    restrict K B hK (originalSpaceOfNative K B hK F hF).obj ≅ F :=
  (fullyFaithfulULiftFunctor.{u+1, u}.whiskeringRight _).preimageIso
    (originalNativeRestrictionIso K B hK F hF)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Genuine recovery of the literal original Space from its actual bounded
restriction, with the original site and value universe unchanged. -/
def originalOfRestrictionIso_of_bounded_atlas
    (W : M9StandaloneDraft.Space K)
    (Z : BigFppfOver B (Spec (.of K)) hK)
    (r : yoneda.obj ((boundedInclusion B K hK).obj Z) ⟶ W.obj)
    (he : (MorphismProperty.inverseImage (@Etale.{u})
      (Over.forget (M9StandaloneDraft.Base K))).presheaf r)
    (hs : (MorphismProperty.inverseImage (@Surjective.{u})
      (Over.forget (M9StandaloneDraft.Base K))).presheaf r) :
    (originalSpaceOfNative K B hK (restrict K B hK W.obj)
      (isAlgebraicSpace_restrict_of_bounded_atlas K B hK W
        ((boundedInclusion B K hK).obj Z) Z.left.property r he hs)).obj ≅ W.obj := Classical.choice <| by
  let hW := isAlgebraicSpace_restrict_of_bounded_atlas K B hK W
    ((boundedInclusion B K hK).obj Z) Z.left.property r he hs
  let G := originalSpaceOfNative K B hK (restrict K B hK W.obj) hW
  let e := originalNativeRestrictionSmallIso K B hK (restrict K B hK W.obj) hW
  obtain ⟨U, a, hae, has⟩ := exists_bounded_original_atlas K B hK
    (restrict K B hK W.obj) hW
  obtain ⟨f, hf, _⟩ := existsUnique_lift_restrictMap_of_bounded_atlas K B hK
    G U a hae has W.obj W.isSheaf e.hom
  obtain ⟨g, hg, _⟩ := existsUnique_lift_restrictMap_of_bounded_atlas K B hK
    W Z r he hs G.obj G.isSheaf e.inv
  refine ⟨⟨f, g, ?_, ?_⟩⟩
  · apply restrictMap_injective_of_bounded_atlas K B hK G U a hae has G.obj G.isSheaf
    let L := restrictionFunctor K B hK
    change L.map (f ≫ g) = L.map (𝟙 G.obj)
    rw [L.map_comp, L.map_id]
    change restrictMap K B hK f ≫ restrictMap K B hK g = 𝟙 _
    rw [hf, hg, e.hom_inv_id]
  · apply restrictMap_injective_of_bounded_atlas K B hK W Z r he hs W.obj W.isSheaf
    let L := restrictionFunctor K B hK
    change L.map (g ≫ f) = L.map (𝟙 W.obj)
    rw [L.map_comp, L.map_id]
    change restrictMap K B hK g ≫ restrictMap K B hK f = 𝟙 _
    rw [hf, hg, e.inv_hom_id]

end M9StacksIntegration.AllTestBoundedOriginalRecovery
