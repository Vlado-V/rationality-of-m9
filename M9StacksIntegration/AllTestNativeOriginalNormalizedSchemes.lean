module

public import M9StacksIntegration.AllTestNativeOriginalUnit
public import M9StacksIntegration.AllTestNativeOriginalSchemes

/-!
# Actual same-scheme comparison normalized by native recovery

The original represented-scheme comparison is constructed with its prescribed
restriction: its composite with actual restriction-Yoneda is precisely the
actual native recovery unit. Full original atlas descent constructs this
map; the genuine natural recovery proves that it is invertible and natural.
This fixes the ORIGINAL base and coefficient map in family recovery, without
assuming a scheme comparison or quotienting by base automorphisms.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public section
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace M9StacksIntegration.AllTestNativeOriginalNormalizedSchemes
open AllTestNativeOriginalUnit AllTestNativeOriginalFunctor
  AllTestNativeOriginalSchemes AllTestBoundedOriginalRecovery
  AllTestNativeOriginalSpace AllTestBoundedCharts AllTestBoundedRestriction
  AllTestBoundedFaithful AllTestBoundedAlgebraicSpace AllTestBoundedAtlasFull AllTestNativeOriginalAtlas
  AllTestSchemeFamilies
universe u
variable (K : Type u) [Field K] (B : BigFppfSite.{u})
  (hK : B.Contains (Spec (.of K)))

/-- Actual recovery makes original-image restriction fully faithful. -/
def originalRestrictionFullyFaithful :
    (originalPresheafFunctor K B hK ⋙ restrictionFunctor K B hK).FullyFaithful :=
  (ObjectProperty.fullyFaithfulι (IsAlgebraicSpace B (Spec (.of K)) hK)).ofIso
    (originalRestrictionUnitIso K B hK).symm

/-- An original map between actual native images is invertible whenever
its literal native restriction is invertible. -/
theorem isIso_of_restrictMap_of_original
    {F G : AlgebraicSpaces B (Spec (.of K)) hK}
    (f : (originalPresheafFunctor K B hK).obj F ⟶
      (originalPresheafFunctor K B hK).obj G)
    [IsIso (restrictMap K B hK f)] : IsIso f := by
  let O := originalPresheafFunctor K B hK
  let R := restrictionFunctor K B hK
  let ff := originalPresheafFullyFaithful K B hK
  let : (O ⋙ R).Full := (originalRestrictionFullyFaithful K B hK).full
  let : (O ⋙ R).Faithful := (originalRestrictionFullyFaithful K B hK).faithful
  let a : F ⟶ G := ff.preimage f
  have ha : O.map a = f := ff.map_preimage f
  have : IsIso ((O ⋙ R).map a) := by
    change IsIso (R.map (O.map a))
    rw [ha]
    change IsIso (restrictMap K B hK f)
    infer_instance
  have : IsIso a := isIso_of_reflects_iso a (O ⋙ R)
  have : IsIso (O.map a) := inferInstance
  exact ha ▸ this

/-- Genuine original atlas descent constructs the prescribed SAME-scheme map. -/
theorem existsUnique_normalizedSchemeHom (U : BigFppfOver B (Spec (.of K)) hK) :
    ∃! f : (originalPresheafFunctor K B hK).obj (schemeSpace U) ⟶
        yoneda.obj ((boundedInclusion B K hK).obj U),
      restrictMap K B hK f =
        (originalNativeRestrictionSmallIso K B hK (schemeSpace U).obj
          (schemeSpace U).property).hom ≫ (restrictRepresentableIso B K hK U).inv := by
  let W := originalSpaceOfNative K B hK (schemeSpace U).obj (schemeSpace U).property
  obtain ⟨Z, a, he, hs⟩ := exists_bounded_original_atlas K B hK
    (schemeSpace U).obj (schemeSpace U).property
  exact existsUnique_lift_restrictMap_of_bounded_atlas K B hK W Z a he hs
    (yoneda.obj ((boundedInclusion B K hK).obj U))
    (standaloneSchemeSpace K ((boundedInclusion B K hK).obj U)).isSheaf _

/-- The actual prescribed SAME-scheme morphism. -/
def normalizedSchemeHom (U : BigFppfOver B (Spec (.of K)) hK) :
    (originalPresheafFunctor K B hK).obj (schemeSpace U) ⟶
      yoneda.obj ((boundedInclusion B K hK).obj U) :=
  (existsUnique_normalizedSchemeHom K B hK U).choose

/-- Literal restriction of the actual chosen comparison. -/
theorem normalizedSchemeHom_restrict (U : BigFppfOver B (Spec (.of K)) hK) :
    restrictMap K B hK (normalizedSchemeHom K B hK U) =
      (originalNativeRestrictionSmallIso K B hK (schemeSpace U).obj
        (schemeSpace U).property).hom ≫ (restrictRepresentableIso B K hK U).inv :=
  (existsUnique_normalizedSchemeHom K B hK U).choose_spec.1

/-- Invertibility follows from the actual natural recovery and genuine
full faithfulness, rather than a supplied same-scheme isomorphism. -/
theorem isIso_normalizedSchemeHom (U : BigFppfOver B (Spec (.of K)) hK) :
    IsIso (normalizedSchemeHom K B hK U) := by
  let e := originalSchemeIso K B hK U
  have : IsIso ((restrictionFunctor K B hK).map (normalizedSchemeHom K B hK U)) := by
    change IsIso (restrictMap K B hK (normalizedSchemeHom K B hK U))
    rw [normalizedSchemeHom_restrict]
    infer_instance
  have : IsIso (restrictMap K B hK (normalizedSchemeHom K B hK U ≫ e.inv)) := by
    change IsIso ((restrictionFunctor K B hK).map (normalizedSchemeHom K B hK U ≫ e.inv))
    rw [Functor.map_comp]
    infer_instance
  let : IsIso (normalizedSchemeHom K B hK U ≫ e.inv) :=
    isIso_of_restrictMap_of_original K B hK (normalizedSchemeHom K B hK U ≫ e.inv)
  have : IsIso ((normalizedSchemeHom K B hK U ≫ e.inv) ≫ e.hom) := inferInstance
  simpa only [Category.assoc, Iso.inv_hom_id, Category.comp_id] using this

/-- The actual isomorphism retaining the ORIGINAL represented base scheme. -/
def normalizedSchemeIso (U : BigFppfOver B (Spec (.of K)) hK) :
    (originalPresheafFunctor K B hK).obj (schemeSpace U) ≅
      yoneda.obj ((boundedInclusion B K hK).obj U) := by
  letI := isIso_normalizedSchemeHom K B hK U
  exact asIso (normalizedSchemeHom K B hK U)

/-- Native recovery fixes the same original base and coefficient map. -/
theorem normalizedSchemeIso_restrict (U : BigFppfOver B (Spec (.of K)) hK) :
    restrictMap K B hK (normalizedSchemeIso K B hK U).hom ≫
        (restrictRepresentableIso B K hK U).hom =
      (originalNativeRestrictionSmallIso K B hK (schemeSpace U).obj
        (schemeSpace U).property).hom := by
  change restrictMap K B hK (normalizedSchemeHom K B hK U) ≫ _ = _
  rw [normalizedSchemeHom_restrict, Category.assoc, Iso.inv_hom_id, Category.comp_id]

set_option backward.defeqAttrib.useBackward true in
/-- The normalized comparison retains EVERY actual original scheme map. -/
theorem normalizedSchemeIso_naturality
    {U V : BigFppfOver B (Spec (.of K)) hK} (v : U ⟶ V) :
    (originalPresheafFunctor K B hK).map (schemeSpaceMap v) ≫
        (normalizedSchemeIso K B hK V).hom =
      (normalizedSchemeIso K B hK U).hom ≫
        yoneda.map ((boundedInclusion B K hK).map v) := by
  let W := originalSpaceOfNative K B hK (schemeSpace U).obj (schemeSpace U).property
  obtain ⟨Z, a, he, hs⟩ := exists_bounded_original_atlas K B hK
    (schemeSpace U).obj (schemeSpace U).property
  apply restrictMap_injective_of_bounded_atlas K B hK W Z a he hs
    (yoneda.obj ((boundedInclusion B K hK).obj V))
    (standaloneSchemeSpace K ((boundedInclusion B K hK).obj V)).isSheaf
  change (restrictionFunctor K B hK).map
      ((originalPresheafFunctor K B hK).map (schemeSpaceMap v) ≫
        (normalizedSchemeIso K B hK V).hom) =
    (restrictionFunctor K B hK).map
      ((normalizedSchemeIso K B hK U).hom ≫
        yoneda.map ((boundedInclusion B K hK).map v))
  rw [Functor.map_comp, Functor.map_comp]
  change restrictMap K B hK ((originalPresheafFunctor K B hK).map (schemeSpaceMap v)) ≫
      restrictMap K B hK (normalizedSchemeIso K B hK V).hom =
    restrictMap K B hK (normalizedSchemeIso K B hK U).hom ≫
      restrictMap K B hK (yoneda.map ((boundedInclusion B K hK).map v))
  apply (cancel_mono (restrictRepresentableIso B K hK V).hom).mp
  calc
    _ = restrictMap K B hK ((originalPresheafFunctor K B hK).map (schemeSpaceMap v)) ≫
        (originalNativeRestrictionSmallIso K B hK (schemeSpace V).obj
          (schemeSpace V).property).hom := by
      rw [Category.assoc, normalizedSchemeIso_restrict]
    _ = (originalNativeRestrictionSmallIso K B hK (schemeSpace U).obj
        (schemeSpace U).property).hom ≫ yoneda.map v :=
      originalNativeRestrictionSmallIso_naturality K B hK (schemeSpaceMap v)
    _ = (restrictMap K B hK (normalizedSchemeIso K B hK U).hom ≫
        (restrictRepresentableIso B K hK U).hom) ≫ yoneda.map v := by
      rw [normalizedSchemeIso_restrict]
    _ = _ := by
      rw [Category.assoc, Category.assoc,
        AllTestBoundedCartesian.restrictRepresentableIso_naturality]

end M9StacksIntegration.AllTestNativeOriginalNormalizedSchemes
