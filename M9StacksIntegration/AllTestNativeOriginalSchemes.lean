module

public import M9StacksIntegration.AllTestNativeOriginalFunctor
public import M9StacksIntegration.AllTestLargeSiteYoneda

/-!
# The actual original functor preserves the SAME schemes and scheme maps

The constructed original image of a native represented space is naturally
the literal represented ORIGINAL scheme. This uses actual natural Yoneda
transport through extension, followed by the proved fully faithful value
lift. The displayed morphism compatibility retains the actual original
coefficient map; no schematic comparison premise is assumed.
-/

set_option autoImplicit false
@[expose] public section
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

namespace M9StacksIntegration.AllTestNativeOriginalSchemes
open AllTestBoundedCharts AllTestNativeOriginalFunctor AllTestNativeOriginalSpace
  AllTestLargeSiteYoneda AllTestLargeSpaceGeometry AllTestLargeSpaceSmallSections
universe u
variable (K : Type u) [Field K] (B : BigFppfSite.{u})
  (hK : B.Contains (Spec (.of K)))

/-- The actual lifted original image of a native represented space is the
literal universe-lifted ORIGINAL represented scheme. -/
def originalSchemeLiftIso (U : BigFppfOver B (Spec (.of K)) hK) :
    (valueLift K).obj ((originalPresheafFunctor K B hK).obj (schemeSpace U)) ≅
      (largeYoneda K).obj ((boundedInclusion B K hK).obj U) :=
  (originalComparison K B hK).app (schemeSpace U) ≪≫
    (sheafToPresheaf (Scheme.fppfTopology.over (M9StandaloneDraft.Base K)) (Type (u+1))).mapIso
      ((extendCompYonedaIso K B hK).app U)

/-- The actual original image is the SAME literal original scheme, on all tests. -/
def originalSchemeIso (U : BigFppfOver B (Spec (.of K)) hK) :
    (originalPresheafFunctor K B hK).obj (schemeSpace U) ≅
      yoneda.obj ((boundedInclusion B K hK).obj U) :=
  (valueLift_fullyFaithful K).preimageIso (originalSchemeLiftIso K B hK U)

/-- The comparison is the actual preimage under the value lift. -/
theorem valueLift_originalSchemeIso_hom (U : BigFppfOver B (Spec (.of K)) hK) :
    (valueLift K).map (originalSchemeIso K B hK U).hom =
      (originalSchemeLiftIso K B hK U).hom :=
  (valueLift_fullyFaithful K).map_preimage _

set_option backward.isDefEq.respectTransparency false in
/-- Literal compatibility with EVERY original scheme map coming from the native site. -/
theorem originalSchemeIso_naturality {U V : BigFppfOver B (Spec (.of K)) hK}
    (f : U ⟶ V) :
    (originalPresheafFunctor K B hK).map (schemeSpaceMap f) ≫
        (originalSchemeIso K B hK V).hom =
      (originalSchemeIso K B hK U).hom ≫ yoneda.map ((boundedInclusion B K hK).map f) := by
  apply (valueLift_fullyFaithful K).map_injective
  rw [(valueLift K).map_comp, (valueLift K).map_comp,
    valueLift_originalSchemeIso_hom, valueLift_originalSchemeIso_hom]
  let e := extendCompYonedaIso K B hK
  have hY := congrArg
    (fun m => (sheafToPresheaf
      (Scheme.fppfTopology.over (M9StandaloneDraft.Base K)) (Type (u+1))).map m)
    (e.hom.naturality f)
  change (valueLift K).map (originalPresheafMap K B hK (schemeSpaceMap f)) ≫
      ((originalSpaceOfNativeIso K B hK (schemeSpace V).obj (schemeSpace V).property).hom ≫
        ((sheafToPresheaf _ (Type (u+1))).map (e.app V).hom)) =
    ((originalSpaceOfNativeIso K B hK (schemeSpace U).obj (schemeSpace U).property).hom ≫
        ((sheafToPresheaf _ (Type (u+1))).map (e.app U).hom)) ≫
      (largeYoneda K).map ((boundedInclusion B K hK).map f)
  rw [← Category.assoc, valueLift_originalPresheafMap, Category.assoc, Category.assoc]
  apply congrArg (fun m =>
    (originalSpaceOfNativeIso K B hK (schemeSpace U).obj (schemeSpace U).property).hom ≫ m)
  simp only [Functor.map_comp, Functor.comp_map] at hY
  exact hY

end M9StacksIntegration.AllTestNativeOriginalSchemes
