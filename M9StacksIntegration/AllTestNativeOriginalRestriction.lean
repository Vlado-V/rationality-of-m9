module

public import M9StacksIntegration.AllTestNativeOriginalSpace
public import StacksFrontier.CategoryTheory.Sites.Cocontinuous.MorphismsOfTopoi

/-!
# The constructed original space restricts to the SAME native space

The actual original full-site inclusion is proved continuous,
cocontinuous and fully faithful. Right Kan extensions exist in the actual
Type-(u+1) universe. The native full-faithfulness theorem therefore applies
to the actual sheaf extension; its actual adjunction unit is an isomorphism.
Composing that unit with the proved original-space universe isomorphism
identifies the restriction with the ORIGINAL native algebraic-space sheaf.
No site-equivalence, classification or fullness premise is supplied.
-/

set_option autoImplicit false
@[expose] public section
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

namespace M9StacksIntegration.AllTestNativeOriginalRestriction
open AllTestBoundedCharts AllTestLargeSitePullback AllTestSiteCocontinuity
  AllTestNativeOriginalSpace AllTestNativeSpacePresentation AllTestLargeSpaceGeometry
universe u
variable (K : Type u) [Field K] (B : BigFppfSite.{u})
  (hK : B.Contains (Spec (.of K)))

/-- Actual full faithfulness of the constructed extension, proved from the
actual original-site inclusion and its actual fppf cover refinements. -/
theorem extendSheaf_full_and_faithful :
    (extendSheaf K B hK).Full ∧ (extendSheaf K B hK).Faithful := by
  let : (boundedInclusion B K hK).IsCocontinuous
      (BigFppfOver.topology B (Spec (.of K)) hK)
      (Scheme.fppfTopology.over (M9StandaloneDraft.Base K)) :=
    boundedInclusion_isCocontinuous K B hK
  let : ∀ F : (BigFppfOver B (Spec (.of K)) hK)ᵒᵖ ⥤ Type (u+1),
      (boundedInclusion B K hK).op.HasPointwiseRightKanExtension F := by
    intro F T
    change HasLimit (StructuredArrow.proj T (boundedInclusion B K hK).op ⋙ F)
    infer_instance
  exact Functor.full_and_faithful_sheafPullback (boundedInclusion B K hK)
    (Type (u+1)) (BigFppfOver.topology B (Spec (.of K)) hK)
    (Scheme.fppfTopology.over (M9StandaloneDraft.Base K))

/-- The actual fully faithful structure, as data rather than an assumption. -/
def extendSheafFullyFaithful : (extendSheaf K B hK).FullyFaithful := by
  let h := extendSheaf_full_and_faithful K B hK
  let : (extendSheaf K B hK).Full := h.1
  let : (extendSheaf K B hK).Faithful := h.2
  exact Functor.FullyFaithful.ofFullyFaithful _

/-- The actual extension followed by literal original-test restriction
recovers every native sheaf, naturally. -/
def extensionUnitIso :
    𝟭 (Sheaf (BigFppfOver.topology B (Spec (.of K)) hK) (Type (u+1))) ≅
      extendSheaf K B hK ⋙ (boundedInclusion B K hK).sheafPushforwardContinuous
        (Type (u+1)) (BigFppfOver.topology B (Spec (.of K)) hK)
        (Scheme.fppfTopology.over (M9StandaloneDraft.Base K)) := by
  let : (extendSheaf K B hK).Full := (extendSheafFullyFaithful K B hK).full
  let : (extendSheaf K B hK).Faithful := (extendSheafFullyFaithful K B hK).faithful
  exact asIso (extendSheafAdjunction K B hK).unit

/-- The constructed original space, restricted to the native tests and
lifted in value universe, is naturally the SAME original native space. -/
def originalNativeRestrictionIso
    (F : (BigFppfOver B (Spec (.of K)) hK)ᵒᵖ ⥤ Type u)
    (hF : IsAlgebraicSpace B (Spec (.of K)) hK F) :
    (boundedInclusion B K hK).op ⋙
        (valueLift K).obj (originalSpaceOfNative K B hK F hF).obj ≅
      F ⋙ uliftFunctor.{u+1, u} :=
  Functor.isoWhiskerLeft (boundedInclusion B K hK).op (originalSpaceOfNativeIso K B hK F hF) ≪≫
    ((sheafToPresheaf (BigFppfOver.topology B (Spec (.of K)) hK) (Type (u+1))).mapIso
      ((extensionUnitIso K B hK).app (nativeLargeSheaf K B hK ⟨F, hF.isSheaf⟩))).symm

end M9StacksIntegration.AllTestNativeOriginalRestriction
