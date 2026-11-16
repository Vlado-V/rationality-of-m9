module

public import M9StacksIntegration.AllTestMonoFlatDescent
public import M9StacksIntegration.AllTestLargeSpaceGeometry

/-!
# Actual large-value monomorphic descent on the full original site

A monomorphism into an original represented sheaf forces every section
type to be small, without any site cutoff or size premise. Shrink the
actual sheaf using that proved fact, transport the actual flat-chart square
through its natural isomorphism, apply actual original-site descent, and
transport the resulting represented functor back. No representability or
all-test comparison hypothesis is introduced.
-/

set_option autoImplicit false
@[expose] public section
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

namespace M9StacksIntegration.AllTestLargeMonoFlatDescent
open AllTestBoundedCharts AllTestLargeSpaceSmallSections AllTestLargeSpaceShrink
  AllTestLargeSpaceGeometry AllTestMonoFlatDescent
universe u
variable (K : Type u) [Field K]

/-- An actual monomorphic subfunctor of an original represented sheaf has
small sections on every original test scheme, with no size assumption. -/
theorem small_obj_of_mono_to_representable
    {A : (M9StandaloneDraft.Schemes K)ᵒᵖ ⥤ Type (u+1)}
    (T : M9StandaloneDraft.Schemes K)
    (f : A ⟶ (largeYoneda K).obj T) [Mono f]
    (W : (M9StandaloneDraft.Schemes K)ᵒᵖ) : Small.{u} (A.obj W) := by
  let : Small.{u} (((largeYoneda K).obj T).obj W) := by
    change Small.{u} (ULift.{u+1} (W.unop ⟶ T))
    infer_instance
  exact small_of_injective (CategoryTheory.injective_of_mono (f.app W))

variable (B : BigFppfSite.{u}) (hK : B.Contains (Spec (.of K)))

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Genuine original all-test monomorphic flat-chart descent, including
the actual Type-(u+1) sheaves constructed by extension from native spaces. -/
theorem isRepresentable_of_single_flat_chart
    {A : (M9StandaloneDraft.Schemes K)ᵒᵖ ⥤ Type (u+1)}
    (hA : Presheaf.IsSheaf (Scheme.fppfTopology.over (M9StandaloneDraft.Base K)) A)
    (T U R : BigFppfOver B (Spec (.of K)) hK) (q : U ⟶ T) (r : R ⟶ U)
    (f : A ⟶ (largeYoneda K).obj ((boundedInclusion B K hK).obj T)) [Mono f]
    (a : (largeYoneda K).obj ((boundedInclusion B K hK).obj R) ⟶ A)
    (h : IsPullback a ((largeYoneda K).map ((boundedInclusion B K hK).map r)) f
      ((largeYoneda K).map ((boundedInclusion B K hK).map q)))
    (hqf : Flat ((BigFppfOver.toScheme B (Spec (.of K)) hK).map q))
    (hqp : LocallyOfFinitePresentation ((BigFppfOver.toScheme B (Spec (.of K)) hK).map q))
    (hqs : Surjective ((BigFppfOver.toScheme B (Spec (.of K)) hK).map q))
    (hrm : Mono ((BigFppfOver.toScheme B (Spec (.of K)) hK).map r))
    (hrl : LocallyOfFiniteType ((BigFppfOver.toScheme B (Spec (.of K)) hK).map r)) :
    A.IsRepresentable := by
  let hsmall := fun W => small_obj_of_mono_to_representable K _ f W
  let G := smallPresheaf K A hsmall
  let e : (valueLift K).obj G ≅ A := smallPresheafIso K A hsmall
  let W := valueLift K
  let : W.Full := (valueLift_fullyFaithful K).full
  let : W.Faithful := (valueLift_fullyFaithful K).faithful
  let fS : G ⟶ yoneda.obj ((boundedInclusion B K hK).obj T) :=
    W.preimage (e.hom ≫ f)
  let aS : yoneda.obj ((boundedInclusion B K hK).obj R) ⟶ G :=
    W.preimage (a ≫ e.inv)
  have hfS : W.map fS = e.hom ≫ f := W.map_preimage _
  have haS : W.map aS = a ≫ e.inv := W.map_preimage _
  have hL : IsPullback (W.map aS)
      (W.map (yoneda.map ((boundedInclusion B K hK).map r))) (W.map fS)
      (W.map (yoneda.map ((boundedInclusion B K hK).map q))) := by
    apply h.of_iso (Iso.refl _) e.symm (Iso.refl _) (Iso.refl _)
    · simpa only [Iso.refl_hom, Iso.symm_hom, Category.id_comp] using haS.symm
    · simp only [Iso.refl_hom, Category.comp_id, Category.id_comp]
      rfl
    · simp only [Iso.refl_hom, Iso.symm_hom, Category.comp_id, hfS,
        Iso.inv_hom_id_assoc]
    · simp only [Iso.refl_hom, Category.comp_id, Category.id_comp]
      rfl
  have hS : IsPullback aS (yoneda.map ((boundedInclusion B K hK).map r)) fS
      (yoneda.map ((boundedInclusion B K hK).map q)) := hL.of_map_of_faithful W
  let : G.IsRepresentable := AllTestMonoFlatDescent.isRepresentable_of_single_flat_chart
    K B hK (smallSheaf K A hA hsmall).property T U R q r fS aS hS
      hqf hqp hqs hrm hrl
  exact isRepresentable_of_natIso (G ⋙ uliftFunctor.{u+1, u}) e

end M9StacksIntegration.AllTestLargeMonoFlatDescent
