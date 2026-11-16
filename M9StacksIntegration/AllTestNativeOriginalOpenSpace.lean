module

public import M9StacksIntegration.AllTestNativeOriginalPullbacks
public import M9StacksIntegration.AllTestNativeOriginalAtlas
public import M9StacksIntegration.AllTestOriginalOpenDescent

/-!
# Native open immersions give actual original all-test open immersions

Take the genuine bounded atlas of the actual constructed original target.
Full faithfulness recovers its actual native arrow. The native open predicate
supplies a represented open pullback, and left exactness retains that square
on every original test. Actual original flat-chart descent then proves the
required original representability and open property without assuming either.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

universe u
namespace M9StacksIntegration.AllTestNativeOriginalOpenSpace
open AllTestBoundedCharts AllTestNativeOriginalFunctor AllTestNativeOriginalSchemes
  AllTestNativeOriginalSpace AllTestNativeOriginalPullbacks

variable (K : Type u) [Field K] (B : BigFppfSite.{u})
  (hK : B.Contains (Spec (.of K)))

/-- Every genuine represented original surjective-etale chart is locally
surjective on the full original scheme category. -/
theorem locallySurjective_of_etale_surjective
    {F : M9StandaloneDraft.Presheaves K} (U : M9StandaloneDraft.Schemes K)
    (a : yoneda.obj U ⟶ F)
    (he : (MorphismProperty.inverseImage (@Etale.{u})
      (Over.forget (M9StandaloneDraft.Base K))).presheaf a)
    (hs : (MorphismProperty.inverseImage (@Surjective.{u})
      (Over.forget (M9StandaloneDraft.Base K))).presheaf a) :
    Presheaf.IsLocallySurjective
      (Scheme.fppfTopology.over (M9StandaloneDraft.Base K)) a := by
  have hf : (MorphismProperty.inverseImage (@Flat.{u})
      (Over.forget (M9StandaloneDraft.Base K))).presheaf a := by
    apply MorphismProperty.relative_monotone (F := yoneda) (P' :=
      MorphismProperty.inverseImage (@Flat.{u})
        (Over.forget (M9StandaloneDraft.Base K))) (P :=
      MorphismProperty.inverseImage (@Etale.{u})
        (Over.forget (M9StandaloneDraft.Base K))) _ _ he
    intro A D f hf
    haveI : Etale f.left := hf
    change Flat f.left
    infer_instance
  have hp : (MorphismProperty.inverseImage (@LocallyOfFinitePresentation.{u})
      (Over.forget (M9StandaloneDraft.Base K))).presheaf a := by
    apply MorphismProperty.relative_monotone (F := yoneda) (P' :=
      MorphismProperty.inverseImage (@LocallyOfFinitePresentation.{u})
        (Over.forget (M9StandaloneDraft.Base K))) (P :=
      MorphismProperty.inverseImage (@Etale.{u})
        (Over.forget (M9StandaloneDraft.Base K))) _ _ he
    intro A D f hf
    haveI : Etale f.left := hf
    change LocallyOfFinitePresentation f.left
    infer_instance
  exact AllTestMonoFlatDescent.isLocallySurjective_of_presheaf_fppf K a hf hp hs

/-- Any genuine native represented scheme property implying monomorphic
local finite type and satisfying scheme fppf descent transfers to the
actual original functor map, on every original test scheme. -/
theorem presheafProperty_of_native_mono_lft
    (P : MorphismProperty Scheme.{u}) [P.IsStableUnderBaseChange]
    [P.DescendsAlong (@Surjective ⊓ @Flat ⊓ @LocallyOfFinitePresentation)]
    (hP : P ≤ MorphismProperty.monomorphisms Scheme.{u} ⊓ @LocallyOfFiniteType)
    {X Y : AlgebraicSpaces B (Spec (.of K)) hK} (f : X ⟶ Y)
    (hf : (P.inverseImage (BigFppfOver.toScheme B (Spec (.of K)) hK)).presheaf f.hom) :
    (P.inverseImage (Over.forget (M9StandaloneDraft.Base K))).presheaf
      ((originalPresheafFunctor K B hK).map f) := by
  let E := originalPresheafFunctor K B hK
  letI : E.Full := (originalPresheafFullyFaithful K B hK).full
  obtain ⟨U, a, hae, has⟩ :=
    AllTestNativeOriginalAtlas.exists_bounded_original_atlas K B hK Y.obj Y.property
  let q : schemeSpace U ⟶ Y := E.preimage ((originalSchemeIso K B hK U).hom ≫ a)
  have hq : E.map q = (originalSchemeIso K B hK U).hom ≫ a := E.map_preimage _
  have hc : originalChart K B hK Y U q.hom = a := by
    change (originalSchemeIso K B hK U).inv ≫ E.map q = a
    rw [hq]
    simp
  let V := hf.rep.pullback q.hom
  let b : yoneda.obj V ⟶ X.obj := hf.rep.fst q.hom
  let r : V ⟶ U := hf.rep.snd q.hom
  have hr : P ((BigFppfOver.toScheme B (Spec (.of K)) hK).map r) :=
    hf.property_snd q.hom
  have hp := originalChart_isPullback K B hK f b r q.hom (hf.rep.isPullback q.hom)
  rw [hc] at hp
  haveI : Mono ((boundedInclusion B K hK).map r).left := (hP _ hr).1
  haveI : LocallyOfFiniteType ((boundedInclusion B K hK).map r).left := (hP _ hr).2
  exact AllTestOriginalOpenDescent.presheafProperty_of_mono_lft_chart K P
    (originalSpaceOfNative K B hK X.obj X.property).isSheaf
    (originalSpaceOfNative K B hK Y.obj Y.property).isSheaf
    (E.map f) ((boundedInclusion B K hK).obj U) ((boundedInclusion B K hK).obj V)
    a (locallySurjective_of_etale_surjective K ((boundedInclusion B K hK).obj U) a hae has)
    (originalChart K B hK X V b) ((boundedInclusion B K hK).map r) hp hr

/-- A native open immersion of arbitrary actual algebraic spaces gives a
literal all-original-test open immersion of the actual original functor map.
No original representability, atlas-comparison or open premise is supplied. -/
theorem openImmersion_of_native
    {X Y : AlgebraicSpaces B (Spec (.of K)) hK} (f : X ⟶ Y)
    (hf : Space.IsOpenImmersion B (Spec (.of K)) hK f.hom) :
    M9StandaloneDraft.OpenImmersion K ((originalPresheafFunctor K B hK).map f) := by
  apply presheafProperty_of_native_mono_lft K B hK (@IsOpenImmersion.{u}) _ f hf
  intro U V g hg
  haveI : IsOpenImmersion g := hg
  exact ⟨inferInstance, inferInstance⟩

end M9StacksIntegration.AllTestNativeOriginalOpenSpace
