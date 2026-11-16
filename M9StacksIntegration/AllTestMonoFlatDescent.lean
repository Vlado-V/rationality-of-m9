module

public import M9StacksIntegration.AllTestBoundedMonoRepresentability
public import StacksFrontier.AlgebraicGeometry.Descent.QuasiAffineFlatChartDescent
public import StacksFrontier.AlgebraicGeometry.Descent.FlatChartDescent

/-!
# Genuine monomorphic flat-chart descent on the full original site

The native effective-descent theorem at monomorphisms locally of finite
type has its geometric input proved. We apply that theorem to the actual
bounded restriction of an original sheaf, then lift the resulting scheme
and map by literal Yoneda evaluation. The actual ORIGINAL fppf chart proves
that the lifted map is an isomorphism on every original test scheme.
No full-test representability, classification or effective-descent premise
is assumed in the result.
-/

set_option autoImplicit false
@[expose] public section
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

namespace M9StacksIntegration.AllTestMonoFlatDescent
open AllTestBoundedCharts AllTestBoundedRestriction AllTestBoundedCartesian
  AllTestBoundedFull AllTestBoundedMonoRepresentability AllTestAtlasDescent
universe u
variable (K : Type u) [Field K]

/-- An actual original singleton fppf cover belongs to the original site. -/
theorem singleton_fppf_cover {U T : M9StandaloneDraft.Schemes K} (v : U ⟶ T)
    (hv : Flat v.left) (hp : LocallyOfFinitePresentation v.left)
    (hs : Surjective v.left) :
    Sieve.ofArrows (fun _ : PUnit.{1} => U) (fun _ => v) ∈
      (Scheme.fppfTopology.over (M9StandaloneDraft.Base K)) T := by
  let : Flat v.left := hv
  let : LocallyOfFinitePresentation v.left := hp
  let : Surjective v.left := hs
  rw [GrothendieckTopology.mem_over_iff, Sieve.overEquiv_ofArrows]
  apply Precoverage.generate_mem_toGrothendieck
  simpa only [Presieve.ofArrows_pUnit] using v.left.singleton_mem_fppfPrecoverage

/-- Actual represented surjective flat finite-presentation charts are locally
surjective on ALL original test schemes, without a small-site hypothesis. -/
theorem isLocallySurjective_of_presheaf_fppf
    {F G : M9StandaloneDraft.Presheaves K} (f : F ⟶ G)
    (hf : (MorphismProperty.inverseImage (@Flat.{u})
      (Over.forget (M9StandaloneDraft.Base K))).presheaf f)
    (hp : (MorphismProperty.inverseImage (@LocallyOfFinitePresentation.{u})
      (Over.forget (M9StandaloneDraft.Base K))).presheaf f)
    (hs : (MorphismProperty.inverseImage (@Surjective.{u})
      (Over.forget (M9StandaloneDraft.Base K))).presheaf f) :
    Presheaf.IsLocallySurjective (Scheme.fppfTopology.over (M9StandaloneDraft.Base K)) f := by
  constructor
  intro T x
  let a : yoneda.obj T ⟶ G := yonedaEquiv.symm x
  obtain ⟨Z, s, r, hcart⟩ := hf.rep a
  have hf' : Flat s.left := hf.property a r s hcart
  have hp' : LocallyOfFinitePresentation s.left := hp.property a r s hcart
  have hs' : Surjective s.left := hs.property a r s hcart
  have hcover := singleton_fppf_cover K s hf' hp' hs'
  apply (Scheme.fppfTopology.over (M9StandaloneDraft.Base K)).superset_covering _ hcover
  rw [Sieve.ofArrows, Sieve.generate_le_iff, Presieve.ofArrows_le_iff]
  intro i
  refine ⟨r.app (op Z) (𝟙 Z), ?_⟩
  have hw := ConcreteCategory.congr_hom (NatTrans.congr_app hcart.w (op Z)) (𝟙 Z)
  change f.app (op Z) (r.app (op Z) (𝟙 Z)) = a.app (op Z) ((𝟙 Z) ≫ s) at hw
  rw [Category.id_comp] at hw
  exact hw.trans (yonedaEquiv_symm_app_apply x (op Z) s)

variable (B : BigFppfSite.{u}) (hK : B.Contains (Spec (.of K)))

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- An actual original sheaf with an actual monomorphic locally-finite-type
scheme chart over one original fppf covering is represented by an ORIGINAL
scheme, on the FULL original test category. -/
theorem isRepresentable_of_single_flat_chart
    {A : M9StandaloneDraft.Presheaves K}
    (hA : Presheaf.IsSheaf (Scheme.fppfTopology.over (M9StandaloneDraft.Base K)) A)
    (T U R : BigFppfOver B (Spec (.of K)) hK) (q : U ⟶ T) (r : R ⟶ U)
    (f : A ⟶ yoneda.obj ((boundedInclusion B K hK).obj T))
    (a : yoneda.obj ((boundedInclusion B K hK).obj R) ⟶ A)
    (h : IsPullback a (yoneda.map ((boundedInclusion B K hK).map r)) f
      (yoneda.map ((boundedInclusion B K hK).map q)))
    (hqf : Flat ((BigFppfOver.toScheme B (Spec (.of K)) hK).map q))
    (hqp : LocallyOfFinitePresentation ((BigFppfOver.toScheme B (Spec (.of K)) hK).map q))
    (hqs : Surjective ((BigFppfOver.toScheme B (Spec (.of K)) hK).map q))
    (hrm : Mono ((BigFppfOver.toScheme B (Spec (.of K)) hK).map r))
    (hrl : LocallyOfFiniteType ((BigFppfOver.toScheme B (Spec (.of K)) hK).map r)) :
    A.IsRepresentable := by
  let Q : MorphismProperty Scheme.{u} :=
    MorphismProperty.monomorphisms Scheme.{u} ⊓ @LocallyOfFiniteType
  let : HasPullbacks ((BigFppfOver B (Spec (.of K)) hK)ᵒᵖ ⥤ Type u) :=
    functorCategoryHasLimitsOfShape (J := WalkingCospan) (C := Type u)
      (K := (BigFppfOver B (Spec (.of K)) hK)ᵒᵖ)
  let fN := baseMap K B hK T f
  let : HasPullback fN (yoneda.map q) :=
    (functorCategoryHasLimitsOfShape (J := WalkingCospan) (C := Type u)
      (K := (BigFppfOver B (Spec (.of K)) hK)ᵒᵖ)).has_limit
        (cospan fN (yoneda.map q))
  have hV : (Q.inverseImage (BigFppfOver.toScheme B (Spec (.of K)) hK)).presheaf
      (pullback.snd fN (yoneda.map q)) :=
    Space.presheaf_pullback_snd_of_isPullback (P := Q)
      (chart_isPullback K B hK r q a f h) ⟨hrm, hrl⟩
  have hN : (Q.inverseImage (BigFppfOver.toScheme B (Spec (.of K)) hK)).presheaf fN :=
    Space.presheaf_of_surjectiveFlatChart_of_coveringSieveDescent
      (Space.isEffectiveDescentAlongCoveringSieve_monomorphisms_inf_lft
        B (Spec (.of K)) hK)
      (restrict_isSheaf K B hK A hA)
      (((BigFppfOver.topology B (Spec (.of K)) hK).yoneda.obj T).property)
      ((BigFppfOver.presheaf_inverseImage_yoneda_map_iff B (Spec (.of K)) hK _ q).2 hqs)
      ((BigFppfOver.presheaf_inverseImage_yoneda_map_iff B (Spec (.of K)) hK _ q).2 hqf)
      ((BigFppfOver.presheaf_inverseImage_yoneda_map_iff B (Spec (.of K)) hK _ q).2 hqp) hV
  let Z := hN.rep.pullback (𝟙 (yoneda.obj T))
  let β : yoneda.obj Z ⟶ restrict K B hK A := hN.rep.fst (𝟙 _)
  let z : Z ⟶ T := hN.rep.snd (𝟙 _)
  have hZ : IsPullback β (yoneda.map z) fN (𝟙 _) := hN.rep.isPullback _
  let : IsIso β := hZ.isIso_fst_of_isIso
  let b : yoneda.obj ((boundedInclusion B K hK).obj Z) ⟶ A :=
    liftChartMap K B hK Z β
  have hb : chartMap K B hK Z b = β := chartMap_liftChartMap K B hK Z β
  let : IsIso (chartMap K B hK Z b) := hb.symm ▸ inferInstance
  have hc : b ≫ f = yoneda.map ((boundedInclusion B K hK).map z) := by
    apply chartMap_injective K B hK Z
    apply (cancel_mono (restrictRepresentableIso B K hK T).hom).mp
    rw [chartMap_postcomp, Category.assoc]
    change chartMap K B hK Z b ≫ fN =
      chartMap K B hK Z (yoneda.map ((boundedInclusion B K hK).map z)) ≫
        (restrictRepresentableIso B K hK T).hom
    rw [hb, chartMap_yoneda_map]
    simpa using hZ.w
  have hz : Q ((BigFppfOver.toScheme B (Spec (.of K)) hK).map z) :=
    hN.property_snd (𝟙 _)
  let : Mono ((boundedInclusion B K hK).map z) :=
    (Over.forget (M9StandaloneDraft.Base K)).mono_of_mono_map hz.1
  let : Mono (b ≫ f) := hc.symm ▸ (inferInstanceAs
    (Mono (yoneda.map ((boundedInclusion B K hK).map z))))
  let : Mono b := by
    constructor
    intro W α β hαβ
    apply (cancel_mono (b ≫ f)).mp
    simpa only [Category.assoc] using congrArg (fun m => m ≫ f) hαβ
  have ha : Presheaf.IsLocallySurjective
      (Scheme.fppfTopology.over (M9StandaloneDraft.Base K)) a :=
    isLocallySurjective_of_presheaf_fppf K a
      (original_chart_presheafProperty K (@Flat.{u}) a f
        ((boundedInclusion B K hK).map r) ((boundedInclusion B K hK).map q) h hqf)
      (original_chart_presheafProperty K (@LocallyOfFinitePresentation.{u}) a f
        ((boundedInclusion B K hK).map r) ((boundedInclusion B K hK).map q) h hqp)
      (original_chart_presheafProperty K (@Surjective.{u}) a f
        ((boundedInclusion B K hK).map r) ((boundedInclusion B K hK).map q) h hqs)
  let : IsIso b := isIso_of_chartMap_isIso_of_mono K B hK hA Z b R a ha
  exact Functor.IsRepresentable.mk' (asIso b)

end M9StacksIntegration.AllTestMonoFlatDescent
