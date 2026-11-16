module

public import M9StacksIntegration.AllTestBoundedFull

/-!
# Genuine full map descent from every original bounded-atlas space

This generalizes the already checked family-total proofs to any literal
original algebraic space with an actual atlas in the site. The original
represented relation is bounded by its monomorphism into the product of
two copies of the atlas. Original sheaf-section descent constructs maps
on ALL original test schemes, and actual native fppf descent verifies
their restriction. No family, full-faithfulness or classifier premise.
-/

set_option autoImplicit false
@[expose] public section
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

namespace M9StacksIntegration.AllTestBoundedAtlasFull
open AllTestBoundedCharts AllTestBoundedRestriction AllTestBoundedCartesian
  AllTestBoundedRepresentability AllTestBoundedAlgebraicSpace AllTestBoundedSpaceTargets
  AllTestAtlasDescent AllTestBoundedFull
universe u
variable (K : Type u) [Field K] (B : BigFppfSite.{u})
  (hK : B.Contains (Spec (.of K)))

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Equality on bounded tests detects actual maps from an original space
with an actual bounded atlas into EVERY original sheaf. -/
theorem restrictMap_injective_of_bounded_atlas
    (W : M9StandaloneDraft.Space K)
    (Z : BigFppfOver B (Spec (.of K)) hK)
    (r : yoneda.obj ((boundedInclusion B K hK).obj Z) ⟶ W.obj)
    (he : (MorphismProperty.inverseImage (@Etale.{u})
      (Over.forget (M9StandaloneDraft.Base K))).presheaf r)
    (hs : (MorphismProperty.inverseImage (@Surjective.{u})
      (Over.forget (M9StandaloneDraft.Base K))).presheaf r)
    (H : M9StandaloneDraft.Presheaves K)
    (hH : Presheaf.IsSheaf (Scheme.fppfTopology.over (M9StandaloneDraft.Base K)) H)
    {a b : W.obj ⟶ H} (hab : restrictMap K B hK a = restrictMap K B hK b) : a = b := by
  let J := Scheme.fppfTopology.over (M9StandaloneDraft.Base K)
  let Fs : Sheaf J (Type u) := ⟨W.obj, W.isSheaf⟩
  let Hs : Sheaf J (Type u) := ⟨H, hH⟩
  let rs : J.yoneda.obj ((boundedInclusion B K hK).obj Z) ⟶ Fs := ⟨r⟩
  let as' : Fs ⟶ Hs := ⟨a⟩
  let bs' : Fs ⟶ Hs := ⟨b⟩
  let : Presheaf.IsLocallySurjective J r :=
    isLocallySurjective_of_presheaf_etale_surjective K r he hs
  let : Sheaf.IsLocallySurjective rs := inferInstanceAs (Presheaf.IsLocallySurjective J r)
  have hpre : r ≫ a = r ≫ b := by
    apply yonedaEquiv.injective
    have hx := ConcreteCategory.congr_hom (NatTrans.congr_app hab (op Z))
      (r.app (op ((boundedInclusion B K hK).obj Z)) (𝟙 _))
    exact hx
  have hs' : rs ≫ as' = rs ≫ bs' := by
    apply ObjectProperty.hom_ext
    exact hpre
  have hab' : as' = bs' := (cancel_epi rs).mp hs'
  exact congrArg (fun f => f.hom) hab'

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Every bounded map from an original bounded-atlas space to any original
sheaf extends uniquely to ALL original tests. -/
theorem existsUnique_lift_restrictMap_of_bounded_atlas
    (W : M9StandaloneDraft.Space K)
    (Z : BigFppfOver B (Spec (.of K)) hK)
    (r : yoneda.obj ((boundedInclusion B K hK).obj Z) ⟶ W.obj)
    (he : (MorphismProperty.inverseImage (@Etale.{u})
      (Over.forget (M9StandaloneDraft.Base K))).presheaf r)
    (hs : (MorphismProperty.inverseImage (@Surjective.{u})
      (Over.forget (M9StandaloneDraft.Base K))).presheaf r)
    (H : M9StandaloneDraft.Presheaves K)
    (hH : Presheaf.IsSheaf (Scheme.fppfTopology.over (M9StandaloneDraft.Base K)) H)
    (n : restrict K B hK W.obj ⟶ restrict K B hK H) :
    ∃! d : W.obj ⟶ H, restrictMap K B hK d = n := by
  let rn := chartMap K B hK Z r
  let a := sectionMap K B hK Z (rn ≫ n)
  obtain ⟨R, s, t, hR⟩ := he.rep r
  have hRb := represented_pullback_bounded K B hK Z Z r r R s t hR
  rcases R with ⟨R, ⟨⟨⟩⟩, Rhom⟩
  let Rn := siteObject B (Spec (.of K)) hK hRb Rhom
  let p := yoneda.preimage t
  have hp : yoneda.map p = t := yoneda.map_preimage t
  let pn : Rn ⟶ Z := boundedPreimage B K hK p
  let sn : Rn ⟶ Z := boundedPreimage B K hK s
  have hw : yoneda.map p ≫ r = yoneda.map s ≫ r := by rw [hp]; exact hR.w
  have hcp : chartMap K B hK Rn (yoneda.map p ≫ r) = yoneda.map pn ≫ rn :=
    chartMap_comp_yoneda K B hK pn r
  have hcs : chartMap K B hK Rn (yoneda.map s ≫ r) = yoneda.map sn ≫ rn :=
    chartMap_comp_yoneda K B hK sn r
  have hn : yoneda.map pn ≫ rn = yoneda.map sn ≫ rn :=
    hcp.symm.trans ((congrArg (fun m => chartMap K B hK Rn m) hw).trans hcs)
  have ha : t ≫ a = yoneda.map s ≫ a := by
    have hcpa : chartMap K B hK Rn (yoneda.map p ≫ a) =
        yoneda.map pn ≫ chartMap K B hK Z a := chartMap_comp_yoneda K B hK pn a
    have hcsa : chartMap K B hK Rn (yoneda.map s ≫ a) =
        yoneda.map sn ≫ chartMap K B hK Z a := chartMap_comp_yoneda K B hK sn a
    have hca : chartMap K B hK Z a = rn ≫ n := chartMap_sectionMap K B hK Z _
    have hleft : chartMap K B hK Rn (t ≫ a) = yoneda.map pn ≫ rn ≫ n :=
      (congrArg (fun m => chartMap K B hK Rn (m ≫ a)) hp.symm).trans
        (hcpa.trans (congrArg (fun m => yoneda.map pn ≫ m) hca))
    have hright : chartMap K B hK Rn (yoneda.map s ≫ a) = yoneda.map sn ≫ rn ≫ n :=
      hcsa.trans (congrArg (fun m => yoneda.map sn ≫ m) hca)
    have heq : yoneda.map pn ≫ rn ≫ n = yoneda.map sn ≫ rn ≫ n := by
      simpa only [Category.assoc] using congrArg (fun m => m ≫ n) hn
    exact chartMap_injective K B hK Rn (hleft.trans (heq.trans hright.symm))
  let J := Scheme.fppfTopology.over (M9StandaloneDraft.Base K)
  let : Presheaf.IsLocallySurjective J r :=
    isLocallySurjective_of_presheaf_etale_surjective K r he hs
  obtain ⟨d, hd⟩ := AllTestLocallySurjectiveDescent.exists_desc_of_isPullback J r hH a
    t (yoneda.map s) hR ha
  have hdnative : restrictMap K B hK d = n := by
    have hen := restrict_presheafProperty_representable_source K B hK (@Etale.{u}) Z r he
    have hsn := restrict_presheafProperty_representable_source K B hK (@Surjective.{u}) Z r hs
    have hcover := Space.isFppfCovering_atlas.{u, 0} B (Spec (.of K)) hK
      (isAlgebraicSpace_restrict_of_bounded_atlas K B hK W
        ((boundedInclusion B K hK).obj Z) Z.left.property r he hs) hsn hen
    apply Space.hom_ext_of_isFppfCovering B (Spec (.of K)) hK
      (fun _ : PUnit.{1} => yoneda.obj Z) (fun _ => rn) hcover
      (restrict_isSheaf K B hK H hH)
    intro i
    calc
      rn ≫ restrictMap K B hK d = chartMap K B hK Z (r ≫ d) :=
        (chartMap_postcomp K B hK Z r d).symm
      _ = chartMap K B hK Z a := congrArg (fun m => chartMap K B hK Z m) hd
      _ = rn ≫ n := chartMap_sectionMap K B hK Z _
  refine ⟨d, hdnative, ?_⟩
  intro d' hdnative'
  exact restrictMap_injective_of_bounded_atlas K B hK W Z r he hs H hH (hdnative'.trans hdnative.symm)

end M9StacksIntegration.AllTestBoundedAtlasFull
