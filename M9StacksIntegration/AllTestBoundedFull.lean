module

public import M9StacksIntegration.AllTestBoundedFaithful
public import M9StacksIntegration.AllTestLocallySurjectiveDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.FppfMorphismDescent

/-!
# Genuine lifting of bounded maps from original family totals

The original bounded atlas and its actual original kernel pair construct
the descended map. The kernel-pair scheme is bounded by the proved mono
size bound; hence its compatibility is detected by the given bounded map.
Actual sheaf-section descent constructs the map in the original value
universe, and native fppf descent verifies its restriction. Fullness is a
conclusion, not an input. All maps are over the original coefficient field.
-/

set_option autoImplicit false
@[expose] public section
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

namespace M9StacksIntegration.AllTestBoundedFull
open AllTestBoundedCharts AllTestBoundedRestriction AllTestBoundedCartesian
  AllTestBoundedRepresentability AllTestBoundedAlgebraicSpace AllTestBoundedSpaceTargets
  AllTestAtlasDescent AllTestBoundedFaithful
universe u
variable (K : Type u) [Field K] (B : BigFppfSite.{u})
  (hK : B.Contains (Spec (.of K)))

/-- Maps from a bounded represented ORIGINAL source are detected by their
actual bounded chart comparison. -/
theorem chartMap_injective {H : M9StandaloneDraft.Presheaves K}
    (Z : BigFppfOver B (Spec (.of K)) hK)
    {a b : yoneda.obj ((boundedInclusion B K hK).obj Z) ⟶ H}
    (hab : chartMap K B hK Z a = chartMap K B hK Z b) : a = b := by
  have hr : restrictMap K B hK a = restrictMap K B hK b := by
    have he := congrArg (fun m => (restrictRepresentableIso B K hK Z).hom ≫ m) hab
    simpa only [chartMap, Iso.hom_inv_id_assoc] using he
  apply yonedaEquiv.injective
  have he : a.app (op ((boundedInclusion B K hK).obj Z)) =
      b.app (op ((boundedInclusion B K hK).obj Z)) := NatTrans.congr_app hr (op Z)
  exact ConcreteCategory.congr_hom he (𝟙 ((boundedInclusion B K hK).obj Z))

/-- The actual represented chart comparison commutes with precomposition. -/
theorem chartMap_comp_yoneda {H : M9StandaloneDraft.Presheaves K}
    {R Z : BigFppfOver B (Spec (.of K)) hK} (p : R ⟶ Z)
    (a : yoneda.obj ((boundedInclusion B K hK).obj Z) ⟶ H) :
    chartMap K B hK R (yoneda.map ((boundedInclusion B K hK).map p) ≫ a) =
      yoneda.map p ≫ chartMap K B hK Z a := by
  let L := restrictionFunctor K B hK
  have hi : (restrictRepresentableIso B K hK R).inv ≫
      L.map (yoneda.map ((boundedInclusion B K hK).map p)) =
      yoneda.map p ≫ (restrictRepresentableIso B K hK Z).inv := by
    apply (cancel_mono (restrictRepresentableIso B K hK Z).hom).mp
    calc
      ((restrictRepresentableIso B K hK R).inv ≫
          L.map (yoneda.map ((boundedInclusion B K hK).map p))) ≫
          (restrictRepresentableIso B K hK Z).hom =
        (restrictRepresentableIso B K hK R).inv ≫
          (L.map (yoneda.map ((boundedInclusion B K hK).map p)) ≫
            (restrictRepresentableIso B K hK Z).hom) := Category.assoc _ _ _
      _ = (restrictRepresentableIso B K hK R).inv ≫
          ((restrictRepresentableIso B K hK R).hom ≫ yoneda.map p) :=
        congrArg (fun m => (restrictRepresentableIso B K hK R).inv ≫ m)
          (restrictRepresentableIso_naturality K B hK p)
      _ = yoneda.map p := by rw [Iso.inv_hom_id_assoc]
      _ = (yoneda.map p ≫ (restrictRepresentableIso B K hK Z).inv) ≫
          (restrictRepresentableIso B K hK Z).hom := by
        simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  change (restrictRepresentableIso B K hK R).inv ≫
      L.map (yoneda.map ((boundedInclusion B K hK).map p) ≫ a) = _
  rw [L.map_comp, ← Category.assoc, hi, Category.assoc]
  rfl

/-- The actual chart comparison commutes with postcomposition. -/
theorem chartMap_postcomp {F H : M9StandaloneDraft.Presheaves K}
    (Z : BigFppfOver B (Spec (.of K)) hK)
    (a : yoneda.obj ((boundedInclusion B K hK).obj Z) ⟶ F) (d : F ⟶ H) :
    chartMap K B hK Z (a ≫ d) = chartMap K B hK Z a ≫ restrictMap K B hK d := by
  let L := restrictionFunctor K B hK
  change (restrictRepresentableIso B K hK Z).inv ≫ L.map (a ≫ d) =
    ((restrictRepresentableIso B K hK Z).inv ≫ L.map a) ≫ L.map d
  rw [L.map_comp, Category.assoc]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- EVERY map on the bounded restriction of an original family total lifts
uniquely to an actual map on the ENTIRE original test category, into any
original sheaf. No full-faithfulness or effective-descent premise is supplied. -/
theorem existsUnique_lift_restrictMap_from_family
    {T : BigFppfOver B (Spec (.of K)) hK} {g : ℕ}
    (F : M9StandaloneDraft.Family K ((boundedInclusion B K hK).obj T) g)
    (H : M9StandaloneDraft.Presheaves K)
    (hH : Presheaf.IsSheaf (Scheme.fppfTopology.over (M9StandaloneDraft.Base K)) H)
    (n : restrict K B hK F.total.obj ⟶ restrict K B hK H) :
    ∃! d : F.total.obj ⟶ H, restrictMap K B hK d = n := by
  obtain ⟨Z, r, he, hs⟩ := exists_bounded_original_atlas K B hK F
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
      (isAlgebraicSpace_restrict_family K B hK F) hsn hen
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
  exact restrictMap_injective_from_family K B hK F H hH (hdnative'.trans hdnative.symm)

end M9StacksIntegration.AllTestBoundedFull
