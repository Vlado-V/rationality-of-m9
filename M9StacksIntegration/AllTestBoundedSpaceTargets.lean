module

public import M9StacksIntegration.AllTestBoundedAlgebraicSpace

/-!
# Arbitrary original algebraic-space targets on a genuine bounded site

Coarse universality must allow all original algebraic-space targets, not just
schemes or curve-family totals. A site containing an actual original atlas
also contains each represented pullback of that atlas: its scheme is a
monomorphism into the fibre product of two bounded schemes. The monomorphism
is proved from the original all-test cartesian universal property, and the
cutoff is the proved strong-prelimit bound, with no finite-presentation
hypothesis on the diagonal.
-/

@[expose] public section
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace M9StacksIntegration.AllTestBoundedSpaceTargets
open AllTestBoundedCharts AllTestBoundedRestriction AllTestBoundedCartesian
  AllTestBoundedRepresentability AllTestBoundedAlgebraicSpace
universe u
variable (K : Type u) [Field K] (B : BigFppfSite.{u})
  (hK : B.Contains (Spec (.of K)))

/-- An actual represented pullback between two bounded represented sources
has bounded total scheme: its map to their scheme fibre product is mono. -/
theorem represented_pullback_bounded
    {F : M9StandaloneDraft.Presheaves K}
    (U V : BigFppfOver B (Spec (.of K)) hK)
    (f : yoneda.obj ((boundedInclusion B K hK).obj U) ⟶ F)
    (g : yoneda.obj ((boundedInclusion B K hK).obj V) ⟶ F)
    (Z : M9StandaloneDraft.Schemes K)
    (s : Z ⟶ (boundedInclusion B K hK).obj V)
    (r : yoneda.obj Z ⟶ yoneda.obj ((boundedInclusion B K hK).obj U))
    (h : IsPullback r (yoneda.map s) f g) : B.Contains Z.left := by
  let p : Z ⟶ (boundedInclusion B K hK).obj U := yoneda.preimage r
  have hp : yoneda.map p = r := yoneda.map_preimage r
  have w : p.left ≫ ((boundedInclusion B K hK).obj U).hom =
      s.left ≫ ((boundedInclusion B K hK).obj V).hom := (Over.w p).trans (Over.w s).symm
  let t := pullback.lift p.left s.left w
  let : Mono t := by
    constructor
    intro W a b hab
    have ha : a ≫ p.left = b ≫ p.left := by
      simpa only [Category.assoc, t, pullback.lift_fst] using
        congrArg (fun m => m ≫ pullback.fst _ _) hab
    have hb : a ≫ s.left = b ≫ s.left := by
      simpa only [Category.assoc, t, pullback.lift_snd] using
        congrArg (fun m => m ≫ pullback.snd _ _) hab
    let Wk : M9StandaloneDraft.Schemes K := Over.mk (a ≫ Z.hom)
    let ak : Wk ⟶ Z := Over.homMk a rfl
    have hbbase : b ≫ Z.hom = a ≫ Z.hom := by
      calc
        b ≫ Z.hom = (b ≫ p.left) ≫ ((boundedInclusion B K hK).obj U).hom := by
          rw [Category.assoc, Over.w p]
        _ = (a ≫ p.left) ≫ ((boundedInclusion B K hK).obj U).hom := by rw [ha]
        _ = a ≫ Z.hom := by rw [Category.assoc, Over.w p]
    let bk : Wk ⟶ Z := Over.homMk b hbbase
    have hak : ak ≫ p = bk ≫ p := by ext; exact ha
    have hbk : ak ≫ s = bk ≫ s := by ext; exact hb
    have he : ak = bk := by
      apply yoneda.map_injective
      apply h.hom_ext
      · simpa only [← hp, ← Functor.map_comp] using congrArg (fun m => yoneda.map m) hak
      · simpa only [← Functor.map_comp] using congrArg (fun m => yoneda.map m) hbk
    exact congrArg (fun m => m.left) he
  exact Scheme.size_lt_of_mono_of_isStrongPrelimit B.cutoff_isStrongPrelimit t
    (Scheme.size_pullback_lt _ _ U.left.property V.left.property)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The full represented-pullback property of an actual original atlas
restricts, with the same underlying scheme property on every actual bounded
represented pullback. -/
theorem restrict_presheafProperty_representable_source
    (P : MorphismProperty Scheme.{u}) [P.RespectsIso]
    {F : M9StandaloneDraft.Presheaves K}
    (U : BigFppfOver B (Spec (.of K)) hK)
    (f : yoneda.obj ((boundedInclusion B K hK).obj U) ⟶ F)
    (hf : (MorphismProperty.inverseImage P (Over.forget (M9StandaloneDraft.Base K))).presheaf f) :
    (MorphismProperty.inverseImage P (BigFppfOver.toScheme B (Spec (.of K)) hK)).presheaf
      (chartMap K B hK U f) := by
  apply MorphismProperty.relative.of_exists
  intro V g
  let g₀ := sectionMap K B hK V g
  obtain ⟨Z, s, r, h⟩ := hf.rep g₀
  have hZ := represented_pullback_bounded K B hK U V f g₀ Z s r h
  have hs := hf.property g₀ r s h
  rcases Z with ⟨Z, ⟨⟨⟩⟩, Zhom⟩
  let Zn := siteObject B (Spec (.of K)) hK hZ Zhom
  let sn : Zn ⟶ V := boundedPreimage B K hK s
  have hn := representable_isPullback K B hK f sn r g₀ h
  have hn' : IsPullback
      (chartMap K B hK Zn r ≫ (restrictRepresentableIso B K hK U).hom)
      (yoneda.map sn) (chartMap K B hK U f) (chartMap K B hK V g₀) := by
    apply hn.of_iso (Iso.refl _) (restrictRepresentableIso B K hK U)
      (Iso.refl _) (Iso.refl _)
    · simp only [Iso.refl_hom, Category.id_comp]
    · simp only [Iso.refl_hom, Category.comp_id, Category.id_comp]
    · simp only [Iso.refl_hom, Category.comp_id, chartMap, Iso.hom_inv_id_assoc]
    · simp only [Iso.refl_hom, Category.comp_id, Category.id_comp]
  rw [chartMap_sectionMap] at hn'
  exact ⟨Zn, _, sn, hn', hs⟩

/-- Any original algebraic space whose actual atlas is bounded restricts to
an actual native algebraic space. This includes arbitrary coarse-map targets,
not only schemes and family totals. -/
theorem isAlgebraicSpace_restrict_of_bounded_atlas
    (W : M9StandaloneDraft.Space K) (U : M9StandaloneDraft.Schemes K)
    (hU : B.Contains U.left) (a : yoneda.obj U ⟶ W.obj)
    (he : (MorphismProperty.inverseImage (@Etale.{u})
      (Over.forget (M9StandaloneDraft.Base K))).presheaf a)
    (hs : (MorphismProperty.inverseImage (@Surjective.{u})
      (Over.forget (M9StandaloneDraft.Base K))).presheaf a) :
    IsAlgebraicSpace B (Spec (.of K)) hK (restrict K B hK W.obj) := by
  rcases U with ⟨U, ⟨⟨⟩⟩, Uhom⟩
  let Un := siteObject B (Spec (.of K)) hK hU Uhom
  refine ⟨restrict_isSheaf K B hK W.obj W.isSheaf,
    diagonal_restrict K B hK W.obj W.diagonal, Un, chartMap K B hK Un a, ?_, ?_⟩
  · exact restrict_presheafProperty_representable_source K B hK (@Surjective.{u}) Un a hs
  · exact restrict_presheafProperty_representable_source K B hK (@Etale.{u}) Un a he

/-- For EVERY original algebraic-space target and original test scheme,
choose an actual site containing its atlas, field and test. Its restriction
is genuinely algebraic there; no classifier or space-comparison premise is
assumed. -/
theorem exists_site_native_target (W : M9StandaloneDraft.Space K)
    (T : M9StandaloneDraft.Schemes K) :
    ∃ (B : BigFppfSite.{u}) (hK : B.Contains (Spec (.of K))),
      B.Contains T.left ∧ IsAlgebraicSpace B (Spec (.of K)) hK (restrict K B hK W.obj) := by
  obtain ⟨U, a, he, hs⟩ := W.atlas
  obtain ⟨B, hB⟩ := BigFppfSite.exists_containing
    ({Spec (.of K), T.left, U.left} : Set Scheme.{u})
  have hK : B.Contains (Spec (.of K)) := hB _ (by simp)
  exact ⟨B, hK, hB _ (by simp),
    isAlgebraicSpace_restrict_of_bounded_atlas K B hK W U (hB _ (by simp)) a he hs⟩

end M9StacksIntegration.AllTestBoundedSpaceTargets
