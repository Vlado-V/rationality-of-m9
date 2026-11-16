module

public import M9StacksIntegration.AllTestBoundedSpaceTargets
public import M9StacksIntegration.AllTestSingleSchematicCover
public import Mathlib.CategoryTheory.Sites.LocallySurjective

/-!
# Actual atlas descent on the original full test category

Local surjectivity is proved from an actual represented surjective etale
pullback on every original test. Every original curve family over a bounded
base has a bounded ORIGINAL atlas, using its full original cartesian square.
This supports genuine descent of all-test maps, without assuming a family
classification or a fully faithful comparison.
-/

set_option autoImplicit false
@[expose] public section
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

namespace M9StacksIntegration.AllTestAtlasDescent
open AllTestBoundedCharts AllTestBoundedRestriction AllTestBoundedCartesian
universe u
variable (K : Type u) [Field K]

/-- Every actual surjective etale morphism over the original field is an
actual singleton cover on the original full fppf test site. -/
theorem singleton_etale_surjective_cover
    {U T : M9StandaloneDraft.Schemes K} (v : U ⟶ T)
    (hv : Etale v.left) (hs : Surjective v.left) :
    Sieve.ofArrows (fun _ : PUnit.{1} => U) (fun _ => v) ∈
      (Scheme.fppfTopology.over (M9StandaloneDraft.Base K)) T := by
  let : Etale v.left := hv
  let : Surjective v.left := hs
  rw [GrothendieckTopology.mem_over_iff, Sieve.overEquiv_ofArrows]
  apply Precoverage.generate_mem_toGrothendieck
  simpa only [Presieve.ofArrows_pUnit] using v.left.singleton_mem_fppfPrecoverage

/-- The represented-pullback definition of a surjective etale morphism gives
actual local surjectivity at EVERY original test and section. -/
theorem isLocallySurjective_of_presheaf_etale_surjective
    {F G : M9StandaloneDraft.Presheaves K} (f : F ⟶ G)
    (he : (MorphismProperty.inverseImage (@Etale.{u})
      (Over.forget (M9StandaloneDraft.Base K))).presheaf f)
    (hs : (MorphismProperty.inverseImage (@Surjective.{u})
      (Over.forget (M9StandaloneDraft.Base K))).presheaf f) :
    Presheaf.IsLocallySurjective (Scheme.fppfTopology.over (M9StandaloneDraft.Base K)) f := by
  constructor
  intro T x
  let a : yoneda.obj T ⟶ G := yonedaEquiv.symm x
  obtain ⟨Z, s, r, hcart⟩ := he.rep a
  have he' : Etale s.left := he.property a r s hcart
  have hs' : Surjective s.left := hs.property a r s hcart
  have hcover := singleton_etale_surjective_cover K s he' hs'
  apply (Scheme.fppfTopology.over (M9StandaloneDraft.Base K)).superset_covering _ hcover
  rw [Sieve.ofArrows, Sieve.generate_le_iff, Presieve.ofArrows_le_iff]
  intro i
  refine ⟨r.app (op Z) (𝟙 Z), ?_⟩
  have hw := ConcreteCategory.congr_hom (NatTrans.congr_app hcart.w (op Z)) (𝟙 Z)
  change f.app (op Z) (r.app (op Z) (𝟙 Z)) = a.app (op Z) ((𝟙 Z) ≫ s) at hw
  rw [Category.id_comp] at hw
  exact hw.trans (yonedaEquiv_symm_app_apply x (op Z) s)

variable (B : BigFppfSite.{u}) (hK : B.Contains (Spec (.of K)))

/-- A stable original scheme property passes from the base cover to its
actual original chart, retaining the FULL all-test pullback square. -/
theorem original_chart_presheafProperty
    (P : MorphismProperty Scheme.{u}) [MorphismProperty.IsStableUnderBaseChange P]
    {F : M9StandaloneDraft.Presheaves K} {Z U T : M9StandaloneDraft.Schemes K}
    (r : yoneda.obj Z ⟶ F) (π : F ⟶ yoneda.obj T) (q : Z ⟶ U) (v : U ⟶ T)
    (h : IsPullback r (yoneda.map q) π (yoneda.map v)) (hv : P v.left) :
    (MorphismProperty.inverseImage P (Over.forget (M9StandaloneDraft.Base K))).presheaf r := by
  let Q := MorphismProperty.inverseImage P (Over.forget (M9StandaloneDraft.Base K))
  let : MorphismProperty.IsStableUnderBaseChange Q :=
    ⟨fun h hp => MorphismProperty.of_isPullback (P := P)
      (h.map (Over.forget (M9StandaloneDraft.Base K))) hp⟩
  let : MorphismProperty.IsStableUnderBaseChange Q.presheaf :=
    MorphismProperty.relative_isStableUnderBaseChange Q
  have hv' : Q.presheaf (yoneda.map v) :=
    MorphismProperty.relative_map (P := Q) (F := yoneda) hv
  exact MorphismProperty.of_isPullback h.flip hv'

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Every original family over a bounded test has a bounded original atlas
whose etale/surjective clauses hold on the FULL original test site. -/
theorem exists_bounded_original_atlas
    {T : BigFppfOver B (Spec (.of K)) hK} {g : ℕ}
    (F : M9StandaloneDraft.Family K ((boundedInclusion B K hK).obj T) g) :
    ∃ (Z : BigFppfOver B (Spec (.of K)) hK)
      (r : yoneda.obj ((boundedInclusion B K hK).obj Z) ⟶ F.total.obj),
      (MorphismProperty.inverseImage (@Etale.{u})
        (Over.forget (M9StandaloneDraft.Base K))).presheaf r ∧
      (MorphismProperty.inverseImage (@Surjective.{u})
        (Over.forget (M9StandaloneDraft.Base K))).presheaf r := by
  have hT : B.Contains ((boundedInclusion B K hK).obj T).left := T.left.property
  obtain ⟨U, Z, v, q, r, hU, hZ, hv, hs, hcart, hq⟩ :=
    AllTestSingleSchematicCover.exists_bounded_schematic_etale_cover B K
      (T := (boundedInclusion B K hK).obj T) (g := g) hT F
  rcases Z with ⟨Z, ⟨⟨⟩⟩, Zhom⟩
  let Zn := siteObject B (Spec (.of K)) hK hZ Zhom
  exact ⟨Zn, r, original_chart_presheafProperty K (@Etale.{u}) r F.projection q v hcart hv,
    original_chart_presheafProperty K (@Surjective.{u}) r F.projection q v hcart hs⟩

end M9StacksIntegration.AllTestAtlasDescent
