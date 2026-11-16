module

public import M9StacksIntegration.AllTestLargeSpaceShrink
public import M9StacksIntegration.AllTestAtlasDescent

/-!
# Actual original algebraic space from large-value all-test geometric data

Universe descent retains the literal original test category and every map.
Representability and the scheme properties of the atlas are reflected through
the actual fully faithful value lift. The diagonal is recovered by its actual
represented-pullback criterion. These are geometric algebraic-space conditions,
with no classifier, coarse existence or family-equivalence hypothesis.
-/

set_option autoImplicit false
@[expose] public section
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

namespace M9StacksIntegration.AllTestLargeSpaceGeometry
open AllTestLargeSpaceSmallSections AllTestLargeSpaceShrink AllTestSheafCoproducts
  AllTestAtlasDescent
universe u
variable (K : Type u) [Field K]

/-- The actual pointwise value-universe lift on the FULL original site. -/
abbrev valueLift : M9StandaloneDraft.Presheaves K ⥤
    (M9StandaloneDraft.Schemes K)ᵒᵖ ⥤ Type (u+1) :=
  (Functor.whiskeringRight _ _ _).obj uliftFunctor.{u+1, u}

/-- Its full faithfulness is the actual ULift full faithfulness. -/
def valueLift_fullyFaithful : (valueLift K).FullyFaithful :=
  fullyFaithfulULiftFunctor.whiskeringRight _

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- A large-value actual surjective etale atlas is locally surjective on
EVERY original test, using the original singleton fppf covers. -/
theorem locallySurjective_of_large_etale_surjective
    {F : (M9StandaloneDraft.Schemes K)ᵒᵖ ⥤ Type (u+1)}
    {Z : M9StandaloneDraft.Schemes K} (a : (largeYoneda K).obj Z ⟶ F)
    (he : (MorphismProperty.inverseImage (@Etale.{u})
      (Over.forget (M9StandaloneDraft.Base K))).relative (largeYoneda K) a)
    (hs : (MorphismProperty.inverseImage (@Surjective.{u})
      (Over.forget (M9StandaloneDraft.Base K))).relative (largeYoneda K) a) :
    Presheaf.IsLocallySurjective (topology K) a := by
  constructor
  intro T x
  let b : (largeYoneda K).obj T ⟶ F := uliftYonedaEquiv.{u+1}.symm x
  obtain ⟨R, s, r, hR⟩ := he.rep b
  have he' : Etale s.left := he.property b r s hR
  have hs' : Surjective s.left := hs.property b r s hR
  have hcover := singleton_etale_surjective_cover K s he' hs'
  apply (topology K).superset_covering _ hcover
  rw [Sieve.ofArrows, Sieve.generate_le_iff, Presieve.ofArrows_le_iff]
  intro i
  refine ⟨r.app (op R) (ULift.up (𝟙 R)), ?_⟩
  have hw := congrArg (fun t : (largeYoneda K).obj R ⟶ F => uliftYonedaEquiv.{u+1} t) hR.w
  change a.app (op R) (r.app (op R) (ULift.up (𝟙 R))) = F.map ((𝟙 R) ≫ s).op x at hw
  simpa only [Category.id_comp] using hw

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Actual relative representability and actual scheme properties reflect
through the value-universe comparison, for every represented original test. -/
theorem presheafProperty_of_large
    (P : MorphismProperty (M9StandaloneDraft.Schemes K)) [P.RespectsIso]
    (G : M9StandaloneDraft.Presheaves K)
    (F : (M9StandaloneDraft.Schemes K)ᵒᵖ ⥤ Type (u+1))
    (e : (valueLift K).obj G ≅ F) {Z : M9StandaloneDraft.Schemes K}
    (a : yoneda.obj Z ⟶ G) (aL : (largeYoneda K).obj Z ⟶ F)
    (heq : (valueLift K).map a ≫ e.hom = aL)
    (ha : P.relative (largeYoneda K) aL) : P.presheaf a := by
  let W := valueLift K
  let : W.Full := (valueLift_fullyFaithful K).full
  let : W.Faithful := (valueLift_fullyFaithful K).faithful
  apply MorphismProperty.relative.of_exists
  intro T g
  let gL : (largeYoneda K).obj T ⟶ F := W.map g ≫ e.hom
  obtain ⟨R, s, r, hR⟩ := ha.rep gL
  let p : R ⟶ Z := (largeYoneda K).preimage r
  have hp : (largeYoneda K).map p = r := (largeYoneda K).map_preimage r
  have hpW : W.map (yoneda.map p) = r := hp
  have ha' : aL ≫ e.inv = W.map a := by
    rw [← heq, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  have hm : IsPullback (W.map (yoneda.map p)) (W.map (yoneda.map s)) (W.map a) (W.map g) := by
    apply hR.of_iso (Iso.refl _) (Iso.refl _) (Iso.refl _) e.symm
    · simpa only [Iso.refl_hom, Category.comp_id, Category.id_comp] using hpW.symm
    · simp only [Iso.refl_hom, Category.comp_id, Category.id_comp]
      rfl
    · simpa only [Iso.symm_hom, Iso.refl_hom, Category.id_comp] using ha'
    · change (W.map g ≫ e.hom) ≫ e.inv = 𝟙 _ ≫ W.map g
      simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id, Category.id_comp]
  exact ⟨R, yoneda.map p, s, hm.of_map_of_faithful W, ha.property gL r s hR⟩

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- An ACTUAL large-value original algebraic space gives an ACTUAL original
Type-u-valued algebraic space on every original test. All section-size,
sheaf and geometric conditions are proved; no small-universe sheafification
or moduli classification is an argument. -/
def originalSpaceOfLargeAtlas
    (F : (M9StandaloneDraft.Schemes K)ᵒᵖ ⥤ Type (u+1))
    (hF : Presheaf.IsSheaf (topology K) F)
    (hdiag : (largeYoneda K).relativelyRepresentable (diag F))
    (Z : M9StandaloneDraft.Schemes K) (a : (largeYoneda K).obj Z ⟶ F)
    (he : (MorphismProperty.inverseImage (@Etale.{u})
      (Over.forget (M9StandaloneDraft.Base K))).relative (largeYoneda K) a)
    (hs : (MorphismProperty.inverseImage (@Surjective.{u})
      (Over.forget (M9StandaloneDraft.Base K))).relative (largeYoneda K) a) :
    M9StandaloneDraft.Space K := by
  let hloc := locallySurjective_of_large_etale_surjective K a he hs
  let hsmall := fun T : (M9StandaloneDraft.Schemes K)ᵒᵖ => small_obj_of_atlas K F hF Z a he.rep hloc T.unop
  let G := smallPresheaf K F hsmall
  let e : (valueLift K).obj G ≅ F := smallPresheafIso K F hsmall
  let W := valueLift K
  let : W.Full := (valueLift_fullyFaithful K).full
  let : W.Faithful := (valueLift_fullyFaithful K).faithful
  let aS : yoneda.obj Z ⟶ G := W.preimage (a ≫ e.inv)
  have hea : W.map aS ≫ e.hom = a := by
    rw [Functor.map_preimage]
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  refine { obj := G
           isSheaf := (smallSheaf K F hF hsmall).property
           diagonal := ?_
           atlas := ⟨Z, aS,
             presheafProperty_of_large K _ G F e aS a hea he,
             presheafProperty_of_large K _ G F e aS a hea hs⟩ }
  apply Functor.relativelyRepresentable.diag_of_map_from_obj
  intro T b
  let bL : (largeYoneda K).obj T ⟶ F := W.map b ≫ e.hom
  have hb : (largeYoneda K).relativelyRepresentable bL :=
    Functor.relativelyRepresentable.of_diag hdiag bL
  have hbtop : (⊤ : MorphismProperty (M9StandaloneDraft.Schemes K)).relative
      (largeYoneda K) bL := ⟨hb, by intros; trivial⟩
  exact (presheafProperty_of_large K ⊤ G F e b bL rfl hbtop).rep

/-- The constructed original space is the SAME full-test presheaf after the
actual universe lift, by a natural isomorphism on every test and map. -/
def originalSpaceOfLargeAtlasIso
    (F : (M9StandaloneDraft.Schemes K)ᵒᵖ ⥤ Type (u+1))
    (hF : Presheaf.IsSheaf (topology K) F)
    (hdiag : (largeYoneda K).relativelyRepresentable (diag F))
    (Z : M9StandaloneDraft.Schemes K) (a : (largeYoneda K).obj Z ⟶ F)
    (he : (MorphismProperty.inverseImage (@Etale.{u})
      (Over.forget (M9StandaloneDraft.Base K))).relative (largeYoneda K) a)
    (hs : (MorphismProperty.inverseImage (@Surjective.{u})
      (Over.forget (M9StandaloneDraft.Base K))).relative (largeYoneda K) a) :
    (valueLift K).obj (originalSpaceOfLargeAtlas K F hF hdiag Z a he hs).obj ≅ F :=
  smallPresheafIso K F (fun T => small_obj_of_atlas K F hF Z a he.rep
    (locallySurjective_of_large_etale_surjective K a he hs) T.unop)

end M9StacksIntegration.AllTestLargeSpaceGeometry
