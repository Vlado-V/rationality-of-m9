module

public import M9StacksIntegration.AllTestPresentationDiagonal
public import Mathlib.CategoryTheory.MorphismProperty.Descent

/-!
# Actual scheme properties of an original all-test atlas

The actual represented fibre product of the chart with an arbitrary
original test is covered, via the proved original single-fppf-lift theorem,
by the actual base change of the relation's second projection. The ordinary
scheme property descends along that actual original fppf cover. Thus the
atlas is relatively representable with surjectivity/etaleness, once the
diagonal has been PROVED represented. No all-test comparison premise occurs.
-/

set_option autoImplicit false
@[expose] public section
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

namespace M9StacksIntegration.AllTestPresentationAtlas
open AllTestLargeSpaceSmallSections AllTestSheafCoproducts
universe u
variable (K : Type u) [Field K]
local notation "Yₖ" => (largeYoneda K)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Every actual represented atlas base change has the scheme property of
the relation projection, by ordinary fppf descent on original schemes. -/
theorem atlas_presheafProperty_of_presentation
    (P : MorphismProperty Scheme.{u}) [P.IsStableUnderBaseChange]
    [P.DescendsAlong (@Surjective ⊓ @Flat ⊓ @LocallyOfFinitePresentation)]
    {F : (M9StandaloneDraft.Schemes K)ᵒᵖ ⥤ Type (u+1)}
    (hF : Presheaf.IsSheaf (topology K) F)
    (U R : M9StandaloneDraft.Schemes K) (s t : R ⟶ U)
    (a : (Yₖ).obj U ⟶ F)
    (ha : Presheaf.IsLocallySurjective (topology K) a)
    (hker : IsPullback ((Yₖ).map s) ((Yₖ).map t) a a)
    (hdiag : (Yₖ).relativelyRepresentable (diag F)) (hP : P t.left) :
    (P.inverseImage (Over.forget (M9StandaloneDraft.Base K))).relative (Yₖ) a := by
  let : HasBinaryProducts (M9StandaloneDraft.Schemes K) :=
    hasBinaryProducts_of_hasTerminal_and_pullbacks _
  let : HasPullbacks ((M9StandaloneDraft.Schemes K)ᵒᵖ ⥤ Type (u+1)) :=
    functorCategoryHasLimitsOfShape (J := WalkingCospan) (C := Type (u+1))
      (K := (M9StandaloneDraft.Schemes K)ᵒᵖ)
  let Q := P.inverseImage (Over.forget (M9StandaloneDraft.Base K))
  apply MorphismProperty.relative.of_exists
  intro T b
  obtain ⟨Z, π, ρ, hZ⟩ := hdiag.of_diag a b
  let ρS : Z ⟶ U := (Yₖ).preimage ρ
  have hρ : (Yₖ).map ρS = ρ := (Yₖ).map_preimage _
  have hZ' : IsPullback ((Yₖ).map ρS) ((Yₖ).map π) a b := by rw [hρ]; exact hZ
  obtain ⟨V, q, v, hqf, hqp, hqs, he⟩ :=
    AllTestSingleFppfLift.exists_single_fppf_lift K hF U T a ha b
  let W := pullback t v
  let k : W ⟶ R := pullback.fst t v
  let r : W ⟶ V := pullback.snd t v
  have hOuter : IsPullback ((Yₖ).map k ≫ (Yₖ).map s) ((Yₖ).map r)
      a ((Yₖ).map q ≫ b) := by
    have h := ((IsPullback.of_hasPullback t v).map (Yₖ)).paste_horiz hker
    simpa only [he] using h
  let β : (Yₖ).obj W ⟶ (Yₖ).obj Z := hZ'.lift
    ((Yₖ).map k ≫ (Yₖ).map s) ((Yₖ).map r ≫ (Yₖ).map q)
    (by simpa only [Category.assoc] using hOuter.w)
  let α : W ⟶ Z := (Yₖ).preimage β
  have hβ : (Yₖ).map α = β := (Yₖ).map_preimage _
  have hbf : β ≫ (Yₖ).map ρS = (Yₖ).map k ≫ (Yₖ).map s := hZ'.lift_fst _ _ _
  have hbr : β ≫ (Yₖ).map π = (Yₖ).map r ≫ (Yₖ).map q := hZ'.lift_snd _ _ _
  have hChart : IsPullback ((Yₖ).map α) ((Yₖ).map r) ((Yₖ).map π) ((Yₖ).map q) := by
    rw [hβ]
    have hO : IsPullback (β ≫ (Yₖ).map ρS) ((Yₖ).map r) a ((Yₖ).map q ≫ b) := by
      rw [hbf]
      exact hOuter
    exact hO.of_right hbr hZ'
  have hOriginal : IsPullback α r π q := hChart.of_map_of_faithful (Yₖ)
  have hScheme : IsPullback α.left r.left π.left q.left :=
    hOriginal.map (Over.forget (M9StandaloneDraft.Base K))
  have hr : P r.left := MorphismProperty.of_isPullback
    ((IsPullback.of_hasPullback t v).map (Over.forget (M9StandaloneDraft.Base K))) hP
  have hπ : P π.left := MorphismProperty.of_isPullback_of_descendsAlong hScheme.flip
    (show (@Surjective ⊓ @Flat ⊓ @LocallyOfFinitePresentation :
      MorphismProperty Scheme.{u}) q.left from ⟨⟨hqs, hqf⟩, hqp⟩) hr
  exact ⟨Z, (Yₖ).map ρS, π, hZ', hπ⟩

end M9StacksIntegration.AllTestPresentationAtlas
