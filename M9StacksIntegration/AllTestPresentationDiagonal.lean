module

public import M9StacksIntegration.AllTestOriginalMonoFlatDescent
public import M9StacksIntegration.AllTestPairFppfLift
public import M9StacksIntegration.AllTestKernelPairDiagonal
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.BinaryProducts
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Mono

/-!
# The actual diagonal of an original full-site etale presentation

A genuine sheaf on ALL original test schemes, with a genuine locally
surjective original represented chart and an actual represented kernel
pair whose projections are etale, has an actually representable diagonal.
After one proved original fppf lift, each represented diagonal test becomes
the pullback of the actual relation scheme. The checked original all-test
monomorphic flat-chart descent constructs its representing scheme.
Diagonal representability, effective descent and a classifier are conclusions
or proved tools, never additional hypotheses.
-/

set_option autoImplicit false
@[expose] public section
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

namespace M9StacksIntegration.AllTestPresentationDiagonal
open AllTestLargeSpaceSmallSections AllTestSheafCoproducts
universe u
variable (K : Type u) [Field K]
local notation "Yₖ" => (largeYoneda K)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The diagonal of an ACTUAL original-site etale presentation is
represented on EVERY original test, without any site cutoff assumption. -/
theorem diagonal_representable_of_presentation
    {F : (M9StandaloneDraft.Schemes K)ᵒᵖ ⥤ Type (u+1)}
    (hF : Presheaf.IsSheaf (topology K) F)
    (U R : M9StandaloneDraft.Schemes K) (s t : R ⟶ U)
    (a : (Yₖ).obj U ⟶ F)
    (ha : Presheaf.IsLocallySurjective (topology K) a)
    (hker : IsPullback ((Yₖ).map s) ((Yₖ).map t) a a)
    (ht : Etale t.left) : (Yₖ).relativelyRepresentable (diag F) := by
  let : HasBinaryProducts (M9StandaloneDraft.Schemes K) :=
    hasBinaryProducts_of_hasTerminal_and_pullbacks _
  let : HasPullbacks ((M9StandaloneDraft.Schemes K)ᵒᵖ ⥤ Type (u+1)) :=
    functorCategoryHasLimitsOfShape (J := WalkingCospan) (C := Type (u+1))
      (K := (M9StandaloneDraft.Schemes K)ᵒᵖ)
  let : HasBinaryProducts ((M9StandaloneDraft.Schemes K)ᵒᵖ ⥤ Type (u+1)) :=
    functorCategoryHasLimitsOfShape (J := Discrete WalkingPair) (C := Type (u+1))
      (K := (M9StandaloneDraft.Schemes K)ᵒᵖ)
  let j : R ⟶ U ⨯ U := prod.lift s t
  let c : (Yₖ).obj (U ⨯ U) ⟶ F ⨯ F := prodComparison (Yₖ) U U ≫ prod.map a a
  have hjc : (Yₖ).map j ≫ prodComparison (Yₖ) U U =
      prod.lift ((Yₖ).map s) ((Yₖ).map t) := by
    apply prod.hom_ext
    · rw [Category.assoc, prodComparison_fst, ← (Yₖ).map_comp, prod.lift_fst]
      exact (prod.lift_fst _ _).symm
    · rw [Category.assoc, prodComparison_snd, ← (Yₖ).map_comp, prod.lift_snd]
      exact (prod.lift_snd _ _).symm
  have hJ : IsPullback ((Yₖ).map s ≫ a) ((Yₖ).map j) (diag F) c := by
    apply (AllTestKernelPairDiagonal.isPullback_diagonal_of_kernelPair hker).of_iso'
      (Iso.refl _) (Iso.refl _) (asIso (prodComparison (Yₖ) U U)) (Iso.refl _)
    · simp
    · change prod.lift ((Yₖ).map s) ((Yₖ).map t) =
        (Yₖ).map j ≫ prodComparison (Yₖ) U U
      exact hjc.symm
    · simp
    · simp [c]
  let : Mono ((Yₖ).map j) := hJ.mono_snd_of_mono
  let : Mono j := (Yₖ).mono_of_mono_map inferInstance
  let : Mono j.left := (Over.forget (M9StandaloneDraft.Base K)).map_mono j
  let : Etale t.left := ht
  have hjt : j.left ≫ (prod.snd (X := U) (Y := U)).left = t.left :=
    congrArg (fun m => m.left) (prod.lift_snd s t)
  let : LocallyOfFiniteType (j.left ≫ (prod.snd (X := U) (Y := U)).left) :=
    hjt.symm ▸ (inferInstanceAs (LocallyOfFiniteType t.left))
  have hjl : LocallyOfFiniteType j.left :=
    locallyOfFiniteType_of_comp j.left (prod.snd (X := U) (Y := U)).left
  intro T g
  obtain ⟨V, q, v₁, v₂, hqf, hqp, hqs, he₁, he₂⟩ :=
    AllTestPairFppfLift.exists_single_pair_fppf_lift K hF U T a ha
      (g ≫ prod.fst) (g ≫ prod.snd)
  let x : V ⟶ U ⨯ U := prod.lift v₁ v₂
  have hfac : (Yₖ).map x ≫ c = (Yₖ).map q ≫ g := by
    apply prod.hom_ext
    · calc
        ((Yₖ).map x ≫ c) ≫ prod.fst =
            ((Yₖ).map x ≫ (Yₖ).map prod.fst) ≫ a := by
          simp only [c, Category.assoc, prod.map_fst, prodComparison_fst_assoc]
        _ = (Yₖ).map (x ≫ prod.fst) ≫ a := by rw [(Yₖ).map_comp]
        _ = (Yₖ).map v₁ ≫ a := by rw [prod.lift_fst]
        _ = ((Yₖ).map q ≫ g) ≫ prod.fst := by
          simpa only [Category.assoc] using he₁
    · calc
        ((Yₖ).map x ≫ c) ≫ prod.snd =
            ((Yₖ).map x ≫ (Yₖ).map prod.snd) ≫ a := by
          simp only [c, Category.assoc, prod.map_snd, prodComparison_snd_assoc]
        _ = (Yₖ).map (x ≫ prod.snd) ≫ a := by rw [(Yₖ).map_comp]
        _ = (Yₖ).map v₂ ≫ a := by rw [prod.lift_snd]
        _ = ((Yₖ).map q ≫ g) ≫ prod.snd := by
          simpa only [Category.assoc] using he₂
  let R' := pullback j x
  let p : R' ⟶ R := pullback.fst j x
  let r : R' ⟶ V := pullback.snd j x
  have hOuter : IsPullback ((Yₖ).map p ≫ ((Yₖ).map s ≫ a)) ((Yₖ).map r)
      (diag F) ((Yₖ).map q ≫ g) := by
    have h := ((IsPullback.of_hasPullback j x).map (Yₖ)).paste_horiz hJ
    simpa only [hfac] using h
  let A := pullback (diag F) g
  let f : A ⟶ (Yₖ).obj T := pullback.snd (diag F) g
  have hD : IsPullback (pullback.fst (diag F) g) f (diag F) g :=
    IsPullback.of_hasPullback _ _
  let : Mono f := hD.mono_snd_of_mono
  have hProd : Presheaf.IsSheaf (topology K) (F ⨯ F) := by
    refine ObjectProperty.prop_of_isLimit _
      (c := BinaryFan.mk (prod.fst (X := F) (Y := F)) prod.snd)
      (prodIsProd F F) fun k => ?_
    rcases k with ⟨k⟩
    cases k <;> exact hF
  have hA : Presheaf.IsSheaf (topology K) A := by
    refine ObjectProperty.prop_of_isLimit _ (c := hD.cone) hD.isLimit fun k => ?_
    match k with
    | none => exact hProd
    | some WalkingPair.left => exact hF
    | some WalkingPair.right => exact ((topology K).uliftYoneda.{u+1}.obj T).property
  let b : (Yₖ).obj R' ⟶ A := hD.lift
    ((Yₖ).map p ≫ ((Yₖ).map s ≫ a)) ((Yₖ).map r ≫ (Yₖ).map q)
    (by simpa only [Category.assoc] using hOuter.w)
  have hbf : b ≫ pullback.fst (diag F) g = (Yₖ).map p ≫ ((Yₖ).map s ≫ a) :=
    hD.lift_fst _ _ _
  have hbr : b ≫ f = (Yₖ).map r ≫ (Yₖ).map q := hD.lift_snd _ _ _
  have hChart : IsPullback b ((Yₖ).map r) f ((Yₖ).map q) := by
    have hO : IsPullback (b ≫ pullback.fst (diag F) g) ((Yₖ).map r)
        (diag F) ((Yₖ).map q ≫ g) := by rw [hbf]; exact hOuter
    exact hO.of_right hbr hD
  have hScheme : IsPullback p.left r.left j.left x.left :=
    (IsPullback.of_hasPullback j x).map (Over.forget (M9StandaloneDraft.Base K))
  have hrm : Mono r.left := hScheme.mono_snd_of_mono
  have hrl : LocallyOfFiniteType r.left :=
    MorphismProperty.of_isPullback hScheme hjl
  let : A.IsRepresentable :=
    @AllTestOriginalMonoFlatDescent.isRepresentable_of_single_flat_chart
      K _ A hA T V R' q r f inferInstance b hChart hqf hqp hqs hrm hrl
  let e : (Yₖ).obj A.reprX ≅ A := A.uliftYonedaReprXIso
  let z : A.reprX ⟶ T := (Yₖ).preimage (e.hom ≫ f)
  refine ⟨A.reprX, z, e.hom ≫ pullback.fst (diag F) g, ?_⟩
  apply hD.of_iso' e (Iso.refl _) (Iso.refl _) (Iso.refl _)
  · simp
  · simpa only [Iso.refl_hom, Category.comp_id] using
      ((Yₖ).map_preimage (e.hom ≫ f)).symm
  · simp
  · simp

end M9StacksIntegration.AllTestPresentationDiagonal
