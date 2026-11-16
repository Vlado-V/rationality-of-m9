module

public import M9StacksIntegration.AllTestSchemeFamilies
public import StacksFrontier.AlgebraicGeometry.Spaces.FibreProduct

/-!
# Actual fibre products of original all-test algebraic spaces

This is the original full test category and original Type-u-valued sheaves.
The finite-limit proof uses no sheafification or size restriction. It adapts
the pinned native `Spaces/FibreProduct` proof to the literal standalone
space fields; all atlas properties remain tested on every original scheme.
-/

set_option autoImplicit false
@[expose] public section
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace M9StacksIntegration.AllTestSpacePullbacks
universe u
variable (K : Type u) [Field K]

/-- The actual original space axioms hold on every genuine pullback of
original algebraic spaces, in the entire unchanged original category. -/
theorem space_conditions_of_isPullback
    (F G H : M9StandaloneDraft.Space K) {Z : M9StandaloneDraft.Presheaves K}
    {f : F.obj ⟶ H.obj} {g : G.obj ⟶ H.obj} {p : Z ⟶ F.obj} {q : Z ⟶ G.obj}
    (hZ : IsPullback p q f g) :
    Presheaf.IsSheaf (Scheme.fppfTopology.over (M9StandaloneDraft.Base K)) Z ∧
      yoneda.relativelyRepresentable (diag Z) ∧
      ∃ (U : M9StandaloneDraft.Schemes K) (a : yoneda.obj U ⟶ Z),
        (MorphismProperty.inverseImage (@Etale.{u})
          (Over.forget (M9StandaloneDraft.Base K))).presheaf a ∧
        (MorphismProperty.inverseImage (@AlgebraicGeometry.Surjective.{u})
          (Over.forget (M9StandaloneDraft.Base K))).presheaf a := by
  let Qe := MorphismProperty.inverseImage (@Etale.{u})
    (Over.forget (M9StandaloneDraft.Base K))
  let : MorphismProperty.IsStableUnderComposition
      (@AlgebraicGeometry.Surjective.{u} : MorphismProperty Scheme.{u}) :=
    ⟨fun _ _ hf hg => ⟨hg.surj.comp hf.surj⟩⟩
  let Qs := MorphismProperty.inverseImage (@AlgebraicGeometry.Surjective.{u})
    (Over.forget (M9StandaloneDraft.Base K))
  let : Qe.IsStableUnderComposition :=
    MorphismProperty.IsStableUnderComposition.inverseImage (P := @Etale.{u})
      (Over.forget (M9StandaloneDraft.Base K))
  let : Qs.IsStableUnderComposition :=
    MorphismProperty.IsStableUnderComposition.inverseImage (P := @AlgebraicGeometry.Surjective.{u})
      (Over.forget (M9StandaloneDraft.Base K))
  let : Qe.presheaf.IsStableUnderComposition :=
    MorphismProperty.relative_isStableUnderComposition Qe (F := yoneda)
  let : Qs.presheaf.IsStableUnderComposition :=
    MorphismProperty.relative_isStableUnderComposition Qs (F := yoneda)
  let : HasBinaryProducts (M9StandaloneDraft.Schemes K) :=
    hasBinaryProducts_of_hasTerminal_and_pullbacks _
  have hsheaf : Presheaf.IsSheaf (Scheme.fppfTopology.over (M9StandaloneDraft.Base K)) Z := by
    refine ObjectProperty.prop_of_isLimit _ hZ.isLimit fun j => ?_
    match j with
    | none => exact H.isSheaf
    | some WalkingPair.left => exact F.isSheaf
    | some WalkingPair.right => exact G.isSheaf
  let : Mono (prod.lift p q) := mono_prodLift hZ
  have hdiag : yoneda.relativelyRepresentable (diag Z) :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback
      (isPullback_diag_of_mono (prod.lift p q))
      (MorphismProperty.diag_mem_of_prod _ F.diagonal G.diagonal)
  obtain ⟨U, a, hae, has⟩ := F.atlas
  obtain ⟨V, b, hbe, hbs⟩ := G.atlas
  obtain ⟨W, w, wfst, hW⟩ := Functor.relativelyRepresentable.of_diag H.diagonal (a ≫ f) (b ≫ g)
  have hUG : IsPullback (pullback.fst (a ≫ f) g) (pullback.snd (a ≫ f) g) (a ≫ f) g :=
    IsPullback.of_hasPullback _ _
  obtain ⟨τ, hτ⟩ : ∃ τ, IsPullback (pullback.fst (a ≫ f) g) τ a p :=
    ⟨_, IsPullback.of_bot' hUG hZ⟩
  obtain ⟨ρ, hρ⟩ : ∃ ρ, IsPullback (yoneda.map w) ρ b (pullback.snd (a ≫ f) g) :=
    ⟨_, IsPullback.of_bot' hW.flip hUG.flip⟩
  refine ⟨hsheaf, hdiag, W, ρ ≫ τ, ?_, ?_⟩
  · exact MorphismProperty.comp_mem _ _ _
      ((MorphismProperty.relative_isStableUnderBaseChange (F := yoneda) _).of_isPullback hρ hbe)
      ((MorphismProperty.relative_isStableUnderBaseChange (F := yoneda) _).of_isPullback hτ hae)
  · exact MorphismProperty.comp_mem _ _ _
      ((MorphismProperty.relative_isStableUnderBaseChange (F := yoneda) _).of_isPullback hρ hbs)
      ((MorphismProperty.relative_isStableUnderBaseChange (F := yoneda) _).of_isPullback hτ has)

/-- The actual full-test fibre-product algebraic space. Its presheaf is the
actual presheaf pullback, not a separately declared moduli object. -/
def pullbackSpace (F G H : M9StandaloneDraft.Space K) (f : F.obj ⟶ H.obj) (g : G.obj ⟶ H.obj) :
    M9StandaloneDraft.Space K where
  obj := pullback f g
  isSheaf := (space_conditions_of_isPullback K F G H (IsPullback.of_hasPullback f g)).1
  diagonal := (space_conditions_of_isPullback K F G H (IsPullback.of_hasPullback f g)).2.1
  atlas := (space_conditions_of_isPullback K F G H (IsPullback.of_hasPullback f g)).2.2

@[simp] theorem pullbackSpace_obj (F G H : M9StandaloneDraft.Space K)
    (f : F.obj ⟶ H.obj) (g : G.obj ⟶ H.obj) :
    (pullbackSpace K F G H f g).obj = pullback f g := rfl

end M9StacksIntegration.AllTestSpacePullbacks
