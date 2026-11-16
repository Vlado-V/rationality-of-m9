module

public import M9StacksIntegration.AllTestSpacePullbacks
public import M9StacksIntegration.AllTestSingleSchematicCover

/-!
# Actual pullback of every original all-test curve family

The total is the genuine presheaf fibre product, with original Type-u values.
A schematic etale cover of the original base pulls back to a schematic etale
cover of the new original base. The unchanged all-field-point genus condition
is transported by the proved original cohomological base-change theorem.
-/

set_option autoImplicit false
@[expose] public section
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

namespace M9StacksIntegration.AllTestFamilyPullback
open AllTestSchemeFamilies AllTestSpacePullbacks AllTestSingleSchematicCover
universe u
variable (K : Type u) [Field K]
local notation "Yₖ" => (yoneda (C := M9StandaloneDraft.Schemes K))

private theorem originalPresheafPullbacks : HasPullbacks (M9StandaloneDraft.Presheaves K) :=
  functorCategoryHasLimitsOfShape (J := WalkingCospan) (C := Type u)
    (K := (M9StandaloneDraft.Schemes K)ᵒᵖ)

/-- The actual finite presheaf pullback exists, in the unchanged value universe. -/
theorem originalPresheafPullback
    {X Y Z : M9StandaloneDraft.Presheaves K} (f : X ⟶ Z) (g : Y ⟶ Z) : HasPullback f g :=
  (originalPresheafPullbacks K).has_limit (cospan f g)

/-- Every actual base change has the literal original local curve property. -/
theorem pullback_locally_curve {T U : M9StandaloneDraft.Schemes K} {g : ℕ}
    (F : M9StandaloneDraft.Family K T g) (a : U ⟶ T) :
    let : HasPullback F.projection ((Yₖ).map a) :=
      originalPresheafPullback K F.projection ((Yₖ).map a)
    ∀ u : U.left, ∃ (V W : M9StandaloneDraft.Schemes K) (v : V ⟶ U) (q : W ⟶ V)
      (r : (Yₖ).obj W ⟶ CategoryTheory.Limits.pullback (C := M9StandaloneDraft.Presheaves K) F.projection ((Yₖ).map a)),
      Etale v.left ∧ u ∈ Set.range v.left ∧
        IsPullback r ((Yₖ).map q) (pullback.snd F.projection ((Yₖ).map a))
          ((Yₖ).map v) ∧ M9StandaloneDraft.SchemeCurve q.left g := by
  let : HasPullback F.projection ((Yₖ).map a) :=
    originalPresheafPullback K F.projection ((Yₖ).map a)
  obtain ⟨U₀, Z₀, v₀, q₀, r₀, he, hs, hcart, hq⟩ := exists_schematic_etale_cover K F
  let V := pullback v₀ a
  let b : V ⟶ U₀ := pullback.fst v₀ a
  let v : V ⟶ U := pullback.snd v₀ a
  let W := pullback q₀ b
  let c : W ⟶ Z₀ := pullback.fst q₀ b
  let q : W ⟶ V := pullback.snd q₀ b
  have hv : IsPullback b.left v.left v₀.left a.left :=
    (IsPullback.of_hasPullback v₀ a).map (Over.forget (M9StandaloneDraft.Base K))
  have he' : Etale v.left := MorphismProperty.of_isPullback (P := @Etale) hv he
  have hs' : Surjective v.left := MorphismProperty.of_isPullback (P := @AlgebraicGeometry.Surjective) hv hs
  have hq' : M9StandaloneDraft.SchemeCurve q.left g :=
    StandaloneCurveCohomology.schemeCurve_of_isPullback q₀.left q.left c.left b.left
      ((IsPullback.of_hasPullback q₀ b).map (Over.forget (M9StandaloneDraft.Base K))) hq
  have houter : IsPullback ((Yₖ).map c ≫ r₀) ((Yₖ).map q) F.projection
      ((Yₖ).map b ≫ (Yₖ).map v₀) :=
    ((IsPullback.of_hasPullback q₀ b).map (Yₖ)).paste_horiz hcart
  have hvw : (Yₖ).map b ≫ (Yₖ).map v₀ = (Yₖ).map v ≫ (Yₖ).map a :=
    ((IsPullback.of_hasPullback v₀ a).map (Yₖ)).w
  have houter' : IsPullback ((Yₖ).map c ≫ r₀) ((Yₖ).map q) F.projection
      ((Yₖ).map v ≫ (Yₖ).map a) := hvw ▸ houter
  let r := pullback.lift ((Yₖ).map c ≫ r₀) ((Yₖ).map q ≫ (Yₖ).map v)
    (houter'.w.trans (Category.assoc _ _ _).symm)
  have hr : IsPullback r ((Yₖ).map q)
      (pullback.snd F.projection ((Yₖ).map a)) ((Yₖ).map v) := by
    apply IsPullback.of_right (t := IsPullback.of_hasPullback F.projection ((Yₖ).map a))
    · simpa only [r, pullback.lift_fst] using houter'
    · exact pullback.lift_snd _ _ _
  intro _ u
  obtain ⟨vpoint, hpoint⟩ := hs'.surj u
  exact ⟨V, W, v, q, r, he', ⟨vpoint, hpoint⟩, hr, hq'⟩

/-- The actual all-test pullback family on every original base scheme. -/
def pullbackFamily {T U : M9StandaloneDraft.Schemes K} {g : ℕ}
    (F : M9StandaloneDraft.Family K T g) (a : U ⟶ T) : M9StandaloneDraft.Family K U g := by
  let : HasPullback F.projection ((Yₖ).map a) :=
    originalPresheafPullback K F.projection ((Yₖ).map a)
  exact {
    total := pullbackSpace K F.total (standaloneSchemeSpace K U) (standaloneSchemeSpace K T)
      F.projection ((Yₖ).map a)
    projection := pullback.snd F.projection ((Yₖ).map a)
    locally_curve := pullback_locally_curve K F a }

@[simp] theorem pullbackFamily_total_obj {T U : M9StandaloneDraft.Schemes K} {g : ℕ}
    (F : M9StandaloneDraft.Family K T g) (a : U ⟶ T) :
    let : HasPullback F.projection ((Yₖ).map a) :=
      originalPresheafPullback K F.projection ((Yₖ).map a)
    (pullbackFamily K F a).total.obj = CategoryTheory.Limits.pullback (C := M9StandaloneDraft.Presheaves K) F.projection ((Yₖ).map a) := by
  let : HasPullback F.projection ((Yₖ).map a) :=
    originalPresheafPullback K F.projection ((Yₖ).map a)
  rfl

@[simp] theorem pullbackFamily_projection {T U : M9StandaloneDraft.Schemes K} {g : ℕ}
    (F : M9StandaloneDraft.Family K T g) (a : U ⟶ T) :
    let : HasPullback F.projection ((Yₖ).map a) :=
      originalPresheafPullback K F.projection ((Yₖ).map a)
    (pullbackFamily K F a).projection = pullback.snd F.projection ((Yₖ).map a) := by
  let : HasPullback F.projection ((Yₖ).map a) :=
    originalPresheafPullback K F.projection ((Yₖ).map a)
  rfl

/-- The full original square, on every original test, is cartesian. -/
theorem pullbackFamily_isPullback {T U : M9StandaloneDraft.Schemes K} {g : ℕ}
    (F : M9StandaloneDraft.Family K T g) (a : U ⟶ T) :
    let : HasPullback F.projection ((Yₖ).map a) :=
      originalPresheafPullback K F.projection ((Yₖ).map a)
    IsPullback (pullback.fst F.projection ((Yₖ).map a))
      (pullbackFamily K F a).projection F.projection ((Yₖ).map a) := by
  let : HasPullback F.projection ((Yₖ).map a) :=
    originalPresheafPullback K F.projection ((Yₖ).map a)
  exact IsPullback.of_hasPullback _ _

end M9StacksIntegration.AllTestFamilyPullback
