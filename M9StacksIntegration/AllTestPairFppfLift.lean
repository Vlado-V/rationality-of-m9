module

public import M9StacksIntegration.AllTestSingleFppfLift

/-!
# Simultaneous original fppf lifts

Two represented sections lift through the same actual original atlas after
one actual original fppf cover, by applying the proved single-lift theorem
twice and composing the actual covering scheme maps.
-/

set_option autoImplicit false
@[expose] public section
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

namespace M9StacksIntegration.AllTestPairFppfLift
universe u
variable (K : Type u) [Field K]

set_option backward.isDefEq.respectTransparency false in
/-- Simultaneous lifts of two ORIGINAL represented sections, with actual
surjectivity/flatness/finite presentation of their common original cover. -/
theorem exists_single_pair_fppf_lift
    {F : (M9StandaloneDraft.Schemes K)ᵒᵖ ⥤ Type (u+1)}
    (hF : Presheaf.IsSheaf (AllTestSheafCoproducts.topology K) F)
    (U T : M9StandaloneDraft.Schemes K)
    (a : uliftYoneda.{u+1}.obj U ⟶ F)
    (ha : Presheaf.IsLocallySurjective (AllTestSheafCoproducts.topology K) a)
    (b₁ b₂ : uliftYoneda.{u+1}.obj T ⟶ F) :
    ∃ (V : M9StandaloneDraft.Schemes K) (q : V ⟶ T) (v₁ v₂ : V ⟶ U),
      Flat q.left ∧ LocallyOfFinitePresentation q.left ∧ Surjective q.left ∧
      uliftYoneda.{u+1}.map v₁ ≫ a = uliftYoneda.{u+1}.map q ≫ b₁ ∧
      uliftYoneda.{u+1}.map v₂ ≫ a = uliftYoneda.{u+1}.map q ≫ b₂ := by
  obtain ⟨V₁, q₁, u₁, hf₁, hp₁, hs₁, he₁⟩ :=
    AllTestSingleFppfLift.exists_single_fppf_lift K hF U T a ha b₁
  obtain ⟨V, q₂, v₂, hf₂, hp₂, hs₂, he₂⟩ :=
    AllTestSingleFppfLift.exists_single_fppf_lift K hF U V₁ a ha
      (uliftYoneda.{u+1}.map q₁ ≫ b₂)
  let : Flat q₁.left := hf₁
  let : Flat q₂.left := hf₂
  let : LocallyOfFinitePresentation q₁.left := hp₁
  let : LocallyOfFinitePresentation q₂.left := hp₂
  refine ⟨V, q₂ ≫ q₁, q₂ ≫ u₁, v₂,
    (show Flat (q₂.left ≫ q₁.left) from inferInstance),
    (show LocallyOfFinitePresentation (q₂.left ≫ q₁.left) from inferInstance),
    ⟨hs₁.surj.comp hs₂.surj⟩, ?_, ?_⟩
  · simpa only [Functor.map_comp, Category.assoc] using
      congrArg (fun m => uliftYoneda.{u+1}.map q₂ ≫ m) he₁
  · simpa only [Functor.map_comp, Category.assoc] using he₂

end M9StacksIntegration.AllTestPairFppfLift
