module

public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic

/-! A morphism factoring through a monomorphism is an isomorphism
onto that factor if its genuine base change to the factor is an
isomorphism. The proof constructs the actual self-pullback inverse. -/

@[expose] public noncomputable section
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits
universe u v
namespace M9Native.MonoFactorIsIso

variable {C : Type u} [Category.{v} C] {Z B X : C} (i : B ⟶ X) [Mono i] (q : Z ⟶ B)
  (f : Z ⟶ X) (h : q ≫ i = f) [HasPullback i f]

def isoPullback : Z ≅ pullback i f where
  hom := pullback.lift q (𝟙 Z) (by simpa using h)
  inv := pullback.snd i f
  hom_inv_id := by simp
  inv_hom_id := by
    apply pullback.hom_ext
    · apply (cancel_mono i).mp
      simp only [Category.assoc,pullback.lift_fst,Category.id_comp]
      rw [h,← pullback.condition]
    · simp

theorem isoPullback_hom_fst : (isoPullback i q f h).hom ≫ pullback.fst i f = q := by simp [isoPullback]

include h in
theorem isIso_factor [IsIso (pullback.fst i f)] : IsIso q := by
  rw [← isoPullback_hom_fst i q f h]
  infer_instance

end M9Native.MonoFactorIsIso
