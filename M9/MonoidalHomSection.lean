module

public import Mathlib.CategoryTheory.Monoidal.Closed.Basic
public import Mathlib.CategoryTheory.Monoidal.Preadditive

/-!
# Nonvanishing of the actual curried Hom section after monoidal pullback

A strong monoidal functor carries a morphism's curried unit-to-Hom map
to a section whose vanishing forces the image morphism to vanish. This
uses the actual curry/uncurry identities and tensor evaluation, not a
comparison-isomorphism or flatness assumption for internal Hom.
-/

@[expose] public section

open CategoryTheory MonoidalCategory MonoidalClosed

namespace M9.MonoidalHomSection

variable {C D : Type*} [Category* C] [Category* D]
  [MonoidalCategory C] [MonoidalCategory D] [Preadditive D] [MonoidalPreadditive D]
  (F : C ⥤ D) [F.Monoidal]

/-- A zero image of the actual curried Hom morphism forces a zero
image of the original morphism. No flatness or internal-Hom comparison
isomorphism is required. -/
theorem map_eq_zero_of_map_curry'_eq_zero {A B : C} [Closed A] (f : A ⟶ B)
    (hf : F.map (curry' f) = 0) : F.map f = 0 := by
  rw [← uncurry'_curry' f, uncurry', uncurry_eq, F.map_comp, F.map_comp,
    Functor.Monoidal.map_whiskerLeft, hf]
  simp

/-- The actual transported unit-to-Hom section under a strong monoidal
functor. For a scheme pullback this is the section of the pulled-back
internal-Hom sheaf, before any comparison with an internal Hom on the
source scheme. -/
def mappedHomSection {A B : C} [Closed A] (f : A ⟶ B) :
    𝟙_ D ⟶ F.obj ((ihom A).obj B) :=
  Functor.LaxMonoidal.ε F ≫ F.map (curry' f)

/-- A nonzero actual image morphism has nonzero transported Hom
section. The invertible monoidal unit comparison removes the extra
unit morphism. -/
theorem mappedHomSection_ne_zero {A B : C} [Closed A] (f : A ⟶ B)
    (hf : F.map f ≠ 0) : mappedHomSection F f ≠ 0 := by
  intro hs
  apply hf
  apply map_eq_zero_of_map_curry'_eq_zero F f
  apply (cancel_epi (Functor.LaxMonoidal.ε F)).mp
  simpa [mappedHomSection] using hs

end M9.MonoidalHomSection
