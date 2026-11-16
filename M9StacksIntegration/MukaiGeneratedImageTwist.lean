module

public import M9StacksIntegration.MukaiGeneratedImage
public import Mathlib.CategoryTheory.Monoidal.Braided.Basic
public import Mathlib.CategoryTheory.Monoidal.CoherenceLemmas

/-!
# The actual ideal relation for one extra section of a line twist

A paired line and ideal give a concrete factorization of the
ideal-multiple of any extra section through the canonical inclusion.
This algebra is later instantiated with the canonical Cartier pairing.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory

universe u v

namespace M9Native.MukaiGeneratedImage

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]
variable [SymmetricCategory C]
variable {I L Q : C}

/-- The canonical inclusion into a line twist. -/
def twistInclusion (c : 𝟙_ C ⟶ L) : Q ⟶ Q ⊗ L :=
  (ρ_ Q).inv ≫ Q ◁ c

/-- Contract the line factor of a section against its paired ideal. -/
def contractTwistedSection (ev : L ⊗ I ≅ 𝟙_ C) (a : 𝟙_ C ⟶ Q ⊗ L) : I ⟶ Q :=
  (λ_ I).inv ≫ a ▷ I ≫ (α_ Q L I).hom ≫ Q ◁ ev.hom ≫ (ρ_ Q).hom

/-- Multiplying an extra section by the ideal inclusion is exactly
the contracted section followed by the canonical twist inclusion. -/
theorem contractTwistedSection_inclusion
    (ev : L ⊗ I ≅ 𝟙_ C) (iota : I ⟶ 𝟙_ C) (c : 𝟙_ C ⟶ L)
    (hpair : L ◁ iota ≫ (ρ_ L).hom = ev.hom ≫ c)
    (a : 𝟙_ C ⟶ Q ⊗ L) :
    contractTwistedSection ev a ≫ twistInclusion c = iota ≫ a := by
  dsimp only [contractTwistedSection, twistInclusion]
  simp only [Category.assoc, Iso.hom_inv_id_assoc]
  rw [← whiskerLeft_comp, ← hpair, whiskerLeft_comp]
  rw [← associator_naturality_right_assoc]
  have hcoh : (α_ Q L (𝟙_ C)).hom ≫ Q ◁ (ρ_ L).hom = (ρ_ (Q ⊗ L)).hom := by
    monoidal
  rw [hcoh, ← whisker_exchange_assoc, rightUnitor_naturality]
  rw [← Category.assoc, ← leftUnitor_inv_naturality, ← unitors_equal]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]

end M9Native.MukaiGeneratedImage

