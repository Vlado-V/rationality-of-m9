module

public import StacksFrontier.Deformation.Cofibered
public import StacksFrontier.CategoryTheory.FiberedCategory.HomLift

/-!
# A cofibered groupoid with thin fibres has a faithful structure functor

This is the semantic adapter from vanishing infinitesimal automorphisms
(all Artin fibres are then thin) to the actual discrete deformation model.
The proof uses the original cofibered unique lifting property, and does
not assume an equivalence with the functor of isomorphism classes.
-/

@[expose] public noncomputable section

open CategoryTheory

universe u v u' v'

namespace M9Native.CofiberedThin

variable {F : Type u} [Category.{v} F] {C : Type u'} [Category.{v'} C]

/-- An actual cofibered structure and thin fibres determine every morphism
from its image in the base. -/
theorem faithful_of_isThin_fibers (p : F ⥤ C) (hp : Deformation.IsCofiberedInGroupoids p)
    (hthin : ∀ A : C, Quiver.IsThin (p.Fiber A)) : p.Faithful := by
  refine ⟨?_⟩
  intro a b α β hαβ
  have hop : (𝟙 (p.obj b)).op ≫ p.op.map α.op = p.op.map β.op := by
    change (p.map α ≫ 𝟙 (p.obj b)).op = (p.map β).op
    exact congrArg Opposite.op (by simpa using hαβ)
  obtain ⟨χop, hχ, -⟩ := hp.unique_lift α.op β.op (𝟙 (p.obj b)).op hop
  let χ : b ⟶ b := χop.unop
  have hχmap : p.map χ = 𝟙 (p.obj b) := Opposite.op_injective hχ.1
  have hχfac : α ≫ χ = β := Opposite.op_injective hχ.2
  have hχlift : p.IsHomLift (𝟙 (p.obj b)) χ :=
    IsHomLift.of_fac p _ χ rfl rfl (by simpa using hχmap.symm)
  let bF : p.Fiber (p.obj b) := ⟨b, rfl⟩
  have hχid : χ = 𝟙 b :=
    congrArg Subtype.val ((hthin (p.obj b) bF bF).elim
      (⟨χ, hχlift⟩ : bF ⟶ bF) (𝟙 bF))
  simpa only [hχid, Category.comp_id] using hχfac

end M9Native.CofiberedThin
