module

public import StacksFrontier.CategoryTheory.Sites.Localization.RelocalizeRepresentable
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartSmallerBase
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic

/-!
# Actual conservativity and cartesian reflection of relocalization

The isomorphism proof below is extracted verbatim, with its theorem name
changed, from the pinned native RelocalizeReflectsIso source. That native
leaf is not built; its already-green RelocalizeRepresentable dependency is
sufficient to check this proof directly here. The original native source is
untouched. The proof uses the actual factorization-and-section formula,
so it neither assumes nor asserts that relocalization is full.
-/

set_option autoImplicit false
@[expose] public section
noncomputable section
open CategoryTheory CategoryTheory.Limits Opposite CategoryTheory.OverShriek

namespace M9StacksIntegration.AllTestRelocalizeReflection
universe v u
variable {C : Type u} [Category.{v} C] {U V : C} (f : V ⟶ U)

/-- The actual factorization-and-section presheaf functor reflects isomorphisms. -/
theorem isIso_of_isIso_relocalize {G H : (Over V)ᵒᵖ ⥤ Type v} (σ : G ⟶ H)
    [IsIso ((relocalizePresheafFunctor f).map σ)] : IsIso σ := by
  have (T : (Over V)ᵒᵖ) : IsIso (σ.app T) := by
    have hbij := (isIso_iff_bijective
      (((relocalizePresheafFunctor f).map σ).app
        (op (Over.mk (T.unop.hom ≫ f))))).mp inferInstance
    rw [isIso_iff_bijective]
    refine ⟨fun a b hab ↦ ?_, fun z ↦ ?_⟩
    · have key : (⟨⟨T.unop.hom, a⟩, rfl⟩ :
            ((relocalizePresheafFunctor f).obj G).obj (op (Over.mk (T.unop.hom ≫ f))))
          = ⟨⟨T.unop.hom, b⟩, rfl⟩ :=
        hbij.1 (congrArg (fun y : H.obj T ↦
          (⟨⟨T.unop.hom, y⟩, rfl⟩ :
            ((relocalizePresheafFunctor f).obj H).obj
              (op (Over.mk (T.unop.hom ≫ f))))) hab)
      exact eq_of_heq (Sigma.ext_iff.mp (congrArg Subtype.val key)).2
    · obtain ⟨p, hp⟩ := hbij.2 (⟨⟨T.unop.hom, z⟩, rfl⟩ :
        ((relocalizePresheafFunctor f).obj H).obj (op (Over.mk (T.unop.hom ≫ f))))
      obtain ⟨⟨ψ, s⟩, hψ⟩ := p
      have hp' : (⟨⟨ψ, σ.app (op (Over.mk ψ)) s⟩, hψ⟩ :
            ((relocalizePresheafFunctor f).obj H).obj (op (Over.mk (T.unop.hom ≫ f))))
          = ⟨⟨T.unop.hom, z⟩, rfl⟩ := hp
      have hp'' : (⟨ψ, σ.app (op (Over.mk ψ)) s⟩ :
            Σ χ : T.unop.left ⟶ V, H.obj (op (Over.mk χ)))
          = ⟨T.unop.hom, z⟩ := congrArg Subtype.val hp'
      obtain ⟨hfst, hsnd⟩ := Sigma.ext_iff.mp hp''
      subst hfst
      exact ⟨s, eq_of_heq hsnd⟩
  exact NatIso.isIso_of_isIso_app _


/-- The actual lower-shriek relocalization reflects cartesian squares, despite
not being full. This uses the already-checked native faithful/limit-reflection
provider in EtaleChartSmallerBase, whose original source is unchanged. -/
theorem isPullback_of_relocalize_isPullback
    {P X Y Z : (Over V)ᵒᵖ ⥤ Type v} {a : P ⟶ X} {b : P ⟶ Y}
    {c : X ⟶ Z} {d : Y ⟶ Z}
    (h : IsPullback ((relocalizePresheafFunctor f).map a)
      ((relocalizePresheafFunctor f).map b)
      ((relocalizePresheafFunctor f).map c)
      ((relocalizePresheafFunctor f).map d)) : IsPullback a b c d := by
  let L := relocalizePresheafFunctor f
  let : L.Faithful := AlgebraicGeometry.relocalizePresheaf_faithful f
  let : ReflectsLimitsOfShape WalkingCospan L :=
    AlgebraicGeometry.relocalizePresheaf_reflectsPullbacks f
  exact h.of_map_of_faithful L

end M9StacksIntegration.AllTestRelocalizeReflection
