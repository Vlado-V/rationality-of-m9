module

public import M9StacksIntegration.PrimitiveRadicalOrbitFieldExtension
public import M9StacksIntegration.PrimitiveConstantFieldAction
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

@[expose] public section

/-! Actual native-field automorphisms extend through the genuine algebraic
orbit-family field extension. No geometric point lifting or orbit section is assumed. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace M9Native.PrimitiveRadicalOrbitEmbeddingExtension
open PrimitiveRadicalOrbitFieldExtension

abbrev closure := AlgebraicClosure sourceField

def inclusion : sourceField →ₐ[ℂ] closure := IsScalarTower.toAlgHom ℂ sourceField closure

/-- Every automorphism of the actual native target field extends to an
embedding of the actual source field into its actual algebraic closure. -/
theorem exists_extension (σ : targetField ≃ₐ[ℂ] targetField) :
    ∃ s : sourceField →ₐ[ℂ] closure,
      s.comp PrimitiveRadicalOrbitDominance.functionFieldEmbedding =
        (inclusion.comp PrimitiveRadicalOrbitDominance.functionFieldEmbedding).comp σ.toAlgHom := by
  have : Algebra.IsAlgebraic targetField sourceField := source_isAlgebraic
  let f : targetField →ₐ[ℂ] closure :=
    (inclusion.comp PrimitiveRadicalOrbitDominance.functionFieldEmbedding).comp σ.toAlgHom
  obtain ⟨s,hs⟩ :=
    (IsAlgClosed.surjective_domRestrict_of_isAlgebraic
      (K := ℂ) (L := targetField) (M := closure) (E := sourceField)) f
  refine ⟨s,?_⟩
  apply AlgHom.ext
  intro x
  exact DFunLike.congr_fun hs x

/-- The previous theorem applies to the original constant symplectic
pullback, retaining the actual native field action and inclusions. -/
theorem exists_constant_action_extension (g : PrimitiveConstantFieldAction.Sp6) :
    ∃ s : sourceField →ₐ[ℂ] closure, ∀ x : targetField,
      s (PrimitiveRadicalOrbitDominance.functionFieldEmbedding x) =
        inclusion (PrimitiveRadicalOrbitDominance.functionFieldEmbedding
          (PrimitiveConstantFieldAction.fieldPullback g x)) := by
  obtain ⟨s,hs⟩ := exists_extension (PrimitiveConstantFieldAction.fieldPullback g)
  exact ⟨s,fun x => DFunLike.congr_fun hs x⟩

end M9Native.PrimitiveRadicalOrbitEmbeddingExtension
