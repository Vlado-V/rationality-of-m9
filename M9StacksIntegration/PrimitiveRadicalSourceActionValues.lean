module

public import M9StacksIntegration.PrimitiveRadicalInvariantDescent

@[expose] public section

/-! Actual native symplectic relations of generic source-field points preserve
the pullback of every original native symplectic invariant. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open MonoidalCategory CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

namespace M9Native.PrimitiveRadicalSourceActionValues
open PrimitiveRadicalOrbitPoints PrimitiveRadicalOrbitGenericPoints
open PrimitiveRadicalInvariantDescent PrimitiveGrassmannianAction PrimitiveUniversalExtensionPoints

theorem eq_of_native_action {K : Type} [Field K] [Algebra ℂ K] (f : targetField)
    (hf : ∀ g : PrimitiveConstantFieldAction.Sp6, PrimitiveConstantFieldAction.fieldPullback g f = f)
    (g : M9.PrimitiveStabilizer.Sp6 K) (s t : sourceField →ₐ[ℂ] K)
    (h : PrimitiveFieldMatrixAction.actPoint K g (nativePoint K (sourcePoint K s))
      (nativePoint_projection K (sourcePoint K s)) = nativePoint K (sourcePoint K t)) :
    s (PrimitiveRadicalOrbitDominance.functionFieldEmbedding f) =
      t (PrimitiveRadicalOrbitDominance.functionFieldEmbedding f) := by
  have hp : PrimitiveFieldMatrixAction.overPoint K (nativePoint K (sourcePoint K s))
      (nativePoint_projection K (sourcePoint K s)) =
    NativeGenericFieldPoints.overPoint ℂ PrimitiveGrassmannianAction.projection rfl
      (s.comp PrimitiveRadicalOrbitDominance.functionFieldEmbedding) := by
    apply Over.OverMorphism.ext
    exact nativePoint_sourcePoint K s
  have ha := h
  change (lift (PrimitiveOriginalExtensionAction.nativeGroupPoint g)
    (PrimitiveFieldMatrixAction.overPoint K (nativePoint K (sourcePoint K s))
      (nativePoint_projection K (sourcePoint K s))) ≫ nativeAction.act).left =
        nativePoint K (sourcePoint K t) at ha
  rw [hp] at ha
  exact PrimitiveGeometricExtensionInvariance.eq_of_original_action f hf g
    (s.comp PrimitiveRadicalOrbitDominance.functionFieldEmbedding)
    (t.comp PrimitiveRadicalOrbitDominance.functionFieldEmbedding)
    (ha.trans (nativePoint_sourcePoint K t))

end M9Native.PrimitiveRadicalSourceActionValues
