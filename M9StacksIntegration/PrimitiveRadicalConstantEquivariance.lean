module

public import M9StacksIntegration.PrimitiveRadicalEquivariantKernelPairs
public import M9StacksIntegration.PrimitiveRadicalOrbitEmbeddingExtension

@[expose] public section

/-! Actual constant target automorphisms lift through the algebraic native
family field, and the resulting genuine family points differ by the actual
reduced stabilizer. No rational orbit section or point lifting is assumed. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open AlgebraicGeometry CategoryTheory

namespace M9Native.PrimitiveRadicalConstantEquivariance
open PrimitiveRadicalOrbitFieldExtension PrimitiveRadicalOrbitEmbeddingExtension
open PrimitiveRadicalOrbitPoints PrimitiveRadicalOrbitGenericPoints PrimitiveRadicalSliceField
open NativeGenericPullbackEvaluation

local instance closureCharZero : CharZero closure := PrimitiveExtensionFieldBridge.charZero_extension closure

/-- The genuine algebraic source-field extension supplies actual generic
points above every original constant symplectic action, whose actual reduced
generic points are related by the actual stabilizer matrix. -/
theorem exists_reduced_relation_for_constant_action (g : PrimitiveConstantFieldAction.Sp6) :
    ∃ s : sourceField →ₐ[ℂ] closure,
      s.comp PrimitiveRadicalOrbitDominance.functionFieldEmbedding =
        (PrimitiveRadicalOrbitEmbeddingExtension.inclusion.comp
          PrimitiveRadicalOrbitDominance.functionFieldEmbedding).comp
            (PrimitiveConstantFieldAction.fieldPullback g).toAlgHom ∧
      ∃ w : ReducedGraphAction.Stabilizer closure,
        PrimitiveReducedFieldMatrixAction.fieldAction closure
          (ReducedGraphAction.matrixRepresentation closure w)⁻¹
            (point (PrimitiveRadicalOrbitEmbeddingExtension.inclusion.comp sliceEmbedding).toRingHom) =
          point (s.comp sliceEmbedding).toRingHom := by
  obtain ⟨s,hs⟩ := PrimitiveRadicalOrbitEmbeddingExtension.exists_extension
    (PrimitiveConstantFieldAction.fieldPullback g)
  let y := sourcePoint closure PrimitiveRadicalOrbitEmbeddingExtension.inclusion
  let z := sourcePoint closure s
  have ha : PrimitiveFieldMatrixAction.actPoint closure
      (PrimitiveConstantOriginalExtension.extendConstant closure g)
        (nativePoint closure y) (nativePoint_projection closure y) = nativePoint closure z := by
    calc
      PrimitiveFieldMatrixAction.actPoint closure
          (PrimitiveConstantOriginalExtension.extendConstant closure g)
            (nativePoint closure y) (nativePoint_projection closure y) =
        nativePoint closure y ≫ PrimitiveConstantFieldAction.schemeMap g :=
          PrimitiveConstantOriginalExtension.actPoint_extendConstant closure g _ _
      _ = point ((PrimitiveRadicalOrbitEmbeddingExtension.inclusion.comp
          PrimitiveRadicalOrbitDominance.functionFieldEmbedding).toRingHom.comp
            (PrimitiveConstantFieldAction.fieldPullback g).toRingHom) := by
        rw [nativePoint_sourcePoint]
        exact NativeGenericPointNaturality.constant_action _ g
      _ = nativePoint closure z := by
        rw [nativePoint_sourcePoint,hs]
        rfl
  obtain ⟨w,hw⟩ := PrimitiveRadicalEquivariantKernelPairs.exists_reduced_relation_of_native_action
    closure (PrimitiveConstantOriginalExtension.extendConstant closure g) y z ha
  refine ⟨s,hs,w,?_⟩
  rw [← slicePoint_sourcePoint,← slicePoint_sourcePoint]
  exact hw

end M9Native.PrimitiveRadicalConstantEquivariance
