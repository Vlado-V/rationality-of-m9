module

public import M9StacksIntegration.PrimitiveReducedFamilyComparison
public import M9StacksIntegration.SL3ExtensionInvariance

@[expose] public section

/-! Genuine full-stabilizer extension-value invariance in the exact original
native matrix field-point convention. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory

namespace M9Native.PrimitiveReducedExtensionValues
open PrimitiveReducedFieldMatrixAction PrimitiveReducedFamilyComparison
open NativeGenericPullbackEvaluation

variable (K : Type) [Field K] [Algebra ℂ K]
local instance extensionCharZero : CharZero K := PrimitiveExtensionFieldBridge.charZero_extension K

/-- Original complex stabilizer fixedness implies value equality at every
actual extension-field stabilizer-related pair of generic native points. -/
theorem eq_of_constant_fixed (f : SliceField)
    (hf : ∀ w : ReducedGraphAction.Stabilizer ℂ,
      ReducedGraphAction.nativeFieldRepresentation ℂ w f = f)
    (w : ReducedGraphAction.Stabilizer K) (s t : SliceField →ₐ[ℂ] K)
    (h : fieldAction K (ReducedGraphAction.matrixRepresentation K w) (point s.toRingHom) =
      point t.toRingHom) : s f = t f := by
  have ht : (SL3UniversalFieldAction.parameterPoint w.left s).left ≫
      SL3ExtensionInvariance.fullActionMap w.right = point t.toRingHom := by
    change fullPoint K w.left w.right s = point t.toRingHom
    rw [fullPoint_eq,SemidirectProduct.inl_left_mul_inr_right]
    exact h
  exact SL3ExtensionInvariance.eq_of_constant_H_fixed f hf w.left w.right s t ht

theorem eq_of_constant_fixed_inverse (f : SliceField)
    (hf : ∀ w : ReducedGraphAction.Stabilizer ℂ,
      ReducedGraphAction.nativeFieldRepresentation ℂ w f = f)
    (w : ReducedGraphAction.Stabilizer K) (s t : SliceField →ₐ[ℂ] K)
    (h : fieldAction K (ReducedGraphAction.matrixRepresentation K w)⁻¹ (point s.toRingHom) =
      point t.toRingHom) : s f = t f := by
  apply eq_of_constant_fixed K f hf w⁻¹ s t
  simpa only [map_inv] using h

/-- Every geometric field-valued test of the actual target-field kernel pair
is discharged by the proved actual stabilizer relation and full H promotion. -/
theorem eq_on_target_kernel_pair (f : SliceField)
    (hf : ∀ w : ReducedGraphAction.Stabilizer ℂ,
      ReducedGraphAction.nativeFieldRepresentation ℂ w f = f)
    (s t : PrimitiveRadicalOrbitFamily.source.functionField →ₐ[ℂ] K)
    (h : s.comp PrimitiveRadicalOrbitDominance.functionFieldEmbedding =
      t.comp PrimitiveRadicalOrbitDominance.functionFieldEmbedding) :
    s (PrimitiveRadicalSliceField.sliceEmbedding f) = t (PrimitiveRadicalSliceField.sliceEmbedding f) := by
  obtain ⟨w,hw⟩ := field_kernel_pair_relation K s t h
  exact eq_of_constant_fixed_inverse K f hf w
    (s.comp PrimitiveRadicalSliceField.sliceEmbedding) (t.comp PrimitiveRadicalSliceField.sliceEmbedding) hw

end M9Native.PrimitiveReducedExtensionValues
