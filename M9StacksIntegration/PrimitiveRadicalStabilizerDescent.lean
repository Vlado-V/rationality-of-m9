module

public import M9StacksIntegration.PrimitiveReducedExtensionValues
public import M9StacksIntegration.PrimitiveRadicalConstantEquivariance
public import M9StacksIntegration.PrimitiveRadicalInvariantDescent
public import M9StacksIntegration.ReducedGraphTwistedAction

@[expose] public section

/-! Actual stabilizer invariant functions descend through the genuine native
orbit-family field embedding, and their descended functions are symplectic
invariants. Every geometric field-point test is proved, not assumed. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace M9Native.PrimitiveRadicalStabilizerDescent
open PrimitiveRadicalInvariantDescent PrimitiveRadicalSliceField

/-- Full actual stabilizer fixedness discharges every geometric field-valued
kernel-pair test for the actual native target-field image. -/
theorem invariant_mem_target_image (f : sliceField)
    (hf : ∀ w : ReducedGraphAction.Stabilizer ℂ,
      ReducedGraphAction.nativeFieldRepresentation ℂ w f = f) :
    sliceEmbedding f ∈ Set.range PrimitiveRadicalOrbitDominance.functionFieldEmbedding := by
  have : CharZero targetField := PrimitiveExtensionFieldBridge.charZero_extension targetField
  change sliceEmbedding f ∈ Set.range (algebraMap targetField sourceField)
  apply (FieldPointDescent.mem_range_iff_forall_algClosed_embeddings_charZero targetField _).mpr
  intro L _ _ _ s t
  let : Algebra ℂ L := ((algebraMap targetField L).comp (algebraMap ℂ targetField)).toAlgebra
  have : IsScalarTower ℂ targetField L := IsScalarTower.of_algebraMap_eq' rfl
  let sC : sourceField →ₐ[ℂ] L := s.restrictScalars ℂ
  let tC : sourceField →ₐ[ℂ] L := t.restrictScalars ℂ
  have he : sC.comp PrimitiveRadicalOrbitDominance.functionFieldEmbedding =
      tC.comp PrimitiveRadicalOrbitDominance.functionFieldEmbedding := by
    apply AlgHom.ext
    intro x
    exact (s.commutes x).trans (t.commutes x).symm
  exact PrimitiveReducedExtensionValues.eq_on_target_kernel_pair L f hf sC tC he

/-- The actual algebraic source extension above a constant native target
automorphism proves that every such descended function is genuinely fixed. -/
theorem lift_fixed (f : sliceField)
    (hf : ∀ w : ReducedGraphAction.Stabilizer ℂ,
      ReducedGraphAction.nativeFieldRepresentation ℂ w f = f)
    (a : targetField) (ha : PrimitiveRadicalOrbitDominance.functionFieldEmbedding a = sliceEmbedding f) :
    a ∈ nativeFixedField := by
  apply (mem_nativeFixedField_iff a).mpr
  intro g
  obtain ⟨s,hs,w,hw⟩ := PrimitiveRadicalConstantEquivariance.exists_reduced_relation_for_constant_action g
  have hv := PrimitiveReducedExtensionValues.eq_of_constant_fixed_inverse
    PrimitiveRadicalOrbitEmbeddingExtension.closure f hf w
      (PrimitiveRadicalOrbitEmbeddingExtension.inclusion.comp sliceEmbedding) (s.comp sliceEmbedding) hw
  apply PrimitiveRadicalOrbitDominance.functionFieldEmbedding.injective
  apply PrimitiveRadicalOrbitEmbeddingExtension.inclusion.injective
  calc
    PrimitiveRadicalOrbitEmbeddingExtension.inclusion
        (PrimitiveRadicalOrbitDominance.functionFieldEmbedding (PrimitiveConstantFieldAction.fieldPullback g a)) =
      s (PrimitiveRadicalOrbitDominance.functionFieldEmbedding a) := (DFunLike.congr_fun hs a).symm
    _ = s (sliceEmbedding f) := congrArg s ha
    _ = PrimitiveRadicalOrbitEmbeddingExtension.inclusion (sliceEmbedding f) := hv.symm
    _ = PrimitiveRadicalOrbitEmbeddingExtension.inclusion
        (PrimitiveRadicalOrbitDominance.functionFieldEmbedding a) :=
      congrArg PrimitiveRadicalOrbitEmbeddingExtension.inclusion ha.symm

/-- The actual invariant restriction covers every element of the actual
native stabilizer fixed field. -/
theorem restriction_covers_stabilizer (f : ReducedGraphTwistedAction.nativeHFixedField) :
    ∃ a : nativeFixedField, restriction a = f.val := by
  have hf := (ReducedGraphTwistedAction.mem_nativeHFixedField_iff f.val).mp f.property
  obtain ⟨a,ha⟩ := invariant_mem_target_image f.val hf
  let a' : nativeFixedField := ⟨a,lift_fixed f.val hf a ha⟩
  refine ⟨a',?_⟩
  apply sliceEmbedding.injective
  change sliceEmbedding (restriction a') = sliceEmbedding f.val
  rw [restriction_spec]
  exact ha

end M9Native.PrimitiveRadicalStabilizerDescent
