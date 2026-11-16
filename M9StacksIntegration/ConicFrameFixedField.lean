module

public import M9StacksIntegration.ConicFrameGammaInvariant
public import M9StacksIntegration.ConicFrameNativeActionCoordinates
public import M9StacksIntegration.ConicFrameDegree
public import Mathlib.FieldTheory.Fixed
public import Mathlib.FieldTheory.IntermediateField.Algebraic

/-! The image of the actual dominant conic-frame morphism is exactly the
fixed field of the actual right tetrahedral action on native projective
matrix space. The two field degrees are derived independently, from the
actual closed fibres and from faithful finite-group Galois theory. -/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace M9Native.ConicFrameFixedField

open ConicFrameGammaAction ConicFrameFieldComparison ConicFrameNativeGeometry
open ConicFrameNativeActionCoordinates ConicFrameRationalGamma

abbrev grassmannianField := (GrassmannianCharts.space ℂ 4 6).functionField

local instance : MulSemiringAction Gamma projectiveField := fieldAction

local instance action_faithful : FaithfulSMul Gamma projectiveField := by
  refine ⟨fun {g h} heq => fieldRepresentation_injective ?_⟩
  ext x
  exact heq x

def fixedField : IntermediateField ℂ projectiveField where
  __ := FixedPoints.subfield Gamma projectiveField
  algebraMap_mem' c g := (fieldRepresentation g).commutes c

def imageField : IntermediateField ℂ projectiveField :=
  (functionFieldEmbedding ℂ).fieldRange

theorem rational_action_comparison (g : Gamma) (x : projectiveField) :
    projectiveNativeEquiv ℂ (fieldRepresentation g x) =
      rationalRepresentation g (projectiveNativeEquiv ℂ x) := by
  rw [fieldRepresentation_apply,namedFieldEquiv]
  change M9.ProjectiveFunctionField.functionFieldEquiv 8 0
      (M9.FrameProjectiveGeometry.fieldRepresentation (rightEmbedding g)
        (nativeFieldEquiv.symm x)) =
    M9.ProjectiveFunctionField.functionFieldEquiv 8 0
      (M9.FrameProjectiveGeometry.fieldRepresentation (rightEmbedding g)
        ((M9.ProjectiveFunctionField.functionFieldEquiv 8 0).symm
          (projectiveNativeEquiv ℂ x)))
  have hx : projectiveNativeEquiv ℂ x =
      M9.ProjectiveFunctionField.functionFieldEquiv 8 0 (nativeFieldEquiv.symm x) := by
    simpa only [AlgEquiv.apply_symm_apply] using namedFieldEquiv (nativeFieldEquiv.symm x)
  rw [hx,AlgEquiv.symm_apply_apply]

theorem embedding_fixed (g : Gamma) (z : grassmannianField) :
    fieldRepresentation g (functionFieldEmbedding ℂ z) = functionFieldEmbedding ℂ z := by
  apply (projectiveNativeEquiv ℂ).injective
  rw [rational_action_comparison,embedding_comparison,
    ConicFrameGammaInvariant.targetFieldEmbedding_fixed]

theorem image_le_fixed : imageField ≤ fixedField := by
  rintro x ⟨z,rfl⟩ g
  exact embedding_fixed g z

theorem image_finrank : Module.finrank imageField projectiveField = 24 := by
  have hh := Algebra.finrank_eq_of_equiv_equiv
    (functionFieldEmbedding ℂ).equivFieldRange.toRingEquiv (RingEquiv.refl projectiveField)
    (by
      apply RingHom.ext
      intro z
      rfl)
  exact hh.symm.trans ConicFrameDegree.native_field_finrank

local instance image_finite : Module.Finite imageField projectiveField := by
  apply Module.finite_of_finrank_pos
  rw [image_finrank]
  norm_num

theorem fixed_finrank : Module.finrank fixedField projectiveField = 24 := by
  change Module.finrank (FixedPoints.subfield Gamma projectiveField) projectiveField = 24
  rw [FixedPoints.finrank_eq_card,M9.TetrahedralGroup.card_gamma]

/-- The actual morphism's subfield, not an independently stipulated
quotient field, is the full right-Γ fixed field. -/
theorem image_eq_fixed : imageField = fixedField :=
  IntermediateField.eq_of_le_of_finrank_eq' image_le_fixed
    (image_finrank.trans fixed_finrank.symm)

def embeddingIntoFixed : grassmannianField →ₐ[ℂ] fixedField where
  toFun z := ⟨functionFieldEmbedding ℂ z,fun g => embedding_fixed g z⟩
  map_one' := Subtype.ext ((functionFieldEmbedding ℂ).map_one)
  map_zero' := Subtype.ext ((functionFieldEmbedding ℂ).map_zero)
  map_add' x y := Subtype.ext ((functionFieldEmbedding ℂ).map_add x y)
  map_mul' x y := Subtype.ext ((functionFieldEmbedding ℂ).map_mul x y)
  commutes' c := Subtype.ext ((functionFieldEmbedding ℂ).commutes c)

/-- The native Grassmannian generic stalk is isomorphic, over its actual
complex structure map, to the actual right tetrahedral fixed field. -/
def nativeGrassmannianFixedFieldEquiv : grassmannianField ≃ₐ[ℂ] fixedField :=
  AlgEquiv.ofBijective embeddingIntoFixed ⟨embeddingIntoFixed.injective,by
    intro x
    have hx : (x : projectiveField) ∈ imageField := by
      rw [image_eq_fixed]
      exact x.property
    obtain ⟨z,hz⟩ := hx
    exact ⟨z,Subtype.ext hz⟩⟩

@[simp] theorem nativeGrassmannianFixedFieldEquiv_coe (z : grassmannianField) :
    (nativeGrassmannianFixedFieldEquiv z : projectiveField) = functionFieldEmbedding ℂ z := rfl

end M9Native.ConicFrameFixedField
