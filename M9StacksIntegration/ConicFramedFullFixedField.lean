module

public import M9StacksIntegration.ConicFramedEvenFixedField
public import M9StacksIntegration.ConicFramedRawOddEquivariance
public import M9StacksIntegration.FrameHomRawInvariantRationality

/-!
# The literal full joint fixed field in the moving conic-frame field

The original even joint field is intersected with fixedness under the
genuine ordinary odd operator. The proved raw embedding intertwines the
actual odd operators, so the original full raw fixed field maps exactly
onto this intersection. Its existing rational coordinates are retained.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 4096

namespace M9Native.ConicFramedFullFixedField

open M9.FrameHomFieldDescent (RawField)
open ConicFramedRawHomQuotient (embedding)

abbrev M := ConicFramedEvenFixedField.M
abbrev RawFullField := FrameHomRawInvariantRationality.fullFixedField
abbrev actualOrdinaryOdd : M ≃ₐ[ℂ] M := ConicFramedTwistAction.ordinaryOdd

attribute [local instance] ConicFramedEvenFixedField.movingField
attribute [local instance] ConicFramedEvenFixedField.jointComplexAlgebra

/-- The actual odd equalizer, retaining the original complex inclusion. -/
def oddFixedField : IntermediateField ℂ M where
  __ := M9.SemilinearInvolution.fixedField actualOrdinaryOdd.toRingEquiv
  algebraMap_mem' c := actualOrdinaryOdd.commutes c

/-- The literal full field inside the original moving-frame field. -/
def fullField : IntermediateField ℂ M := ConicFramedEvenFixedField.jointField ⊓ oddFixedField

local instance fullComplexAlgebra : Algebra ℂ fullField :=
  Subalgebra.algebra fullField.toSubalgebra

theorem mem_oddFixedField (z : M) :
    z ∈ oddFixedField ↔ ConicFramedTwistAction.ordinaryOdd z = z := Iff.rfl

theorem mem_fullField (z : M) :
    z ∈ fullField ↔ z ∈ ConicFramedEvenFixedField.jointField ∧
      ConicFramedTwistAction.ordinaryOdd z = z := Iff.rfl

theorem mem_fullField_actions (z : M) :
    z ∈ fullField ↔
      (∀ g : ProjectivePairSLFixedField.SL3, ConicFramedSLQuotient.coefficientTranslate g z = z) ∧
      (∀ g : M9.FrameBundleDescent.Even, ConicFramedGraphField.inducedRepresentation g z = z) ∧
      ConicFramedTwistAction.ordinaryOdd z = z := by
  rw [mem_fullField, ConicFramedEvenFixedField.mem_jointField]
  exact and_assoc

/-- Odd stability follows from the true raw odd comparison and genuine
finite-frame odd restriction; it is not an input to the field definition. -/
theorem ordinaryOdd_joint_stable {z : M} (hz : z ∈ ConicFramedEvenFixedField.jointField) :
    actualOrdinaryOdd z ∈ ConicFramedEvenFixedField.jointField := by
  obtain ⟨x, hx⟩ := (ConicFramedEvenFixedField.evenEmbedding_image_iff z).mpr hz
  change embedding (x : RawField) = z at hx
  let y := FrameHomRawFiniteOddDescent.fixedInversion x
  have hy : ConicFramedEvenFixedField.evenEmbedding y = actualOrdinaryOdd z := by
    calc
      ConicFramedEvenFixedField.evenEmbedding y =
          embedding (FrameHomRawOddCoordinates.rawInversion (x : RawField)) :=
        congrArg embedding (FrameHomRawFiniteOddDescent.inclusion_intertwines x).symm
      _ = actualOrdinaryOdd (embedding (x : RawField)) :=
        ConicFramedRawOddEquivariance.embedding_equivariant (x : RawField)
      _ = actualOrdinaryOdd z := congrArg actualOrdinaryOdd hx
  rw [← hy]
  exact ConicFramedEvenFixedField.evenEmbedding_mem_joint y

def fullInclusion : fullField →ₐ[ℂ] ConicFramedEvenFixedField.jointField where
  toFun z := ⟨z.val, z.property.1⟩
  map_zero' := Subtype.ext rfl
  map_one' := Subtype.ext rfl
  map_add' _ _ := Subtype.ext rfl
  map_mul' _ _ := Subtype.ext rfl
  commutes' _ := Subtype.ext rfl

theorem fullInclusion_coe (z : fullField) :
    ((fullInclusion z : ConicFramedEvenFixedField.jointField) : M) = (z : M) := rfl

def fullEmbedding : RawFullField →ₐ[ℂ] M :=
  ConicFramedEvenFixedField.evenEmbedding.comp FrameHomRawInvariantRationality.evenInclusion

theorem fullEmbedding_coe (z : RawFullField) : fullEmbedding z = embedding (z : RawField) := rfl

theorem fullEmbedding_mem (z : RawFullField) : fullEmbedding z ∈ fullField := by
  refine ⟨ConicFramedEvenFixedField.evenEmbedding_mem_joint
    (FrameHomRawInvariantRationality.evenInclusion z), ?_⟩
  exact (ConicFramedRawOddEquivariance.embedding_fixed_iff (z : RawField)).mpr z.property.2

/-- The original full raw invariants have exactly the literal full joint image. -/
theorem fullEmbedding_image_iff (z : M) :
    (∃ x : RawFullField, fullEmbedding x = z) ↔ z ∈ fullField := by
  constructor
  · rintro ⟨x, rfl⟩
    exact fullEmbedding_mem x
  · intro hz
    obtain ⟨x, hx⟩ := (ConicFramedEvenFixedField.evenEmbedding_image_iff z).mpr hz.1
    change embedding (x : RawField) = z at hx
    have ho : FrameHomRawOddCoordinates.rawInversion (x : RawField) = (x : RawField) := by
      apply (ConicFramedRawOddEquivariance.embedding_fixed_iff (x : RawField)).mp
      rw [hx]
      exact hz.2
    exact ⟨⟨x.val, x.property, ho⟩, hx⟩

theorem fullEmbedding_fieldRange : fullEmbedding.fieldRange = fullField := by
  ext z
  exact fullEmbedding_image_iff z

/-- The original full raw fixed field and the literal full joint field,
with their actual complex algebra structures and inclusion maps. -/
def rawFullEquiv : RawFullField ≃ₐ[ℂ] fullField :=
  fullEmbedding.equivFieldRange.trans (IntermediateField.equivOfEq fullEmbedding_fieldRange)

theorem rawFullEquiv_coe (z : RawFullField) :
    (rawFullEquiv z : M) = embedding (z : RawField) := rfl

theorem rawFullEquiv_coefficient (c : ℂ) :
    rawFullEquiv (algebraMap ℂ RawFullField c) =
      @algebraMap ℂ fullField _ _ fullComplexAlgebra c :=
  rawFullEquiv.commutes c

theorem rawFullEquiv_symm_coe (z : fullField) :
    embedding ((rawFullEquiv.symm z : RawFullField) : RawField) = (z : M) := by
  exact (rawFullEquiv_coe (rawFullEquiv.symm z)).symm.trans
    (congrArg (fun x : fullField => (x : M)) (rawFullEquiv.apply_symm_apply z))

theorem rawFullEquiv_even (z : RawFullField) :
    fullInclusion (rawFullEquiv z) =
      ConicFramedEvenFixedField.rawEvenEquiv (FrameHomRawInvariantRationality.evenInclusion z) := by
  apply Subtype.ext
  rfl

/-- Existing genuine raw invariant rational coordinates on the exact full field. -/
def rationalEquiv : fullField ≃ₐ[ℂ] M9.RationalField ℂ 24 :=
  rawFullEquiv.symm.trans FrameHomRawInvariantRationality.rationalEquiv

theorem rationalEquiv_rawFull (z : RawFullField) :
    rationalEquiv (rawFullEquiv z) = FrameHomRawInvariantRationality.rationalEquiv z := by
  change FrameHomRawInvariantRationality.rationalEquiv (rawFullEquiv.symm (rawFullEquiv z)) = _
  rw [AlgEquiv.symm_apply_apply]

theorem rationalEquiv_coefficient (c : ℂ) :
    rationalEquiv (@algebraMap ℂ fullField _ _ fullComplexAlgebra c) =
      algebraMap ℂ (M9.RationalField ℂ 24) c :=
  rationalEquiv.commutes c

theorem rationalEquiv_symm_coe (z : M9.RationalField ℂ 24) :
    (rationalEquiv.symm z : M) =
      embedding ((FrameHomRawInvariantRationality.rationalEquiv.symm z : RawFullField) : RawField) :=
  rawFullEquiv_coe (FrameHomRawInvariantRationality.rationalEquiv.symm z)

theorem fullField_rational : Nonempty (fullField ≃ₐ[ℂ] M9.RationalField ℂ 24) := ⟨rationalEquiv⟩

end M9Native.ConicFramedFullFixedField
