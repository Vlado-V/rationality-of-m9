module

public import M9StacksIntegration.ConicFramedRawGammaEquivariance

/-!
# The literal joint even fixed field in the moving conic-frame field

The actual native SL3 coefficient-fixed image is intersected with the
fixed field of the genuine induced finite deck action. The original raw
even fixed field maps isomorphically onto this literal intersection, by
the proved embedding and its actual deck equivariance. No commutation,
field identification, or action comparison is supplied as a premise.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 4096

namespace M9Native.ConicFramedEvenFixedField

open M9.FrameBundleDescent (Ambient Even ConnectedField)
open M9.FrameHomFieldDescent
open ConicFramedRawHomQuotient (embedding)
open ConicFramedGraphField (inducedRepresentation)

abbrev M := ConicFramedRawHomQuotient.ConicM
abbrev RawEvenField := M9.FrameHomFieldDescent.RawFixedField

local instance movingField : Field M :=
  FractionRing.field (MvPolynomial M9.GraphBundleDescent.FiberIndex ConicFramedSLQuotient.B)

/-- The actual coefficient-fixed image, with its original complex inclusion. -/
def coefficientFixedField : IntermediateField ℂ M := embedding.fieldRange

/-- The fixed field of the existing genuine induced deck representation. -/
def gammaFixedField : IntermediateField ℂ M :=
  IntermediateField.fixedField ConicFramedGraphField.inducedRepresentation.range

/-- The literal intersection in the original moving-frame field. -/
def jointField : IntermediateField ℂ M := coefficientFixedField ⊓ gammaFixedField

local instance jointComplexAlgebra : Algebra ℂ jointField :=
  Subalgebra.algebra jointField.toSubalgebra

theorem mem_coefficientFixedField (z : M) :
    z ∈ coefficientFixedField ↔
      ∀ g : ProjectivePairSLFixedField.SL3,
        ConicFramedSLQuotient.coefficientTranslate g z = z := by
  change (∃ x : RawField, embedding x = z) ↔ _
  exact ConicFramedRawHomQuotient.embedding_image_iff z

theorem mem_gammaFixedField (z : M) :
    z ∈ gammaFixedField ↔ ∀ g : Even, inducedRepresentation g z = z := by
  rw [gammaFixedField, IntermediateField.mem_fixedField_iff]
  constructor
  · intro h g
    exact h (inducedRepresentation g) ⟨g, rfl⟩
  · rintro h σ ⟨g, rfl⟩
    exact h g

theorem mem_jointField (z : M) :
    z ∈ jointField ↔
      (∀ g : ProjectivePairSLFixedField.SL3,
        ConicFramedSLQuotient.coefficientTranslate g z = z) ∧
      ∀ g : Even, inducedRepresentation g z = z := by
  change (z ∈ coefficientFixedField ∧ z ∈ gammaFixedField) ↔ _
  rw [mem_coefficientFixedField, mem_gammaFixedField]

/-- Stability is a consequence of the actual embedding equivariance. -/
theorem coefficientFixedField_gamma_stable (g : Even) {z : M}
    (hz : z ∈ coefficientFixedField) : inducedRepresentation g z ∈ coefficientFixedField := by
  obtain ⟨x, rfl⟩ := hz
  exact ⟨ConicFramedRawGammaEquivariance.rawTranslate g x,
    (ConicFramedRawGammaEquivariance.embedding_equivariant g x).symm⟩

theorem coefficient_fixed_gamma_stable (g : Even) (z : M)
    (hz : ∀ h : ProjectivePairSLFixedField.SL3,
      ConicFramedSLQuotient.coefficientTranslate h z = z) :
    ∀ h : ProjectivePairSLFixedField.SL3,
      ConicFramedSLQuotient.coefficientTranslate h (inducedRepresentation g z) =
        inducedRepresentation g z :=
  (mem_coefficientFixedField _).mp
    (coefficientFixedField_gamma_stable g ((mem_coefficientFixedField z).mpr hz))

/-- Inclusion of the original even fixed field with its existing complex algebra. -/
def rawEvenInclusion : RawEvenField →ₐ[ℂ] RawField where
  toFun z := z.val
  map_zero' := rfl
  map_one' := rfl
  map_add' _ _ := rfl
  map_mul' _ _ := rfl
  commutes' c := by
    exact (rawFixedComplexAlgebra_coe c).trans
      (IsScalarTower.algebraMap_apply ℂ Ambient RawField c).symm

theorem rawEvenInclusion_coe (z : RawEvenField) : rawEvenInclusion z = (z : RawField) := rfl

theorem rawEvenInclusion_coefficient (c : ℂ) :
    rawEvenInclusion (algebraMap ℂ RawEvenField c) = algebraMap ℂ RawField c :=
  rawEvenInclusion.commutes c

def evenEmbedding : RawEvenField →ₐ[ℂ] M := embedding.comp rawEvenInclusion

theorem evenEmbedding_coe (z : RawEvenField) : evenEmbedding z = embedding (z : RawField) := rfl

theorem evenEmbedding_mem_joint (z : RawEvenField) : evenEmbedding z ∈ jointField := by
  refine ⟨⟨z.val, rfl⟩, ?_⟩
  exact (mem_gammaFixedField _).mpr
    ((ConicFramedRawGammaEquivariance.embedding_fixed_iff_mem_rawFixedField z.val).mpr z.property)

/-- The actual image is exactly the literal joint fixed field. -/
theorem evenEmbedding_image_iff (z : M) :
    (∃ x : RawEvenField, evenEmbedding x = z) ↔ z ∈ jointField := by
  constructor
  · rintro ⟨x, rfl⟩
    exact evenEmbedding_mem_joint x
  · rintro ⟨hx, hΓ⟩
    obtain ⟨x, hx⟩ := hx
    change embedding x = z at hx
    have hg : ∀ g : Even, inducedRepresentation g (embedding x) = embedding x := by
      intro g
      rw [hx]
      exact (mem_gammaFixedField z).mp hΓ g
    refine ⟨⟨x, (ConicFramedRawGammaEquivariance.embedding_fixed_iff_mem_rawFixedField x).mp hg⟩, hx⟩

theorem evenEmbedding_fieldRange : evenEmbedding.fieldRange = jointField := by
  ext z
  exact evenEmbedding_image_iff z

/-- Genuine complex algebra equivalence from the original raw even invariants. -/
def rawEvenEquiv : RawEvenField ≃ₐ[ℂ] jointField :=
  evenEmbedding.equivFieldRange.trans (IntermediateField.equivOfEq evenEmbedding_fieldRange)

theorem rawEvenEquiv_coe (z : RawEvenField) :
    (rawEvenEquiv z : M) = embedding (z : RawField) := rfl

theorem rawEvenEquiv_coefficient (c : ℂ) :
    rawEvenEquiv (algebraMap ℂ RawEvenField c) =
      @algebraMap ℂ jointField _ _ jointComplexAlgebra c :=
  rawEvenEquiv.commutes c

theorem rawEvenEquiv_connected_coefficient (a : ConnectedField) :
    (rawEvenEquiv (algebraMap ConnectedField RawEvenField a) : M) =
      algebraMap ConicFramedSLQuotient.B M
        (ConicFramedSLQuotient.coefficientEmbedding (a : Ambient)) := by
  rw [rawEvenEquiv_coe, rawFixedConnectedAlgebra_coe]
  exact ConicFramedRawHomQuotient.embedding_constant (a : Ambient)

theorem rawEvenEquiv_symm_coe (z : jointField) :
    embedding ((rawEvenEquiv.symm z : RawEvenField) : RawField) = (z : M) := by
  exact (rawEvenEquiv_coe (rawEvenEquiv.symm z)).symm.trans
    (congrArg (fun x : jointField => (x : M)) (rawEvenEquiv.apply_symm_apply z))

/-- The existing genuine finite-frame descent identifies the same joint field
with the original descended isomorphism field. -/
def jointIsomEquiv : jointField ≃ₐ[ℂ] M9.FrameBundleDescent.Standard.IsomField :=
  rawEvenEquiv.symm.trans fixedFieldComplexEquiv

theorem jointIsomEquiv_rawEven (z : RawEvenField) :
    jointIsomEquiv (rawEvenEquiv z) = fixedFieldComplexEquiv z := by
  change fixedFieldComplexEquiv (rawEvenEquiv.symm (rawEvenEquiv z)) = _
  rw [AlgEquiv.symm_apply_apply]

theorem jointIsomEquiv_coefficient (c : ℂ) :
    jointIsomEquiv (@algebraMap ℂ jointField _ _ jointComplexAlgebra c) =
      algebraMap ℂ M9.FrameBundleDescent.Standard.IsomField c :=
  jointIsomEquiv.commutes c

theorem jointIsomEquiv_symm_coe (z : M9.FrameBundleDescent.Standard.IsomField) :
    (jointIsomEquiv.symm z : M) =
      embedding ((fixedFieldComplexEquiv.symm z : RawEvenField) : RawField) :=
  rawEvenEquiv_coe (fixedFieldComplexEquiv.symm z)

end M9Native.ConicFramedEvenFixedField
