module

public import M9StacksIntegration.ConicFramedGammaAction
public import M9StacksIntegration.ConicFramedRawHomQuotient
public import M9StacksIntegration.FrameHomRawMatrixAction
public import M9StacksIntegration.FrameHomRawOddCoordinates

/-! The actual original raw-Hom field embeds equivariantly into the literal
moving conic-frame field. Coefficients and the genuine sixteen raw matrix
entries determine the comparison of the two already constructed actions. -/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option maxRecDepth 4096

open Matrix

namespace M9Native.ConicFramedRawGammaEquivariance

open M9.FrameBundleDescent (Ambient Even)
open M9.FrameHomFieldDescent (RawField)
open ConicRawGammaMatrices FrameHomRawMatrixCoordinates
open ConicFramedGraphField (M inducedRepresentation genericRawMatrix)
open ConicFramedRawHomQuotient (embedding)

local instance ambientEvenAction : MulSemiringAction Even Ambient :=
  M9.FrameQuadraticExtension.evenAction

/-- The original contragredient raw-Hom field action, with its existing
instance explicitly pinned. -/
def rawTranslate (g : Even) : RawField →+* RawField :=
  @MulSemiringAction.toRingHom Even inferInstance RawField inferInstance
    M9.FrameHomFieldDescent.rawFieldAction g

/-- The original native SL3 coefficient quotient followed by the actual
coefficient inclusion in the moving-frame field. -/
def ambientEmbedding : Ambient →ₐ[ℂ] M :=
  (IsScalarTower.toAlgHom ℂ ConicFramedSLQuotient.B M).comp
    ConicFramedSLQuotient.coefficientEmbedding

theorem embedding_constant (a : Ambient) :
    embedding (algebraMap Ambient RawField a) = ambientEmbedding a :=
  ConicFramedRawHomQuotient.embedding_constant a

/-- On coefficients the deck comparison is the original native projective
matrix action restricted to the actual even frame subgroup. -/
theorem coefficientEmbedding_even (g : Even) (a : Ambient) :
    ConicGraphCoefficientDescent.frameRepresentation g
        (ConicFramedSLQuotient.coefficientEmbedding a) =
      ConicFramedSLQuotient.coefficientEmbedding
        (M9.FrameQuadraticExtension.evenRepresentation g a) := by
  exact (ConicGraphCoefficientDescent.frameRepresentation_apply g _).trans
    (ConicFramedSLQuotient.coefficientEmbedding_pairDeck g.1 g.2 a)

theorem rawTranslate_coefficient (g : Even) (a : Ambient) :
    rawTranslate g (algebraMap Ambient RawField a) =
      algebraMap Ambient RawField (M9.FrameQuadraticExtension.evenRepresentation g a) :=
  FrameHomRawMatrixAction.rawFieldAction_coefficient g a

theorem embedding_equivariant_coefficient (g : Even) (a : Ambient) :
    inducedRepresentation g (embedding (algebraMap Ambient RawField a)) =
      embedding (rawTranslate g (algebraMap Ambient RawField a)) := by
  rw [ConicFramedRawHomQuotient.embedding_constant,ConicFramedGammaAction.induced_constant,
    coefficientEmbedding_even,rawTranslate_coefficient,
    ConicFramedRawHomQuotient.embedding_constant]

/-- The embedding sends the original genuine raw matrix to the original
sixteen independent moving-frame variables. -/
theorem embedding_rawMatrix : rawMatrix.map embedding.toRingHom = genericRawMatrix := by
  ext i j
  exact ConicFramedRawHomQuotient.embedding_rawMatrix i j

theorem embedding_gammaK_matrix (g : Gamma) :
    ((gammaK Ambient g).val.map (algebraMap Ambient RawField)).map embedding.toRingHom =
      (gammaK M g).val := by
  have h := congrArg Units.val (map_gammaK Ambient ambientEmbedding g)
  calc
    _ = (gammaK Ambient g).val.map ambientEmbedding.toRingHom := by
      ext i j
      exact embedding_constant _
    _ = _ := h

theorem embedding_gammaK_inv_matrix (g : Gamma) :
    (((gammaK Ambient g)⁻¹).val.map (algebraMap Ambient RawField)).map embedding.toRingHom =
      ((gammaK M g)⁻¹).val := by
  simpa only [map_inv] using embedding_gammaK_matrix g⁻¹

theorem rawTranslate_matrix (g : Even) :
    rawMatrix.map (rawTranslate g) =
      (((gammaK Ambient g.2)⁻¹).val.map (algebraMap Ambient RawField)) * rawMatrix *
        ((gammaK Ambient g.1).val.map (algebraMap Ambient RawField)) :=
  FrameHomRawMatrixAction.rawFieldAction_matrix g

/-- Both existing actions have the same actual inverse-left/right matrix
law, with every complex gamma coefficient mapped through its original inclusion. -/
theorem embedding_rawTranslate_matrix (g : Even) :
    (rawMatrix.map (rawTranslate g)).map embedding.toRingHom =
      genericRawMatrix.map (inducedRepresentation g).toRingHom := by
  rw [rawTranslate_matrix,Matrix.map_mul,Matrix.map_mul,embedding_gammaK_inv_matrix,
    embedding_gammaK_matrix,embedding_rawMatrix]
  exact (ConicFramedGammaAction.induced_rawMatrix g).symm

/-- Equality of the two genuine field homomorphisms follows from their
actual coefficient and raw-matrix generators. -/
theorem embedding_equivariant_hom (g : Even) :
    (inducedRepresentation g).toRingHom.comp embedding.toRingHom =
      embedding.toRingHom.comp (rawTranslate g) := by
  apply FrameHomRawOddCoordinates.rawFieldHom_ext
  · intro a
    exact embedding_equivariant_coefficient g a
  · intro i j
    change inducedRepresentation g (embedding (rawMatrix i j)) =
      embedding (rawTranslate g (rawMatrix i j))
    rw [ConicFramedRawHomQuotient.embedding_rawMatrix]
    exact (congrFun (congrFun (embedding_rawTranslate_matrix g) i) j).symm

theorem embedding_equivariant (g : Even) (z : RawField) :
    inducedRepresentation g (embedding z) = embedding (rawTranslate g z) :=
  RingHom.congr_fun (embedding_equivariant_hom g) z

/-- Induced deck fixedness on the actual raw embedding image is exactly
fixedness for the original raw-Hom field action. -/
theorem embedding_fixed_iff (z : RawField) :
    (∀ g : Even, inducedRepresentation g (embedding z) = embedding z) ↔
      ∀ g : Even, M9.FrameHomFieldDescent.rawFieldAction.smul g z = z := by
  constructor
  · intro h g
    apply ConicFramedRawHomQuotient.embedding_injective
    exact (embedding_equivariant g z).symm.trans (h g)
  · intro h g
    exact (embedding_equivariant g z).trans (congrArg embedding (h g))

theorem embedding_fixed_iff_mem_rawFixedField (z : RawField) :
    (∀ g : Even, inducedRepresentation g (embedding z) = embedding z) ↔
      z ∈ M9.FrameHomFieldDescent.RawFixedField :=
  (embedding_fixed_iff z).trans (M9.FrameHomFieldDescent.mem_rawFixedField z).symm

/-- Membership in the actual moving graph-field image agrees with the
already proved finite-frame descent of the original raw-Hom field. -/
theorem embedding_graph_image_iff (z : RawField) :
    (∃ x : ConicFramedGraphField.FF, ConicFramedGraphField.embedding x = embedding z) ↔
      z ∈ M9.FrameHomFieldDescent.RawFixedField := by
  rw [ConicFramedGraphField.embedding_image_iff,embedding_fixed_iff_mem_rawFixedField]

end M9Native.ConicFramedRawGammaEquivariance
