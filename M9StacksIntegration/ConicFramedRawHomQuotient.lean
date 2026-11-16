module

public import M9StacksIntegration.ConicFramedSLQuotient
public import M9StacksIntegration.FrameHomRawMatrixCoordinates

/-!
# The actual raw Hom field inside the conic-frame coefficient quotient

The proved raw tensor-evaluation matrix coordinates are composed with
the proved coefficient quotient by the actual infinite native SL3.
The image is characterized by that actual coefficient action, and the
original coefficient inclusion and all sixteen raw entries are retained.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option maxRecDepth 4096

open MvPolynomial

namespace M9Native.ConicFramedRawHomQuotient

abbrev RawField := M9.FrameHomFieldDescent.RawField
abbrev CoefficientField := M9.FrameBundleDescent.Ambient
abbrev ConicM := ConicFramedSLQuotient.M

/-- The actual raw-coordinate inverse followed by the actual SL3
coefficient quotient inclusion. No field identification is assumed. -/
def embedding : RawField →ₐ[ℂ] ConicM :=
  ConicFramedSLQuotient.quotientEmbedding.comp
    (FrameHomRawMatrixCoordinates.fieldEquiv.symm.restrictScalars ℂ).toAlgHom

/-- The composition on the proved original matrix-field coordinates. -/
theorem embedding_fieldEquiv (x : ConicFramedSLQuotient.QuotientField) :
    embedding (FrameHomRawMatrixCoordinates.fieldEquiv x) =
      ConicFramedSLQuotient.quotientEmbedding x := by
  change ConicFramedSLQuotient.quotientEmbedding
    (FrameHomRawMatrixCoordinates.fieldEquiv.symm
      (FrameHomRawMatrixCoordinates.fieldEquiv x)) = _
  rw [AlgEquiv.symm_apply_apply]

theorem embedding_injective : Function.Injective embedding := embedding.injective

/-- The literal image consists exactly of the functions fixed by the
actual native SL3 coefficient action. -/
theorem embedding_image_iff (f : ConicM) :
    (∃ x : RawField, embedding x = f) ↔
      ∀ g : ProjectivePairSLFixedField.SL3,
        ConicFramedSLQuotient.coefficientTranslate g f = f := by
  rw [← ConicFramedSLQuotient.quotientEmbedding_image_iff f]
  constructor
  · rintro ⟨x, hx⟩
    exact ⟨FrameHomRawMatrixCoordinates.fieldEquiv.symm x, hx⟩
  · rintro ⟨x, hx⟩
    exact ⟨FrameHomRawMatrixCoordinates.fieldEquiv x, (embedding_fieldEquiv x).trans hx⟩

/-- Every actual raw Hom function has SL3-fixed coefficient image. -/
theorem embedding_fixed (x : RawField) (g : ProjectivePairSLFixedField.SL3) :
    ConicFramedSLQuotient.coefficientTranslate g (embedding x) = embedding x :=
  (embedding_image_iff (embedding x)).mp ⟨x, rfl⟩ g

/-- All original ambient coefficients retain the original quotient inclusion. -/
theorem embedding_constant (a : CoefficientField) :
    embedding (algebraMap CoefficientField RawField a) =
      algebraMap ConicFramedSLQuotient.B ConicM
        (ConicFramedSLQuotient.coefficientEmbedding a) := by
  rw [← FrameHomRawMatrixCoordinates.fieldEquiv_constant a, embedding_fieldEquiv]
  exact ConicFramedSLQuotient.quotientEmbedding_constant a

/-- Explicit values through the original actual native SL3 quotient
equivalence, rather than through an assumed coefficient identification. -/
theorem embedding_constant_native (a : CoefficientField) :
    embedding (algebraMap CoefficientField RawField a) =
      algebraMap ConicFramedSLQuotient.B ConicM
        ((ProjectivePairSLFixedField.nativeSLQuotientEquiv a).val) :=
  embedding_constant a

/-- The entire original raw polynomial ring is transported through the
proved matrix polynomial coordinates and actual coefficient inclusion. -/
theorem embedding_polynomial (p : FrameHomRawMatrixCoordinates.PolynomialRing) :
    embedding (algebraMap M9.FrameHomFieldDescent.RawRing RawField
      (FrameHomRawMatrixCoordinates.polynomialEquiv p)) =
        ConicFramedSLQuotient.polynomialToField p := by
  rw [← FrameHomRawMatrixCoordinates.fieldEquiv_polynomial p,
    embedding_fieldEquiv, ConicFramedSLQuotient.quotientEmbedding_polynomial]

/-- Every actual degree-one raw matrix functional is the corresponding
original independent conic-frame variable. -/
theorem embedding_coordinate (ij : FrameHomRawMatrixCoordinates.Index) :
    embedding (algebraMap M9.FrameHomFieldDescent.RawRing RawField
      (SymmetricAlgebra.ι CoefficientField M9.FrameHomFieldDescent.RawDual
        (FrameHomRawMatrixCoordinates.coordinateBasis ij))) =
      algebraMap (MvPolynomial M9.GraphBundleDescent.FiberIndex ConicFramedSLQuotient.B)
        ConicM (X ij) := by
  rw [← FrameHomRawMatrixCoordinates.fieldEquiv_X ij,
    embedding_fieldEquiv, ConicFramedSLQuotient.quotientEmbedding_variable]

/-- The literal original raw Hom matrix has exactly the original
sixteen independent matrix entries after inclusion. -/
theorem embedding_rawMatrix (i j : Fin 4) :
    embedding (FrameHomRawMatrixCoordinates.rawMatrix i j) =
      algebraMap (MvPolynomial M9.GraphBundleDescent.FiberIndex ConicFramedSLQuotient.B)
        ConicM (X (i, j)) :=
  embedding_coordinate (i, j)

end M9Native.ConicFramedRawHomQuotient
