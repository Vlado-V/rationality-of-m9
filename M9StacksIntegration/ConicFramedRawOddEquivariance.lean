module

public import M9StacksIntegration.ConicFramedTwistAction
public import M9StacksIntegration.ConicFramedRawHomQuotient
public import M9StacksIntegration.FrameHomRawOddCoordinates

/-!
# The original raw-Hom odd operator inside the conic-frame field

The actual ambient coefficient embedding intertwines the original transpose
with the original projective frame swap. The genuine raw matrix maps to the
sixteen conic-frame variables, so its inverse maps to their inverse. These
generator identities identify the two already constructed field maps.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

open Matrix

namespace M9Native.ConicFramedRawOddEquivariance

open M9.FrameBundleDescent (Ambient nativeTranspose)
open M9.FrameHomFieldDescent (RawField)
open FrameHomRawMatrixCoordinates
open FrameHomRawOddCoordinates (rawInversion)
open ConicFramedGraphField (M genericRawMatrix)
open ConicFramedRawHomQuotient (embedding)
open ConicFramedTwistAction (ordinaryOdd)

/-- The coefficient comparison uses the original native projective pair swap. -/
theorem coefficientEmbedding_transpose (a : Ambient) :
    PairProjectiveEquivariance.projectivePairSwap
        (ConicFramedSLQuotient.coefficientEmbedding a) =
      ConicFramedSLQuotient.coefficientEmbedding (nativeTranspose a) := by
  have ht : M9.FrameProjectiveGeometry.fieldRepresentation
      M9.FrameAction.FrameGroup.tau a = nativeTranspose a := by
    delta M9.FrameBundleDescent.nativeTranspose
    rfl
  exact (ConicFramedSLQuotient.coefficientEmbedding_pairSwap a).trans
    (congrArg ConicFramedSLQuotient.coefficientEmbedding ht)

/-- The original raw matrix retains the original independent matrix entries. -/
theorem embedding_rawMatrix : rawMatrix.map embedding.toRingHom = genericRawMatrix := by
  ext i j
  exact ConicFramedRawHomQuotient.embedding_rawMatrix i j

/-- Nonsingularity of the actual raw matrix follows from its proved coordinates. -/
theorem rawMatrix_det_ne_zero : rawMatrix.det ≠ 0 := by
  intro h
  apply ConicFramedTwistAction.genericRawMatrix_det_ne_zero
  have hd := embedding.map_det rawMatrix
  change embedding rawMatrix.det =
    (rawMatrix.map embedding.toRingHom).det at hd
  rw [embedding_rawMatrix, h, map_zero] at hd
  exact hd.symm

/-- The field embedding carries the actual matrix inverse to the actual inverse. -/
theorem embedding_rawMatrix_inv :
    (rawMatrix⁻¹).map embedding.toRingHom = genericRawMatrix⁻¹ := by
  have hi := M9.map_matrix_inverse embedding.toRingHom rawMatrix rawMatrix_det_ne_zero
  change (rawMatrix⁻¹).map embedding.toRingHom =
    (rawMatrix.map embedding.toRingHom)⁻¹ at hi
  rw [embedding_rawMatrix] at hi
  exact hi

/-- Odd compatibility on every original ambient coefficient. -/
theorem embedding_equivariant_coefficient (a : Ambient) :
    embedding (rawInversion (algebraMap Ambient RawField a)) =
      ordinaryOdd (embedding (algebraMap Ambient RawField a)) := by
  rw [FrameHomRawOddCoordinates.rawInversion_constant,
    ConicFramedRawHomQuotient.embedding_constant,
    ConicFramedRawHomQuotient.embedding_constant,
    ConicFramedTwistAction.ordinaryOdd_constant, coefficientEmbedding_transpose]

/-- Both odd operators have the same literal inverse-matrix image. -/
theorem embedding_rawInversion_matrix :
    (rawMatrix.map rawInversion.toRingHom).map embedding.toRingHom =
      genericRawMatrix.map ordinaryOdd.toRingHom := by
  rw [FrameHomRawOddCoordinates.rawInversion_matrix, embedding_rawMatrix_inv,
    ConicFramedTwistAction.ordinaryOdd_matrix]

/-- The two actual field homomorphisms agree on the genuine generators. -/
theorem embedding_equivariant_hom :
    embedding.toRingHom.comp rawInversion.toRingHom =
      ordinaryOdd.toRingHom.comp embedding.toRingHom := by
  apply FrameHomRawOddCoordinates.rawFieldHom_ext
  · intro a
    exact embedding_equivariant_coefficient a
  · intro i j
    change embedding (rawInversion (rawMatrix i j)) = ordinaryOdd (embedding (rawMatrix i j))
    have hX := congrFun (congrFun embedding_rawMatrix i) j
    change embedding (rawMatrix i j) = genericRawMatrix i j at hX
    rw [hX]
    exact congrFun (congrFun embedding_rawInversion_matrix i) j

/-- The actual raw-Hom inclusion intertwines the original odd involution. -/
theorem embedding_equivariant (z : RawField) :
    embedding (rawInversion z) = ordinaryOdd (embedding z) :=
  RingHom.congr_fun embedding_equivariant_hom z

/-- Odd fixedness is retained by the injective original raw-Hom inclusion. -/
theorem embedding_fixed_iff (z : RawField) :
    ordinaryOdd (embedding z) = embedding z ↔ rawInversion z = z := by
  constructor
  · intro h
    apply ConicFramedRawHomQuotient.embedding_injective
    exact (embedding_equivariant z).trans h
  · intro h
    exact (embedding_equivariant z).symm.trans (congrArg embedding h)

end M9Native.ConicFramedRawOddEquivariance
