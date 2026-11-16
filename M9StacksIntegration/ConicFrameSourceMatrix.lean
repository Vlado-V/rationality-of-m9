module

public import M9StacksIntegration.ConicFrameSourceAlgebra
public import M9StacksIntegration.ConicFrameBaseChange

/-! Literal normalized matrices over the actual frame localization. -/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false

universe u

namespace M9Native.ConicFrameSourceMatrix

open M9Native.ConicFrame M9Native.ConicFrameProjective M9Native.ConicFrameCoordinates
open M9Native.ConicFrameCoordinateIndex M9Native.ConicFrameSourceAlgebra

theorem matrixInverse_map {R S : Type*} [CommRing R] [CommRing S]
    (φ : R →+* S) (A : Matrix (Fin 2) (Fin 2) R) (hA : IsUnit A.det) :
    A⁻¹.map φ = (A.map φ)⁻¹ := by
  apply Eq.symm
  apply Matrix.inv_eq_left_inv
  rw [← Matrix.map_mul,Matrix.nonsing_inv_mul _ hA,Matrix.map_one] <;> simp

variable (K : Type u) [Field K]

def sourceFrame : Mat3 (sourceRing K) :=
  (normalizedFrame K).map (algebraMap (polynomial K) (sourceRing K))

theorem sourceFrame_det_unit : IsUnit (sourceFrame K).det := by
  rw [sourceFrame,← RingHom.mapMatrix_apply,← RingHom.map_det]
  exact frame_det_unit K

theorem sourceQuotient_eq : quotientMatrix (sourceFrame K) =
    (quotientMatrix (normalizedFrame K)).map (algebraMap (polynomial K) (sourceRing K)) :=
  (quotientMatrix_map _ _).symm

theorem sourcePivot_eq : (quotientMatrix (sourceFrame K)).submatrix id pivotEmbedding =
    (pivot K).map (algebraMap (polynomial K) (sourceRing K)) := by
  rw [sourceQuotient_eq,Matrix.submatrix_map]
  rfl

theorem sourcePivot_det_eq : ((quotientMatrix (sourceFrame K)).submatrix id pivotEmbedding).det =
    algebraMap (polynomial K) (sourceRing K) (denominator K) := by
  rw [sourcePivot_eq,← RingHom.mapMatrix_apply,← RingHom.map_det]
  rfl

theorem sourcePivot_det_unit : IsUnit ((quotientMatrix (sourceFrame K)).submatrix id pivotEmbedding).det := by
  rw [sourcePivot_det_eq]
  exact denominator_unit K

theorem sourceNormalizedMatrix_eq :
    ((quotientMatrix (sourceFrame K)).submatrix id pivotEmbedding)⁻¹ * quotientMatrix (sourceFrame K) =
      inverseDenominator K • ((numeratorMatrix K).map (algebraMap (polynomial K) (sourceRing K))) := by
  rw [Matrix.inv_def,sourcePivot_det_eq,← (denominator_unit K).unit_spec,Ring.inverse_unit,
    Matrix.smul_mul,sourcePivot_eq,sourceQuotient_eq]
  have ha := (algebraMap (polynomial K) (sourceRing K)).map_adjugate (pivot K)
  rw [← RingHom.mapMatrix_apply,← ha,RingHom.mapMatrix_apply,← Matrix.map_mul]
  rfl

theorem sourceCoordinate_eq_entry (a : AlgebraicGeometry.Grassmannian.ChartIndex.{u}
    (k := 4) (n := 6) pivotEmbedding) :
    sourceCoordinate K (coordinateEquiv a) =
      (((quotientMatrix (sourceFrame K)).submatrix id pivotEmbedding)⁻¹ *
        quotientMatrix (sourceFrame K)) a.down.2 a.down.1.val := by
  rw [sourceNormalizedMatrix_eq]
  have hrow := coordinateEquiv_symm_row (coordinateEquiv a)
  have hcol := coordinateEquiv_symm_column (coordinateEquiv a)
  rw [Equiv.symm_apply_apply] at hrow hcol
  simp only [sourceCoordinate,numerator,coordinatePair,Matrix.smul_apply,Matrix.map_apply,smul_eq_mul]
  rw [← hrow,← hcol]

end M9Native.ConicFrameSourceMatrix
