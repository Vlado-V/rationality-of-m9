module

public import M9StacksIntegration.ConicFramedTwistEmbedding
public import M9StacksIntegration.ConicFramedGammaAction
public import M9StacksIntegration.ConicOrdinaryGraphGeometry
public import M9StacksIntegration.GraphFieldAction

/-! The original native graph quotient under the genuine ordinary framed
field inclusion. Its coefficients are the actual moving conic graph. -/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000
set_option maxRecDepth 10000

open Matrix MvPolynomial
open scoped Classical

namespace M9Native.ConicOrdinaryGraphEvaluation

open M9.GraphBundleDescent M9.MovingDeterminantFrames
open ConicPairMovingFrames ConicFrameHeadMatrices MovingConicCells
open ConicOrdinaryGraphGeometry ConicFramedTwistEmbedding

section Naturality

variable {K T : Type*} [Field K] [Field T] [Algebra ℂ K] [Algebra ℂ T]
  [CharZero K] [CharZero T]

omit [CharZero K] [CharZero T] in
theorem ordinaryIsomorphism_map (φ : K →ₐ[ℂ] T) (F H : GL3 K)
    (hF : IsUnit (headMatrix K F).det) (hH : IsUnit (headMatrix K H).det) (Z : GL4 K) :
    Matrix.GeneralLinearGroup.map φ.toRingHom (ordinaryIsomorphism K F H hF hH Z) =
      ordinaryIsomorphism T (Matrix.GeneralLinearGroup.map φ.toRingHom F)
        (Matrix.GeneralLinearGroup.map φ.toRingHom H)
        (ConicMovingFrameBaseChange.mappedHeadCondition φ F hF)
        (ConicMovingFrameBaseChange.mappedHeadCondition φ H hH)
        (Matrix.GeneralLinearGroup.map φ.toRingHom Z) := by
  rw [ordinaryIsomorphism, map_mul, map_mul, map_inv,
    ConicMovingFrameBaseChange.headUnit_map, ConicMovingFrameBaseChange.headUnit_map]
  rfl

omit [CharZero K] [CharZero T] in
theorem ordinaryQuotient_map (φ : K →ₐ[ℂ] T) (F H : GL3 K)
    (hF : IsUnit (headMatrix K F).det) (hH : IsUnit (headMatrix K H).det) (Z : GL4 K) :
    (ordinaryQuotient K F H hF hH Z).map φ.toRingHom =
      ordinaryQuotient T (Matrix.GeneralLinearGroup.map φ.toRingHom F)
        (Matrix.GeneralLinearGroup.map φ.toRingHom H)
        (ConicMovingFrameBaseChange.mappedHeadCondition φ F hF)
        (ConicMovingFrameBaseChange.mappedHeadCondition φ H hH)
        (Matrix.GeneralLinearGroup.map φ.toRingHom Z) := by
  have hx := congrArg Units.val (ordinaryIsomorphism_map φ F H hF hH Z)
  change (ordinaryIsomorphism K F H hF hH Z).val.map φ.toRingHom = _ at hx
  rw [ordinaryQuotient, ReducedGraphGenericPoint.kernelMatrix_map,
    GraphGrassmannianChart.blockRows_map, Matrix.map_mul,
    ConicMovingFrameBaseChange.movingCellMatrix_map,
    ConicMovingFrameBaseChange.movingCellMatrix_map, hx]
  rfl

end Naturality

abbrev M := ConicFramedGraphField.M

def frame (s : Fin 2) : GL3 M :=
  Matrix.GeneralLinearGroup.map (algebraMap B M) (frameUnit s)

theorem headCondition (s : Fin 2) : IsUnit (headMatrix M (frame s)).det :=
  ConicMovingFrameBaseChange.mappedHeadCondition (IsScalarTower.toAlgHom ℂ B M)
    (frameUnit s) (ConicPairMovingFrames.headCondition s)

theorem headUnit_actual (s : Fin 2) :
    headUnit M (frame s) (headCondition s) =
      Matrix.GeneralLinearGroup.map (algebraMap B M) (movingHeadUnit s) := by
  calc
    _ = Matrix.GeneralLinearGroup.map (algebraMap B M)
        (headUnit B (frameUnit s) (ConicPairMovingFrames.headCondition s)) :=
      (ConicMovingFrameBaseChange.headUnit_map (IsScalarTower.toAlgHom ℂ B M)
        (frameUnit s) (ConicPairMovingFrames.headCondition s)).symm
    _ = _ := congrArg (Matrix.GeneralLinearGroup.map (algebraMap B M)) (actualHeadUnit s)

theorem cellMatrix_actual (s : Fin 2) :
    movingCellMatrix M (frame s) (headCondition s) = (planeMatrix s).map (algebraMap B M) := by
  calc
    _ = (movingCellMatrix B (frameUnit s) (ConicPairMovingFrames.headCondition s)).map
        (algebraMap B M) :=
      (ConicMovingFrameBaseChange.movingCellMatrix_map (IsScalarTower.toAlgHom ℂ B M)
        (frameUnit s) (ConicPairMovingFrames.headCondition s)).symm
    _ = _ := congrArg (fun A : BaseMatrix B => A.map (algebraMap B M)) (actualPlaneMatrix s)

theorem genericBase_coordinate (s : Fin 2) (i : Fin 2) (j : Fin 4) :
    ReducedGraphGenericPoint.genericBase ℂ s i j =
      algebraMap (ChartRing ℂ) FF (X (.inl (s,i,j))) := by
  exact chartLocalizationToField_polynomial ℂ (X (.inl (s,i,j)))

theorem genericIsomorphism_val :
    (ReducedGraphGenericPoint.genericIsomorphism ℂ).val = chartGenericFiber ℂ := by
  apply Matrix.ext
  intro i j
  exact chartLocalizationToField_polynomial ℂ (X (.inr (i,j)))

theorem evaluated_base (s : Fin 2) :
    GraphFieldEvaluation.base ℂ M ordinaryEmbedding s =
      movingCellMatrix M (frame s) (headCondition s) := by
  rw [cellMatrix_actual]
  apply Matrix.ext
  intro i j
  change ordinaryEmbedding (ReducedGraphGenericPoint.genericBase ℂ s i j) = _
  rw [genericBase_coordinate, ordinaryEmbedding_base, ConicPairBaseEmbedding.baseEmbedding_entry]
  rfl

theorem evaluated_isomorphism :
    GraphFieldEvaluation.isomorphism ℂ M ordinaryEmbedding =
      ordinaryIsomorphism M (frame 0) (frame 1) (headCondition 0) (headCondition 1)
        ConicFramedGammaAction.rawUnit := by
  apply Units.ext
  change (ReducedGraphGenericPoint.genericIsomorphism ℂ).val.map ordinaryEmbedding.toRingHom = _
  rw [genericIsomorphism_val, ordinaryEmbedding_matrix]
  change ordinaryMatrix =
    ((headUnit M (frame 1) (headCondition 1)) * ConicFramedGammaAction.rawUnit *
      (headUnit M (frame 0) (headCondition 0))⁻¹).val
  rw [headUnit_actual, headUnit_actual]
  have hi := congrArg Units.val
    ((Matrix.GeneralLinearGroup.map (algebraMap B M)).map_inv (movingHeadUnit 0))
  exact congrArg (fun A : Matrix (Fin 4) (Fin 4) M =>
    (movingHeadUnit 1).val.map (algebraMap B M) * ConicFramedGraphField.genericRawMatrix * A) hi

/-- Literal original native quotient matrix, without a supplied graph identification. -/
theorem quotientMatrix_actual :
    GraphFieldEvaluation.quotientMatrix ℂ M ordinaryEmbedding =
      ordinaryQuotient M (frame 0) (frame 1) (headCondition 0) (headCondition 1)
        ConicFramedGammaAction.rawUnit := by
  rw [GraphFieldEvaluation.quotientMatrix, evaluated_base, evaluated_base,
    evaluated_isomorphism]
  rfl

theorem translated_quotient (σ : M ≃ₐ[ℂ] M) :
    GraphFieldEvaluation.quotientMatrix ℂ M
      (GraphFieldAction.translatedEmbedding ℂ M ordinaryEmbedding σ) =
        (GraphFieldEvaluation.quotientMatrix ℂ M ordinaryEmbedding).map σ.toRingHom := by
  rw [GraphFieldEvaluation.quotientMatrix_map, GraphFieldEvaluation.quotientMatrix_map]
  apply Matrix.ext
  intro i j
  rfl

/-- Its actual kernel is the actual moving ordinary graph in the fixed native coordinates. -/
theorem quotientMatrix_kernel :
    LinearMap.ker (GraphFieldEvaluation.quotientMatrix ℂ M ordinaryEmbedding).mulVecLin =
      LinearMap.range (framedEmbedding M (frame 0) (frame 1) ConicFramedGammaAction.rawUnit) := by
  rw [quotientMatrix_actual]
  exact ordinaryQuotient_kernel M (frame 0) (frame 1) (headCondition 0) (headCondition 1) _

end M9Native.ConicOrdinaryGraphEvaluation
