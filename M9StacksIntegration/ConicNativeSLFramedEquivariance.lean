module

public import M9StacksIntegration.ConicOrdinaryGraphAction
public import M9StacksIntegration.ConicFramedTwistAction

/-! Literal equivariance of the actual native determinant-compensated graph
field under the original constant SL3, with no action identification premise. -/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000
set_option maxRecDepth 10000

open Matrix
open scoped Classical

namespace M9Native.ConicNativeSLFramedEquivariance

open M9.GraphBundleDescent M9.MovingDeterminantFrames
open ConicPairMovingFrames ConicOrdinaryGraphEvaluation ConicOrdinaryGraphAction
open ConicOrdinaryGraphTransform ConicFramedTwistEmbedding ConicFramedTwistAction

abbrev SL3 := ProjectivePairSLFixedField.SL3
abbrev M := ConicFramedGraphField.M

def normalization0 (g : SL3) : Mˣ :=
  Units.map (algebraMap B M).toMonoidHom (ConicPairFrameSLAction.normalizationUnit0 g)

def normalization1 (g : SL3) : Mˣ :=
  Units.map (algebraMap B M).toMonoidHom (ConicPairFrameSLAction.normalizationUnit1 g)

theorem constantSL_map (g : SL3) :
    Matrix.GeneralLinearGroup.map (algebraMap B M) (ConicPairFrameSLAction.constantSL g) =
      Matrix.SpecialLinearGroup.toGL (extendedSL g) := by
  apply Units.ext
  apply Matrix.ext
  intro i j
  change algebraMap B M (algebraMap ℂ B (g.val i j)) = algebraMap ℂ M (g.val i j)
  exact IsScalarTower.algebraMap_apply ℂ B M _

theorem constantTransposeSL_map (g : SL3) :
    Matrix.GeneralLinearGroup.map (algebraMap B M) (ConicPairFrameSLAction.constantTransposeSL g) =
      (Matrix.SpecialLinearGroup.toGL
        (M9.PrimitiveRepresentation.inverseTranspose M (extendedSL g)))⁻¹ := by
  have hi : (Matrix.SpecialLinearGroup.toGL
      (M9.PrimitiveRepresentation.inverseTranspose M (extendedSL g)))⁻¹ =
      Matrix.SpecialLinearGroup.toGL (extendedSL g).transpose := by
    rw [← map_inv, M9.PrimitiveRepresentation.inverseTranspose_inv]
  rw [hi]
  apply Units.ext
  apply Matrix.ext
  intro i j
  change algebraMap B M (algebraMap ℂ B (g.val j i)) = algebraMap ℂ M (g.val j i)
  exact IsScalarTower.algebraMap_apply ℂ B M _

theorem ordinarySL_frame_map (g : SL3) (s : Fin 2) :
    Matrix.GeneralLinearGroup.map (ordinarySL g).toRingHom (frame s) =
      Matrix.GeneralLinearGroup.map (algebraMap B M)
        (Matrix.GeneralLinearGroup.map (ProjectivePairSLFixedField.slActionHom g).toRingHom
          (frameUnit s)) := by
  apply Units.ext
  apply Matrix.ext
  intro i j
  exact ordinarySL_constant g ((frameUnit s).val i j)

theorem ordinarySL_firstFrame (g : SL3) :
    Matrix.GeneralLinearGroup.map (ordinarySL g).toRingHom (frame 0) =
      firstTransform M (extendedSL g) (normalization0 g) (frame 0) := by
  rw [ordinarySL_frame_map, ConicPairFrameSLAction.firstFrame_image,
    map_mul, map_mul, map_inv, Matrix.GeneralLinearGroup.map_scalar, constantSL_map]
  change (Matrix.GeneralLinearGroup.scalar (Fin 3) (normalization0 g) *
    (Matrix.SpecialLinearGroup.toGL (extendedSL g))⁻¹) * frame 0 = _
  exact mul_assoc _ _ _

theorem ordinarySL_secondFrame (g : SL3) :
    Matrix.GeneralLinearGroup.map (ordinarySL g).toRingHom (frame 1) =
      secondTransform M (extendedSL g) (normalization1 g) (frame 1) := by
  rw [ordinarySL_frame_map, ConicPairFrameSLAction.secondFrame_image,
    map_mul, map_mul, Matrix.GeneralLinearGroup.map_scalar, constantTransposeSL_map]
  change (Matrix.GeneralLinearGroup.scalar (Fin 3) (normalization1 g) *
    (Matrix.SpecialLinearGroup.toGL
      (M9.PrimitiveRepresentation.inverseTranspose M (extendedSL g)))⁻¹) * frame 1 = _
  exact mul_assoc _ _ _

theorem normalizationRatio_map (g : SL3) :
    Units.map (algebraMap B M).toMonoidHom (normalizationRatio g) =
      normalization0 g ^ 2 / normalization1 g ^ 2 := by
  rw [normalizationRatio, map_div, map_pow, map_pow]
  rfl

theorem ordinarySL_rawUnit (g : SL3) :
    Matrix.GeneralLinearGroup.map (ordinarySL g).toRingHom ConicFramedGammaAction.rawUnit =
      rawTransform M (normalization0 g) (normalization1 g) ConicFramedGammaAction.rawUnit := by
  apply Units.ext
  change ConicFramedGraphField.genericRawMatrix.map (ordinarySL g).toRingHom =
    Matrix.scalar (Fin 4) (normalization0 g ^ 2 / normalization1 g ^ 2).val *
      ConicFramedGraphField.genericRawMatrix
  rw [ordinarySL_matrix, Matrix.scalar_apply, ← Matrix.smul_eq_diagonal_mul]
  have hv := congrArg Units.val (normalizationRatio_map g)
  change algebraMap B M (normalizationRatio g).val =
    (normalization0 g ^ 2 / normalization1 g ^ 2).val at hv
  rw [hv]

/-- Equivariance of the actual ordinary native graph pullback, with all
normalization and raw matrix formulas discharged. -/
theorem ordinarySL_equivariance (g : SL3) (f : FF) :
    ordinaryEmbedding (ordinaryFieldRepresentation (SemidirectProduct.inl g) f) =
      ordinarySL g (ordinaryEmbedding f) := by
  have h := connected_field_of_formulas g (ordinarySL g) (normalization0 g) (normalization1 g)
    (ordinarySL_firstFrame g) (ordinarySL_secondFrame g) (ordinarySL_rawUnit g)
    ((GraphGrassmannianChart.graphFunctionFieldEquiv ℂ).symm f)
  simpa only [ordinaryFieldRepresentation_apply, AlgEquiv.apply_symm_apply] using h

/-- Actual determinant-compensated native graph equivariance under SL3. -/
theorem embedding_connected (g : SL3) (f : FF) :
    ConicFramedGraphField.embedding
      (ConicCompatibleTwistedAction.twistedFieldRepresentation (SemidirectProduct.inl g) f) =
      coefficientSL g (ConicFramedGraphField.embedding f) :=
  twisted_equivariance_of_ordinary (SemidirectProduct.inl g) (ordinarySL g) (coefficientSL g)
    (ordinarySL_equivariance g) (ordinarySL_J g) f

/-- The coefficient action is the exact original infinite-SL3 action used
by the proved coefficient fixed-field quotient. -/
theorem embedding_connected_actual (g : SL3) (f : FF) :
    ConicFramedGraphField.embedding
      (ConicCompatibleTwistedAction.twistedFieldRepresentation (SemidirectProduct.inl g) f) =
      ConicFramedSLQuotient.coefficientTranslate g (ConicFramedGraphField.embedding f) := by
  rw [embedding_connected]
  exact RingHom.congr_fun (coefficientSL_eq_actual g) _

end M9Native.ConicNativeSLFramedEquivariance
