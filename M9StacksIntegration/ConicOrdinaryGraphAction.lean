module

public import M9StacksIntegration.ConicOrdinaryGraphEvaluation
public import M9StacksIntegration.ConicOrdinaryGraphTransform
public import M9StacksIntegration.ConicCompatibleTwistedAction

/-! Actual native ordinary graph action from concrete moving-frame
coefficient formulas. The generic criterion is derived through the original
native quotient classifier and its literal kernels. -/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000
set_option maxRecDepth 10000

open Matrix
open scoped Classical

namespace M9Native.ConicOrdinaryGraphAction

open M9.GraphBundleDescent M9.MovingDeterminantFrames
open ConicFrameHeadMatrices ConicOrdinaryGraphGeometry ConicOrdinaryGraphTransform
open ConicOrdinaryGraphEvaluation ConicFramedTwistEmbedding ConicCompatibleGraphCoordinates

abbrev SL3 := Matrix.SpecialLinearGroup (Fin 3) ℂ
abbrev M := ConicFramedGraphField.M

def extendedSL (g : SL3) : Matrix.SpecialLinearGroup (Fin 3) M :=
  Matrix.SpecialLinearGroup.map (algebraMap ℂ M) g

theorem connected_kernel_of_formulas (g : SL3) (σ : M ≃ₐ[ℂ] M) (a b : Mˣ)
    (hF : Matrix.GeneralLinearGroup.map σ.toRingHom (frame 0) =
      firstTransform M (extendedSL g) a (frame 0))
    (hH : Matrix.GeneralLinearGroup.map σ.toRingHom (frame 1) =
      secondTransform M (extendedSL g) b (frame 1))
    (hZ : Matrix.GeneralLinearGroup.map σ.toRingHom ConicFramedGammaAction.rawUnit =
      rawTransform M a b ConicFramedGammaAction.rawUnit) :
    LinearMap.ker (GraphFieldAction.actionMatrix ℂ M ordinaryEmbedding
      (matrixRepresentation ℂ (SemidirectProduct.inl g))).mulVecLin =
    LinearMap.ker (GraphFieldEvaluation.quotientMatrix ℂ M
      (GraphFieldAction.translatedEmbedding ℂ M ordinaryEmbedding σ)).mulVecLin := by
  have ht : LinearMap.ker (GraphFieldEvaluation.quotientMatrix ℂ M
      (GraphFieldAction.translatedEmbedding ℂ M ordinaryEmbedding σ)).mulVecLin =
      LinearMap.range (framedEmbedding M (firstTransform M (extendedSL g) a (frame 0))
        (secondTransform M (extendedSL g) b (frame 1))
        (rawTransform M a b ConicFramedGammaAction.rawUnit)) := by
    rw [translated_quotient, quotientMatrix_actual]
    change LinearMap.ker ((ordinaryQuotient M (frame 0) (frame 1)
      (headCondition 0) (headCondition 1) ConicFramedGammaAction.rawUnit).map
        σ.toAlgHom.toRingHom).mulVecLin = _
    rw [ordinaryQuotient_map σ.toAlgHom (frame 0) (frame 1)
        (headCondition 0) (headCondition 1) ConicFramedGammaAction.rawUnit,
      ordinaryQuotient_kernel]
    change LinearMap.range (framedEmbedding M
      (Matrix.GeneralLinearGroup.map σ.toRingHom (frame 0))
      (Matrix.GeneralLinearGroup.map σ.toRingHom (frame 1))
      (Matrix.GeneralLinearGroup.map σ.toRingHom ConicFramedGammaAction.rawUnit)) = _
    rw [hF, hH, hZ]
  rw [GraphFieldAction.actionMatrix, quotientMatrix_actual,
    show GraphFieldAction.constantUnit ℂ M (matrixRepresentation ℂ (SemidirectProduct.inl g)) =
      matrixRepresentation M (SemidirectProduct.inl (extendedSL g)) from
        ConicConstantActionMatrices.matrixRepresentation_connected_map M g, ht]
  apply kernel_mul_of_covariance M _ _
    (framedEmbedding M (frame 0) (frame 1) ConicFramedGammaAction.rawUnit)
    (framedEmbedding M (firstTransform M (extendedSL g) a (frame 0))
      (secondTransform M (extendedSL g) b (frame 1))
      (rawTransform M a b ConicFramedGammaAction.rawUnit))
    (Matrix.GeneralLinearGroup.scalar (Fin 4) (a^2))
  · exact ordinaryQuotient_kernel M _ _ _ _ _
  · intro x
    rw [scalarUnit_mulVec]
    exact framedEmbedding_connected M (extendedSL g) a b _ _ _ x

theorem connected_field_of_formulas (g : SL3) (σ : M ≃ₐ[ℂ] M) (a b : Mˣ)
    (hF : Matrix.GeneralLinearGroup.map σ.toRingHom (frame 0) =
      firstTransform M (extendedSL g) a (frame 0))
    (hH : Matrix.GeneralLinearGroup.map σ.toRingHom (frame 1) =
      secondTransform M (extendedSL g) b (frame 1))
    (hZ : Matrix.GeneralLinearGroup.map σ.toRingHom ConicFramedGammaAction.rawUnit =
      rawTransform M a b ConicFramedGammaAction.rawUnit)
    (z : (GrassmannianCharts.space ℂ 4 12).functionField) :
    ordinaryEmbedding (GraphGrassmannianChart.graphFunctionFieldEquiv ℂ
      (nativeFieldRepresentation ℂ (SemidirectProduct.inl g) z)) =
      σ (ordinaryEmbedding (GraphGrassmannianChart.graphFunctionFieldEquiv ℂ z)) :=
  GraphFieldAction.field_equivariance_of_kernel_eq ℂ M ordinaryEmbedding _ σ
    (connected_kernel_of_formulas g σ a b hF hH hZ) z

theorem odd_kernel_of_formulas (σ : M ≃ₐ[ℂ] M)
    (hF : Matrix.GeneralLinearGroup.map σ.toRingHom (frame 0) = frame 1)
    (hH : Matrix.GeneralLinearGroup.map σ.toRingHom (frame 1) = frame 0)
    (hZ : Matrix.GeneralLinearGroup.map σ.toRingHom ConicFramedGammaAction.rawUnit =
      ConicFramedGammaAction.rawUnit⁻¹) :
    LinearMap.ker (GraphFieldAction.actionMatrix ℂ M ordinaryEmbedding
      (matrixRepresentation ℂ (SemidirectProduct.inr M9.CentralSignQuotient.epsilon))).mulVecLin =
    LinearMap.ker (GraphFieldEvaluation.quotientMatrix ℂ M
      (GraphFieldAction.translatedEmbedding ℂ M ordinaryEmbedding σ)).mulVecLin := by
  have ht : LinearMap.ker (GraphFieldEvaluation.quotientMatrix ℂ M
      (GraphFieldAction.translatedEmbedding ℂ M ordinaryEmbedding σ)).mulVecLin =
      LinearMap.range (framedEmbedding M (frame 1) (frame 0) ConicFramedGammaAction.rawUnit⁻¹) := by
    rw [translated_quotient, quotientMatrix_actual]
    change LinearMap.ker ((ordinaryQuotient M (frame 0) (frame 1)
      (headCondition 0) (headCondition 1) ConicFramedGammaAction.rawUnit).map
        σ.toAlgHom.toRingHom).mulVecLin = _
    rw [ordinaryQuotient_map σ.toAlgHom (frame 0) (frame 1)
        (headCondition 0) (headCondition 1) ConicFramedGammaAction.rawUnit,
      ordinaryQuotient_kernel]
    change LinearMap.range (framedEmbedding M
      (Matrix.GeneralLinearGroup.map σ.toRingHom (frame 0))
      (Matrix.GeneralLinearGroup.map σ.toRingHom (frame 1))
      (Matrix.GeneralLinearGroup.map σ.toRingHom ConicFramedGammaAction.rawUnit)) = _
    rw [hF, hH, hZ]
  rw [GraphFieldAction.actionMatrix, quotientMatrix_actual,
    show GraphFieldAction.constantUnit ℂ M
        (matrixRepresentation ℂ (SemidirectProduct.inr M9.CentralSignQuotient.epsilon)) =
      matrixRepresentation M (SemidirectProduct.inr M9.CentralSignQuotient.epsilon) from
        ConicConstantActionMatrices.matrixRepresentation_odd_map M, ht]
  exact kernel_mul_of_covariance M _ _
    (framedEmbedding M (frame 0) (frame 1) ConicFramedGammaAction.rawUnit)
    (framedEmbedding M (frame 1) (frame 0) ConicFramedGammaAction.rawUnit⁻¹)
    ConicFramedGammaAction.rawUnit⁻¹ (ordinaryQuotient_kernel M _ _ _ _ _)
    (framedEmbedding_odd M _ _ _)

theorem odd_field_of_formulas (σ : M ≃ₐ[ℂ] M)
    (hF : Matrix.GeneralLinearGroup.map σ.toRingHom (frame 0) = frame 1)
    (hH : Matrix.GeneralLinearGroup.map σ.toRingHom (frame 1) = frame 0)
    (hZ : Matrix.GeneralLinearGroup.map σ.toRingHom ConicFramedGammaAction.rawUnit =
      ConicFramedGammaAction.rawUnit⁻¹)
    (z : (GrassmannianCharts.space ℂ 4 12).functionField) :
    ordinaryEmbedding (GraphGrassmannianChart.graphFunctionFieldEquiv ℂ
      (nativeFieldRepresentation ℂ (SemidirectProduct.inr M9.CentralSignQuotient.epsilon) z)) =
      σ (ordinaryEmbedding (GraphGrassmannianChart.graphFunctionFieldEquiv ℂ z)) :=
  GraphFieldAction.field_equivariance_of_kernel_eq ℂ M ordinaryEmbedding _ σ
    (odd_kernel_of_formulas σ hF hH hZ) z

/-- The original native field action in the proved original graph coordinates. -/
def ordinaryFieldRepresentation : ConicCompatibleTwistedAction.H →* (FF ≃ₐ[ℂ] FF) :=
  (AlgEquiv.autCongr (GraphGrassmannianChart.graphFunctionFieldEquiv ℂ)).toMonoidHom.comp
    (nativeFieldRepresentation ℂ)

theorem ordinaryFieldRepresentation_apply (w : ConicCompatibleTwistedAction.H) (f : FF) :
    ordinaryFieldRepresentation w f = GraphGrassmannianChart.graphFunctionFieldEquiv ℂ
      (nativeFieldRepresentation ℂ w ((GraphGrassmannianChart.graphFunctionFieldEquiv ℂ).symm f)) :=
  rfl

/-- Actual native center restriction, with the original determinant quotient inclusion. -/
theorem centralEmbedding_equivariance (w : ConicCompatibleTwistedAction.H) (f : FF) :
    centralEmbedding (ConicCompatibleTwistedAction.twistedFieldRepresentation w f) =
      ordinaryFieldRepresentation w (centralEmbedding f) := by
  have hi : (GraphGrassmannianChart.graphFunctionFieldEquiv ℂ).symm (centralEmbedding f) =
      (ReducedGraphCenter.nativeDeterminantQuotient f).val := by
    apply (GraphGrassmannianChart.graphFunctionFieldEquiv ℂ).injective
    rw [AlgEquiv.apply_symm_apply, ReducedGraphCenter.nativeDeterminantQuotient_coordinates]
    rfl
  calc
    _ = GraphGrassmannianChart.graphFunctionFieldEquiv ℂ
        (ReducedGraphCenter.nativeDeterminantQuotient
          (ConicCompatibleTwistedAction.twistedFieldRepresentation w f)).val :=
      (ReducedGraphCenter.nativeDeterminantQuotient_coordinates _).symm
    _ = GraphGrassmannianChart.graphFunctionFieldEquiv ℂ
        (nativeFieldRepresentation ℂ w (ReducedGraphCenter.nativeDeterminantQuotient f).val) :=
      congrArg (GraphGrassmannianChart.graphFunctionFieldEquiv ℂ)
        (ConicCompatibleTwistedAction.twistedFieldRepresentation_quotient w f)
    _ = _ := by rw [ordinaryFieldRepresentation_apply, hi]

/-- The actual native center quotient and the proved literal J diagram
transfer ordinary equivariance to the determinant-compensated graph. -/
theorem twisted_equivariance_of_ordinary (w : ConicCompatibleTwistedAction.H)
    (σordinary σtwisted : M ≃ₐ[ℂ] M)
    (hOrdinary : ∀ f : FF, ordinaryEmbedding (ordinaryFieldRepresentation w f) =
      σordinary (ordinaryEmbedding f))
    (hJ : ∀ z : M, σordinary (J z) = J (σtwisted z)) (f : FF) :
    ConicFramedGraphField.embedding (ConicCompatibleTwistedAction.twistedFieldRepresentation w f) =
      σtwisted (ConicFramedGraphField.embedding f) := by
  apply J_injective
  calc
    _ = ordinaryEmbedding (centralEmbedding
        (ConicCompatibleTwistedAction.twistedFieldRepresentation w f)) := (commuting _).symm
    _ = ordinaryEmbedding (ordinaryFieldRepresentation w (centralEmbedding f)) :=
      congrArg ordinaryEmbedding (centralEmbedding_equivariance w f)
    _ = σordinary (ordinaryEmbedding (centralEmbedding f)) := hOrdinary _
    _ = σordinary (J (ConicFramedGraphField.embedding f)) := congrArg σordinary (commuting f)
    _ = _ := hJ _

end M9Native.ConicOrdinaryGraphAction
