module

public import M9StacksIntegration.ConicFramedGraphField
public import M9.DeterminantTwistBaseChange

/-! The actual determinant quotient in the ordinary and compensated
moving conic frames. The raw substitution is constructed from the proved
sixteen-coordinate determinant quotient and an actual scalar automorphism. -/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 10000

open MvPolynomial Matrix
open scoped Classical

namespace M9Native.ConicFramedTwistEmbedding

open M9.GraphBundleDescent ConicPairMovingFrames

abbrev M := ConicFramedGraphField.M
abbrev FF := ChartFunctionField ℂ

/-- The actual determinant character of the original moving GL3 frame. -/
def beta (s : Fin 2) : Bˣ := (Matrix.GeneralLinearGroup.det (frameUnit s)) ^ 2

/-- The exact compensating scalar, as a genuine nonzero coefficient unit. -/
def twistScalar : Bˣ := beta 0 / beta 1

theorem beta_val (s : Fin 2) : (beta s).val = (frameUnit s).val.det ^ 2 := rfl

theorem twistScalar_val : twistScalar.val =
    (frameUnit 0).val.det ^ 2 / (frameUnit 1).val.det ^ 2 := by
  simp only [twistScalar, Units.val_div_eq_div_val, beta_val]

theorem compensatedFrame_eq (s : Fin 2) :
    compensatedFrame s = Matrix.GeneralLinearGroup.scalar (Fin 4) (beta s) *
      adjustedFrameHom B (movingHeadUnit s) := by
  rw [← actualCompensatedFrame, MovingConicTensorCoordinates.compensatedHead, actualHeadUnit]
  rfl

/-- Actual ordinary moving-head substitution, before determinant adjustment. -/
def ordinaryGauge : M ≃ₐ[ℂ] M :=
  (RationalMatrixGauge.fieldEquiv B (Fin 4) (movingHeadUnit 1) (movingHeadUnit 0)⁻¹).restrictScalars ℂ

def ordinaryEmbedding : FF →ₐ[ℂ] M :=
  ordinaryGauge.toAlgHom.comp ConicGraphCoefficientDescent.chartEmbedding

/-- The actual chart μ3-quotient inclusion, with no quotient premise. -/
def centralEmbedding : FF →ₐ[ℂ] FF :=
  chartCentralFixedField.val.comp chartCentralQuotientEquiv.toAlgHom

/-- Inclusion of the proved actual sixteen-coordinate determinant quotient. -/
def twistEmbedding : M →ₐ[B] M :=
  (M9.DeterminantTwistBaseChange.scalarFixedField B).val.comp
    (M9.DeterminantTwistBaseChange.quotientCoordinateEquiv B).toAlgHom

/-- Actual nonzero scalar change of the independent raw coordinates. -/
def rawScale : M ≃ₐ[B] M :=
  M9.ProjectiveNoName.fractionScale FiberIndex twistScalar.val twistScalar.ne_zero

def JBase : M →ₐ[B] M := twistEmbedding.comp rawScale.toAlgHom

/-- The actual injective raw substitution `W ↦ c det(Z)⁻¹ Z`. -/
def J : M →ₐ[ℂ] M := JBase.restrictScalars ℂ

theorem J_injective : Function.Injective J := J.injective

theorem ordinaryGauge_constant (b : B) : ordinaryGauge (algebraMap B M b) = algebraMap B M b :=
  (RationalMatrixGauge.fieldEquiv B (Fin 4) (movingHeadUnit 1) (movingHeadUnit 0)⁻¹).commutes b

theorem twistEmbedding_variable (ij : FiberIndex) :
    twistEmbedding (ConicFramedGraphField.genericRawMatrix ij.1 ij.2) =
      M9.DeterminantTwist.twist ConicFramedGraphField.genericRawMatrix ij.1 ij.2 :=
  M9.DeterminantTwistBaseChange.quotientCoordinateEquiv_coordinate B ij

theorem J_constant (b : B) : J (algebraMap B M b) = algebraMap B M b :=
  JBase.commutes b

theorem J_variable (ij : FiberIndex) :
    J (ConicFramedGraphField.genericRawMatrix ij.1 ij.2) =
      algebraMap B M twistScalar.val *
        M9.DeterminantTwist.twist ConicFramedGraphField.genericRawMatrix ij.1 ij.2 := by
  change twistEmbedding (rawScale
    (algebraMap (MvPolynomial FiberIndex B) M (X ij))) = _
  rw [show rawScale (algebraMap (MvPolynomial FiberIndex B) M (X ij)) =
      algebraMap B M twistScalar.val * algebraMap (MvPolynomial FiberIndex B) M (X ij)
    from M9.ProjectiveNoName.fractionScale_variable FiberIndex twistScalar.val twistScalar.ne_zero ij]
  rw [map_mul, twistEmbedding.commutes]
  exact congrArg (fun z : M => algebraMap B M twistScalar.val * z) (twistEmbedding_variable ij)

theorem J_matrix :
    ConicFramedGraphField.genericRawMatrix.map J.toRingHom =
      algebraMap B M twistScalar.val •
        M9.DeterminantTwist.twist ConicFramedGraphField.genericRawMatrix := by
  ext i j
  exact J_variable (i,j)

/-- The literal raw-variable formula with the actual original frame
determinants and actual generic matrix determinant written explicitly. -/
theorem J_variable_explicit (ij : FiberIndex) :
    J (ConicFramedGraphField.genericRawMatrix ij.1 ij.2) =
      algebraMap B M ((frameUnit 0).val.det ^ 2 / (frameUnit 1).val.det ^ 2) *
        (ConicFramedGraphField.genericRawMatrix.det⁻¹ *
          ConicFramedGraphField.genericRawMatrix ij.1 ij.2) := by
  rw [J_variable, twistScalar_val]
  rfl

theorem centralEmbedding_base (b : BaseIndex) :
    centralEmbedding (algebraMap (ChartRing ℂ) FF (X (.inl b))) =
      algebraMap (ChartRing ℂ) FF (X (.inl b)) :=
  chartCentralQuotient_base_coordinate b

theorem centralEmbedding_fiber (ij : FiberIndex) :
    centralEmbedding (algebraMap (ChartRing ℂ) FF (X (.inr ij))) =
      M9.DeterminantTwist.twist (chartGenericFiber ℂ) ij.1 ij.2 :=
  chartCentralQuotient_fiber_coordinate ij

def ordinaryMatrix : Matrix (Fin 4) (Fin 4) M :=
  (movingHeadUnit 1).val.map (algebraMap B M) * ConicFramedGraphField.genericRawMatrix *
    (movingHeadUnit 0)⁻¹.val.map (algebraMap B M)

theorem ordinaryEmbedding_base (b : BaseIndex) :
    ordinaryEmbedding (algebraMap (ChartRing ℂ) FF (X (.inl b))) =
      algebraMap B M (ConicGraphBaseCoordinates.baseEmbedding
        (algebraMap (MvPolynomial BaseIndex ℂ) (BaseFunctionField ℂ) (X b))) := by
  change ordinaryGauge (ConicGraphCoefficientDescent.chartEmbedding _) = _
  rw [ConicGraphCoefficientDescent.chartEmbedding_base, ordinaryGauge_constant]

theorem ordinaryEmbedding_fiber (ij : FiberIndex) :
    ordinaryEmbedding (algebraMap (ChartRing ℂ) FF (X (.inr ij))) =
      ordinaryMatrix ij.1 ij.2 := by
  change ordinaryGauge (ConicGraphCoefficientDescent.chartEmbedding _) = _
  rw [ConicGraphCoefficientDescent.chartEmbedding_fiber]
  exact RationalMatrixGauge.fieldEquiv_variable B (Fin 4) (movingHeadUnit 1)
    (movingHeadUnit 0)⁻¹ ij.1 ij.2

theorem ordinaryEmbedding_matrix :
    (chartGenericFiber ℂ).map ordinaryEmbedding.toRingHom = ordinaryMatrix := by
  ext i j
  exact ordinaryEmbedding_fiber (i,j)

theorem ordinaryEmbedding_central_fiber (ij : FiberIndex) :
    ordinaryEmbedding (centralEmbedding (algebraMap (ChartRing ℂ) FF (X (.inr ij)))) =
      M9.DeterminantTwist.twist ordinaryMatrix ij.1 ij.2 := by
  rw [centralEmbedding_fiber]
  have hd := ordinaryEmbedding.map_det (chartGenericFiber ℂ)
  change ordinaryEmbedding (chartGenericFiber ℂ).det =
    ((chartGenericFiber ℂ).map ordinaryEmbedding.toRingHom).det at hd
  rw [ordinaryEmbedding_matrix] at hd
  change ordinaryEmbedding ((chartGenericFiber ℂ).det⁻¹ * chartGenericFiber ℂ ij.1 ij.2) =
    ordinaryMatrix.det⁻¹ * ordinaryMatrix ij.1 ij.2
  rw [map_mul, map_inv₀, hd]
  exact congrArg (fun z : M => ordinaryMatrix.det⁻¹ * z) (ordinaryEmbedding_fiber ij)

/-- The actual compensated frame factors cancel precisely with the
determinant quotient scalar. This identity is valid for every matrix Z. -/
theorem compensated_twist_matrix {K : Type*} [Field K]
    (b0 b1 : Kˣ) (R0 R1 : GL4 K) (Z : M9.DeterminantTwist.Mat4 K) :
    (Matrix.GeneralLinearGroup.scalar (Fin 4) b1 * adjustedFrameHom K R1).val *
        ((b0 / b1).val • M9.DeterminantTwist.twist Z) *
        (Matrix.GeneralLinearGroup.scalar (Fin 4) b0 * adjustedFrameHom K R0)⁻¹.val =
      M9.DeterminantTwist.twist (R1.val * Z * R0⁻¹.val) := by
  have hL : (Matrix.GeneralLinearGroup.scalar (Fin 4) b1 * adjustedFrameHom K R1).val =
      b1.val • (adjustedFrameHom K R1).val := by
    change Matrix.scalar (Fin 4) b1.val * (adjustedFrameHom K R1).val = _
    rw [Matrix.scalar_apply, ← Matrix.smul_eq_diagonal_mul]
  have hR : (Matrix.GeneralLinearGroup.scalar (Fin 4) b0 * adjustedFrameHom K R0)⁻¹.val =
      (b0⁻¹).val • (adjustedFrameHom K R0⁻¹).val := by
    rw [show (Matrix.GeneralLinearGroup.scalar (Fin 4) b0 * adjustedFrameHom K R0)⁻¹ =
      adjustedFrameHom K R0⁻¹ * Matrix.GeneralLinearGroup.scalar (Fin 4) b0⁻¹ by
        simp only [_root_.mul_inv_rev, map_inv]]
    change (adjustedFrameHom K R0⁻¹).val * Matrix.scalar (Fin 4) (b0⁻¹).val = _
    rw [Matrix.scalar_apply, ← Matrix.smul_eq_mul_diagonal]
  have hc : b1.val * (b0 / b1).val * (b0⁻¹).val = (1 : K) := by
    have hu : b1 * (b0 / b1) * b0⁻¹ = 1 := by
      simp [div_eq_mul_inv, mul_left_comm]
    exact congrArg Units.val hu
  calc
    _ = (b1.val * (b0 / b1).val * (b0⁻¹).val) •
        (M9.DeterminantTwist.twist R1.val * M9.DeterminantTwist.twist Z *
          M9.DeterminantTwist.twist R0⁻¹.val) := by
      rw [hL, hR, adjustedFrame_field_value, adjustedFrame_field_value]
      simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul, Matrix.mul_assoc]
      congr 1
      ring
    _ = _ := by
      rw [hc, one_smul, ← M9.DeterminantTwist.twist_mul, ← M9.DeterminantTwist.twist_mul]

private def coefficientUnit (g : GL4 B) : GL4 M :=
  Matrix.GeneralLinearGroup.map (algebraMap B M) g

private def coefficientBeta (s : Fin 2) : Mˣ :=
  Units.map (algebraMap B M).toMonoidHom (beta s)

private theorem coefficientUnit_compensated (s : Fin 2) :
    coefficientUnit (compensatedFrame s) =
      Matrix.GeneralLinearGroup.scalar (Fin 4) (coefficientBeta s) *
        adjustedFrameHom M (coefficientUnit (movingHeadUnit s)) := by
  change Matrix.GeneralLinearGroup.map (algebraMap B M) (compensatedFrame s) = _
  rw [compensatedFrame_eq, map_mul, Matrix.GeneralLinearGroup.map_scalar,
    ConicPairMovingFrames.adjustedFrame_map]
  rfl

private theorem coefficientUnit_inv_val (g : GL4 B) :
    (coefficientUnit g)⁻¹.val = g⁻¹.val.map (algebraMap B M) := by
  change (Matrix.GeneralLinearGroup.map (algebraMap B M) g)⁻¹.val = _
  rw [← map_inv]
  rfl

private theorem coefficient_twistScalar :
    (coefficientBeta 0 / coefficientBeta 1).val = algebraMap B M twistScalar.val := by
  change (Units.map (algebraMap B M).toMonoidHom (beta 0) /
    Units.map (algebraMap B M).toMonoidHom (beta 1)).val = _
  rw [← map_div]
  rfl

/-- The exact identity for the actual original moving-frame matrices,
with their true beta factors and coefficient inclusions. -/
theorem compensation_identity :
    (compensatedFrame 1).val.map (algebraMap B M) *
        (algebraMap B M twistScalar.val •
          M9.DeterminantTwist.twist ConicFramedGraphField.genericRawMatrix) *
        (compensatedFrame 0)⁻¹.val.map (algebraMap B M) =
      M9.DeterminantTwist.twist ordinaryMatrix := by
  have h := compensated_twist_matrix (coefficientBeta 0) (coefficientBeta 1)
    (coefficientUnit (movingHeadUnit 0)) (coefficientUnit (movingHeadUnit 1))
    ConicFramedGraphField.genericRawMatrix
  rw [← coefficientUnit_compensated 1, ← coefficientUnit_compensated 0,
    coefficient_twistScalar] at h
  simp only [coefficientUnit_inv_val] at h
  exact h

private theorem J_coefficientMatrix (g : GL4 B) :
    (g.val.map (algebraMap B M)).map J.toRingHom = g.val.map (algebraMap B M) := by
  ext i j
  exact J_constant (g.val i j)

/-- Applying the genuine raw substitution to the compensated moving
matrix gives the determinant twist of the ordinary moving matrix. -/
theorem J_compensatedMatrix :
    ((compensatedFrame 1).val.map (algebraMap B M) *
        ConicFramedGraphField.genericRawMatrix *
        (compensatedFrame 0)⁻¹.val.map (algebraMap B M)).map J.toRingHom =
      M9.DeterminantTwist.twist ordinaryMatrix := by
  rw [Matrix.map_mul, Matrix.map_mul, J_coefficientMatrix, J_coefficientMatrix, J_matrix]
  exact compensation_identity

theorem J_embedding_fiber (ij : FiberIndex) :
    J (ConicFramedGraphField.embedding (algebraMap (ChartRing ℂ) FF (X (.inr ij)))) =
      M9.DeterminantTwist.twist ordinaryMatrix ij.1 ij.2 := by
  rw [ConicFramedGraphField.embedding_fiber]
  exact congrFun (congrFun J_compensatedMatrix ij.1) ij.2

theorem commuting_base (b : BaseIndex) :
    ordinaryEmbedding (centralEmbedding (algebraMap (ChartRing ℂ) FF (X (.inl b)))) =
      J (ConicFramedGraphField.embedding (algebraMap (ChartRing ℂ) FF (X (.inl b)))) := by
  rw [centralEmbedding_base, ordinaryEmbedding_base]
  change _ = J (ConicFramedGraphField.movingGauge
    (ConicGraphCoefficientDescent.chartEmbedding _))
  rw [ConicGraphCoefficientDescent.chartEmbedding_base,
    ConicFramedGraphField.movingGauge_constant, J_constant]

/-- The actual ordinary embedding after the actual determinant quotient
equals the actual raw substitution after the original compensated embedding. -/
theorem commuting_hom : ordinaryEmbedding.comp centralEmbedding =
    J.comp ConicFramedGraphField.embedding := by
  have h : (ordinaryEmbedding.comp centralEmbedding).toRingHom =
      (J.comp ConicFramedGraphField.embedding).toRingHom := by
    apply M9.ProjectiveNoName.rationalRingHom_ext ℂ ParameterIndex
    · intro c
      exact ((ordinaryEmbedding.comp centralEmbedding).commutes c).trans
        ((J.comp ConicFramedGraphField.embedding).commutes c).symm
    · intro ij
      cases ij with
      | inl b => exact commuting_base b
      | inr ij => exact (ordinaryEmbedding_central_fiber ij).trans (J_embedding_fiber ij).symm
  exact AlgHom.ext (fun f => RingHom.congr_fun h f)

/-- The commuting identity holds for every actual chart rational function. -/
theorem commuting (f : FF) : ordinaryEmbedding (centralEmbedding f) =
    J (ConicFramedGraphField.embedding f) :=
  congrArg (fun h : FF →ₐ[ℂ] M => h f) commuting_hom

end M9Native.ConicFramedTwistEmbedding
