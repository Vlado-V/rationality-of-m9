module

public import M9StacksIntegration.ConicFramedTwistEmbedding
public import M9StacksIntegration.ConicPairFrameSLAction
public import M9StacksIntegration.ConicFramedSLQuotient
public import M9StacksIntegration.FrameHomRawOddCoordinates
public import M9StacksIntegration.ConicFramedGammaAction

/-! Actual coefficient and raw-matrix automorphisms compatible with the
determinant-twist embedding. The SL3 scalar comes from the original two
frame normalizations; the odd map uses the original coefficient exchange. -/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 10000

open MvPolynomial Matrix
open scoped Classical

namespace M9Native.ConicFramedTwistAction

open M9.GraphBundleDescent ConicPairMovingFrames
open ConicFramedTwistEmbedding (J twistScalar)
open ProjectivePairSLFixedField (SL3 slActionHom)

abbrev M := ConicFramedTwistEmbedding.M
abbrev Z := ConicFramedGraphField.genericRawMatrix

/-- The coefficient extension fixes the sixteen original raw coordinates. -/
def coefficientEquiv (φ : B ≃ₐ[ℂ] B) : M ≃ₐ[ℂ] M :=
  M9.ProjectiveNoName.rationalCoefficientEquiv ℂ FiberIndex φ

/-- A genuine coefficient automorphism followed by raw scalar substitution. -/
def scaledCoefficient (φ : B ≃ₐ[ℂ] B) (r : Bˣ) : M ≃ₐ[ℂ] M :=
  (M9.ProjectiveNoName.fractionScale FiberIndex r.val r.ne_zero).restrictScalars ℂ *
    coefficientEquiv φ

theorem coefficientEquiv_constant (φ : B ≃ₐ[ℂ] B) (b : B) :
    coefficientEquiv φ (algebraMap B M b) = algebraMap B M (φ b) :=
  M9.ProjectiveNoName.rationalCoefficientEquiv_coefficient ℂ FiberIndex φ b

theorem coefficientEquiv_variable (φ : B ≃ₐ[ℂ] B) (ij : FiberIndex) :
    coefficientEquiv φ (Z ij.1 ij.2) = Z ij.1 ij.2 :=
  M9.ProjectiveNoName.rationalCoefficientEquiv_variable ℂ FiberIndex φ ij

theorem scaledCoefficient_constant (φ : B ≃ₐ[ℂ] B) (r : Bˣ) (b : B) :
    scaledCoefficient φ r (algebraMap B M b) = algebraMap B M (φ b) := by
  change (M9.ProjectiveNoName.fractionScale FiberIndex r.val r.ne_zero)
    (coefficientEquiv φ (algebraMap B M b)) = _
  rw [coefficientEquiv_constant, AlgEquiv.commutes]

theorem scaledCoefficient_variable (φ : B ≃ₐ[ℂ] B) (r : Bˣ) (ij : FiberIndex) :
    scaledCoefficient φ r (Z ij.1 ij.2) = algebraMap B M r.val * Z ij.1 ij.2 := by
  change (M9.ProjectiveNoName.fractionScale FiberIndex r.val r.ne_zero)
    (coefficientEquiv φ (Z ij.1 ij.2)) = _
  rw [coefficientEquiv_variable]
  exact M9.ProjectiveNoName.fractionScale_variable FiberIndex r.val r.ne_zero ij

theorem scaledCoefficient_matrix (φ : B ≃ₐ[ℂ] B) (r : Bˣ) :
    Z.map (scaledCoefficient φ r).toRingHom = algebraMap B M r.val • Z := by
  ext i j
  exact scaledCoefficient_variable φ r (i,j)

theorem genericRawMatrix_det_ne_zero : Z.det ≠ 0 :=
  M9.CayleyField.genericMatrix_det_ne_zero B

/-- The generator computation behind the actual SL3 specialization.
Only this intermediate lemma has an explicit scalar transformation hypothesis. -/
theorem scaledCoefficient_J_variable (φ : B ≃ₐ[ℂ] B) (r : Bˣ)
    (hc : φ twistScalar.val = r.val ^ 3 * twistScalar.val) (ij : FiberIndex) :
    scaledCoefficient φ r (J (Z ij.1 ij.2)) =
      J (coefficientEquiv φ (Z ij.1 ij.2)) := by
  have hd : scaledCoefficient φ r Z.det = (algebraMap B M r.val)^4 * Z.det := by
    rw [(scaledCoefficient φ r).map_det]
    change (Z.map (scaledCoefficient φ r).toRingHom).det = _
    rw [scaledCoefficient_matrix]
    exact M9.DeterminantTwist.det_smul_four Z _
  have hr : algebraMap B M r.val ≠ 0 := (map_ne_zero (algebraMap B M)).mpr r.ne_zero
  rw [coefficientEquiv_variable, ConicFramedTwistEmbedding.J_variable,
    map_mul, scaledCoefficient_constant, hc, map_mul, map_pow]
  change algebraMap B M r.val ^ 3 * algebraMap B M twistScalar.val *
    scaledCoefficient φ r (Z.det⁻¹ * Z ij.1 ij.2) =
      algebraMap B M twistScalar.val * (Z.det⁻¹ * Z ij.1 ij.2)
  rw [map_mul, map_inv₀, hd, scaledCoefficient_variable]
  field_simp [hr, genericRawMatrix_det_ne_zero]

theorem scaledCoefficient_J (φ : B ≃ₐ[ℂ] B) (r : Bˣ)
    (hc : φ twistScalar.val = r.val ^ 3 * twistScalar.val) (f : M) :
    scaledCoefficient φ r (J f) = J (coefficientEquiv φ f) := by
  have h : (scaledCoefficient φ r).toRingHom.comp J.toRingHom =
      J.toRingHom.comp (coefficientEquiv φ).toRingHom := by
    apply M9.ProjectiveNoName.rationalRingHom_ext B FiberIndex
    · intro b
      change scaledCoefficient φ r (J (algebraMap B M b)) =
        J (coefficientEquiv φ (algebraMap B M b))
      rw [ConicFramedTwistEmbedding.J_constant, coefficientEquiv_constant,
        ConicFramedTwistEmbedding.J_constant, scaledCoefficient_constant]
    · exact scaledCoefficient_J_variable φ r hc
  exact DFunLike.congr_fun h f

/-- The actual original SL3 coefficient automorphism, with its proved
complex-linearity retained explicitly. -/
def slCoefficientAlgEquiv (g : SL3) : B ≃ₐ[ℂ] B where
  __ := slActionHom g
  commutes' c := by
    change slActionHom g (algebraMap ℂ B c) = algebraMap ℂ B c
    apply Subtype.ext
    rw [ProjectivePairSLFixedField.slActionHom_apply,
      M9.ProjectiveFrameAction.projectiveActionHom_val]
    exact M9.FrameFieldElimination.pairAction_constant ℂ
      (Matrix.SpecialLinearGroup.toGL g) c

theorem slCoefficientAlgEquiv_apply (g : SL3) (b : B) :
    slCoefficientAlgEquiv g b = slActionHom g b := rfl

/-- The exact ratio of the two actual frame normalization squares. -/
def normalizationRatio (g : SL3) : Bˣ :=
  ConicPairFrameSLAction.normalizationUnit0 g ^ 2 /
    ConicPairFrameSLAction.normalizationUnit1 g ^ 2

theorem normalizationRatio_val (g : SL3) : (normalizationRatio g).val =
    (ConicPairFrameSLAction.normalizationUnit0 g : B)^2 /
      (ConicPairFrameSLAction.normalizationUnit1 g : B)^2 := by
  simp only [normalizationRatio, Units.val_div_eq_div_val, Units.val_pow_eq_pow_val]

def coefficientSL (g : SL3) : M ≃ₐ[ℂ] M := coefficientEquiv (slCoefficientAlgEquiv g)

def ordinarySL (g : SL3) : M ≃ₐ[ℂ] M :=
  scaledCoefficient (slCoefficientAlgEquiv g) (normalizationRatio g)

theorem coefficientSL_constant (g : SL3) (b : B) :
    coefficientSL g (algebraMap B M b) = algebraMap B M (slActionHom g b) :=
  coefficientEquiv_constant (slCoefficientAlgEquiv g) b

theorem coefficientSL_variable (g : SL3) (ij : FiberIndex) :
    coefficientSL g (Z ij.1 ij.2) = Z ij.1 ij.2 :=
  coefficientEquiv_variable (slCoefficientAlgEquiv g) ij

theorem coefficientSL_eq_actual (g : SL3) :
    (coefficientSL g).toRingHom = ConicFramedSLQuotient.coefficientTranslate g := by
  apply M9.ProjectiveNoName.rationalRingHom_ext B FiberIndex
  · intro b
    exact (coefficientSL_constant g b).trans
      (ConicFramedSLQuotient.coefficientTranslate_constant g b).symm
  · intro ij
    exact (coefficientSL_variable g ij).trans
      (ConicFramedSLQuotient.coefficientTranslate_variable g ij).symm

theorem ordinarySL_constant (g : SL3) (b : B) :
    ordinarySL g (algebraMap B M b) = algebraMap B M (slActionHom g b) :=
  scaledCoefficient_constant (slCoefficientAlgEquiv g) (normalizationRatio g) b

theorem ordinarySL_variable (g : SL3) (ij : FiberIndex) :
    ordinarySL g (Z ij.1 ij.2) = algebraMap B M (normalizationRatio g).val * Z ij.1 ij.2 :=
  scaledCoefficient_variable (slCoefficientAlgEquiv g) (normalizationRatio g) ij

theorem ordinarySL_matrix (g : SL3) :
    Z.map (ordinarySL g).toRingHom = algebraMap B M (normalizationRatio g).val • Z :=
  scaledCoefficient_matrix (slCoefficientAlgEquiv g) (normalizationRatio g)

/-- The scalar relation is derived from the actual two determinant laws. -/
theorem sl_twistScalar (g : SL3) :
    slActionHom g twistScalar.val = (normalizationRatio g).val ^ 3 * twistScalar.val := by
  rw [ConicFramedTwistEmbedding.twistScalar_val, map_div₀, map_pow, map_pow,
    ConicPairFrameSLAction.firstFrame_det_image,
    ConicPairFrameSLAction.secondFrame_det_image, normalizationRatio_val]
  simp only [mul_pow, div_pow]
  ring

/-- Intertwining for every rational function, with no scalar-compatibility premise. -/
theorem ordinarySL_J (g : SL3) (f : M) :
    ordinarySL g (J f) = J (coefficientSL g f) :=
  scaledCoefficient_J (slCoefficientAlgEquiv g) (normalizationRatio g) (sl_twistScalar g) f

theorem ordinarySL_rawUnit (g : SL3) :
    Matrix.GeneralLinearGroup.map (ordinarySL g).toRingHom ConicFramedGammaAction.rawUnit =
      Matrix.GeneralLinearGroup.scalar (Fin 4)
        (Units.map (algebraMap B M).toMonoidHom (normalizationRatio g)) *
          ConicFramedGammaAction.rawUnit := by
  apply Units.ext
  change Z.map (ordinarySL g).toRingHom =
    Matrix.diagonal (fun _ : Fin 4 => algebraMap B M (normalizationRatio g).val) * Z
  rw [ordinarySL_matrix]
  ext i j
  exact (Matrix.diagonal_mul (fun _ : Fin 4 => algebraMap B M (normalizationRatio g).val)
    Z i j).symm

theorem swap_firstEmbedding (b : GenericConicHead.L) :
    PairProjectiveEquivariance.projectivePairSwap (firstEmbedding b) = secondEmbedding b := by
  change PairProjectiveEquivariance.projectivePairSwap
    (PairProjectiveRatios.pairProjectiveEquiv
      (ConicFrameIndependentPairAction.coefficientEmbedding b)) =
        PairProjectiveRatios.pairProjectiveEquiv
          (ConicFrameIndependentPairAction.outerEmbedding b)
  rw [← PairProjectiveEquivariance.pairProjectiveEquiv_swap,
    ConicFrameIndependentPairAction.swap_coefficient]

theorem swap_secondEmbedding (b : GenericConicHead.L) :
    PairProjectiveEquivariance.projectivePairSwap (secondEmbedding b) = firstEmbedding b := by
  change PairProjectiveEquivariance.projectivePairSwap
    (PairProjectiveRatios.pairProjectiveEquiv
      (ConicFrameIndependentPairAction.outerEmbedding b)) =
        PairProjectiveRatios.pairProjectiveEquiv
          (ConicFrameIndependentPairAction.coefficientEmbedding b)
  rw [← PairProjectiveEquivariance.pairProjectiveEquiv_swap,
    ConicFrameIndependentPairAction.swap_outer]

/-- Original normalized frame units are exchanged by the original pair swap. -/
theorem swap_frameUnit_zero :
    Matrix.GeneralLinearGroup.map PairProjectiveEquivariance.projectivePairSwap.toRingHom
      (frameUnit 0) = frameUnit 1 := by
  apply Units.ext
  apply Matrix.ext
  intro i j
  exact swap_firstEmbedding (GenericConicHead.genericFrameUnit.val i j)

theorem swap_frameUnit_one :
    Matrix.GeneralLinearGroup.map PairProjectiveEquivariance.projectivePairSwap.toRingHom
      (frameUnit 1) = frameUnit 0 := by
  apply Units.ext
  apply Matrix.ext
  intro i j
  exact swap_secondEmbedding (GenericConicHead.genericFrameUnit.val i j)

theorem swap_frame_det_zero :
    PairProjectiveEquivariance.projectivePairSwap (frameUnit 0).val.det =
      (frameUnit 1).val.det := by
  have h := congrArg (fun U : Matrix.GeneralLinearGroup (Fin 3) B => U.val.det)
    swap_frameUnit_zero
  exact (PairProjectiveEquivariance.projectivePairSwap.map_det (frameUnit 0).val).trans h

theorem swap_frame_det_one :
    PairProjectiveEquivariance.projectivePairSwap (frameUnit 1).val.det =
      (frameUnit 0).val.det := by
  have h := congrArg (fun U : Matrix.GeneralLinearGroup (Fin 3) B => U.val.det)
    swap_frameUnit_one
  exact (PairProjectiveEquivariance.projectivePairSwap.map_det (frameUnit 1).val).trans h

theorem swap_twistScalar :
    PairProjectiveEquivariance.projectivePairSwap twistScalar.val = twistScalar.val⁻¹ := by
  rw [ConicFramedTwistEmbedding.twistScalar_val, map_div₀, map_pow, map_pow,
    swap_frame_det_zero, swap_frame_det_one, inv_div]

/-- An actual nonzero anti-invariant in the original pair coefficient field. -/
def oddTheta : B :=
  ConicFramedSLQuotient.coefficientEmbedding FrameHomRawOddCoordinates.antiInvariant

theorem oddTheta_ne_zero : oddTheta ≠ 0 :=
  (map_ne_zero ConicFramedSLQuotient.coefficientEmbedding).mpr
    FrameHomRawOddCoordinates.antiInvariant_ne_zero

theorem oddTheta_anti :
    PairProjectiveEquivariance.projectivePairSwap oddTheta = -oddTheta := by
  rw [oddTheta, ConicFramedSLQuotient.coefficientEmbedding_pairSwap]
  change ConicFramedSLQuotient.coefficientEmbedding
    (M9.FrameBundleDescent.nativeTranspose FrameHomRawOddCoordinates.antiInvariant) = _
  rw [FrameHomRawOddCoordinates.transpose_antiInvariant, map_neg]

/-- The genuine raw inverse/coefficient-swap automorphism. Its inversion
formula follows from the proved Cayley coordinate equivalence. -/
def ordinaryOdd : M ≃ₐ[ℂ] M where
  __ := M9.CayleyFixedField.graphInvolution B
    PairProjectiveEquivariance.projectivePairSwap.toRingEquiv oddTheta oddTheta_ne_zero
  commutes' c := by
    change M9.CayleyFixedField.graphInvolution B
      PairProjectiveEquivariance.projectivePairSwap.toRingEquiv oddTheta oddTheta_ne_zero
        (algebraMap ℂ M c) = algebraMap ℂ M c
    rw [IsScalarTower.algebraMap_apply ℂ B M,
      M9.CayleyFixedField.graphInvolution_constant]
    change algebraMap B M (PairProjectiveEquivariance.projectivePairSwap
      (algebraMap ℂ B c)) = algebraMap B M (algebraMap ℂ B c)
    rw [PairProjectiveEquivariance.projectivePairSwap.commutes]

theorem ordinaryOdd_constant (b : B) :
    ordinaryOdd (algebraMap B M b) =
      algebraMap B M (PairProjectiveEquivariance.projectivePairSwap b) :=
  M9.CayleyFixedField.graphInvolution_constant B
    PairProjectiveEquivariance.projectivePairSwap.toRingEquiv oddTheta oddTheta_ne_zero b

theorem ordinaryOdd_matrix : Z.map ordinaryOdd.toRingHom = Z⁻¹ :=
  M9.CayleyFixedField.graphInvolution_matrix B
    PairProjectiveEquivariance.projectivePairSwap.toRingEquiv oddTheta oddTheta_ne_zero oddTheta_anti

theorem ordinaryOdd_variable (ij : FiberIndex) :
    ordinaryOdd (Z ij.1 ij.2) = Z⁻¹ ij.1 ij.2 :=
  congrFun (congrFun ordinaryOdd_matrix ij.1) ij.2

theorem ordinaryOdd_rawUnit :
    Matrix.GeneralLinearGroup.map ordinaryOdd.toRingHom ConicFramedGammaAction.rawUnit =
      ConicFramedGammaAction.rawUnit⁻¹ := by
  apply Units.ext
  change Z.map ordinaryOdd.toRingHom = (ConicFramedGammaAction.rawUnit⁻¹).val
  rw [Matrix.GeneralLinearGroup.coe_inv]
  exact ordinaryOdd_matrix

/-- Determinant twist commutes with every actual field embedding. -/
theorem map_twist {K F : Type*} [Field K] [Field F] (φ : K →+* F)
    (A : M9.DeterminantTwist.Mat4 K) :
    (M9.DeterminantTwist.twist A).map φ = M9.DeterminantTwist.twist (A.map φ) := by
  have hd := φ.map_det A
  change φ A.det = (A.map φ).det at hd
  ext i j
  change φ (A.det⁻¹ * A i j) = (A.map φ).det⁻¹ * φ (A i j)
  rw [map_mul, map_inv₀, hd]

theorem ordinaryOdd_twist_matrix :
    (M9.DeterminantTwist.twist Z).map ordinaryOdd.toRingHom =
      (M9.DeterminantTwist.twist Z)⁻¹ := by
  rw [map_twist, ordinaryOdd_matrix,
    M9.DeterminantTwist.twist_inverse Z genericRawMatrix_det_ne_zero]

theorem J_inverse_matrix :
    (Z⁻¹).map J.toRingHom =
      algebraMap B M twistScalar.val⁻¹ • (M9.DeterminantTwist.twist Z)⁻¹ := by
  have h := M9.map_matrix_inverse J.toRingHom Z genericRawMatrix_det_ne_zero
  change (Z⁻¹).map J.toRingHom = (Z.map J.toRingHom)⁻¹ at h
  rw [ConicFramedTwistEmbedding.J_matrix] at h
  rw [h]
  let u : Mˣ := Units.map (algebraMap B M).toMonoidHom twistScalar
  have hu : u.val = algebraMap B M twistScalar.val := rfl
  have hi := Matrix.inv_smul' (A := M9.DeterminantTwist.twist Z) u
    (isUnit_iff_ne_zero.mpr (M9.DeterminantTwist.det_twist_ne_zero Z genericRawMatrix_det_ne_zero))
  change (u.val • M9.DeterminantTwist.twist Z)⁻¹ =
    algebraMap B M twistScalar.val⁻¹ • (M9.DeterminantTwist.twist Z)⁻¹
  simpa only [Units.smul_def, Units.val_inv_eq_inv_val, hu, map_inv₀] using hi

theorem ordinaryOdd_J_variable (ij : FiberIndex) :
    ordinaryOdd (J (Z ij.1 ij.2)) = J (ordinaryOdd (Z ij.1 ij.2)) := by
  rw [ConicFramedTwistEmbedding.J_variable, ordinaryOdd_variable, map_mul,
    ordinaryOdd_constant, swap_twistScalar]
  have hT := congrFun (congrFun ordinaryOdd_twist_matrix ij.1) ij.2
  have hJ := congrFun (congrFun J_inverse_matrix ij.1) ij.2
  change ordinaryOdd (M9.DeterminantTwist.twist Z ij.1 ij.2) =
    (M9.DeterminantTwist.twist Z)⁻¹ ij.1 ij.2 at hT
  change J (Z⁻¹ ij.1 ij.2) = algebraMap B M twistScalar.val⁻¹ *
    (M9.DeterminantTwist.twist Z)⁻¹ ij.1 ij.2 at hJ
  change algebraMap B M twistScalar.val⁻¹ *
    ordinaryOdd (M9.DeterminantTwist.twist Z ij.1 ij.2) = J (Z⁻¹ ij.1 ij.2)
  rw [hT]
  exact hJ.symm

/-- The actual original pair-swap/matrix-inverse map commutes with J on
the whole rational field, with no prescribed-action premise. -/
theorem ordinaryOdd_J (f : M) : ordinaryOdd (J f) = J (ordinaryOdd f) := by
  have h : ordinaryOdd.toRingHom.comp J.toRingHom = J.toRingHom.comp ordinaryOdd.toRingHom := by
    apply M9.ProjectiveNoName.rationalRingHom_ext B FiberIndex
    · intro b
      change ordinaryOdd (J (algebraMap B M b)) = J (ordinaryOdd (algebraMap B M b))
      rw [ConicFramedTwistEmbedding.J_constant, ordinaryOdd_constant,
        ConicFramedTwistEmbedding.J_constant]
    · exact ordinaryOdd_J_variable
  exact DFunLike.congr_fun h f

end M9Native.ConicFramedTwistAction
end
