module

public import M9StacksIntegration.ConicPairMovingFrames
public import M9StacksIntegration.ProjectivePairSLFixedField

/-! The original SL3 action on the two actual normalized frame units.
The normalization factors are inverses of the actual chart00 denominators;
their nonvanishing follows from the genuine original raw-pair automorphism.
The first frame transforms by g inverse, the second by g transpose. -/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxRecDepth 4096
open scoped Classical Matrix
namespace M9Native.ConicPairFrameSLAction
open ConicPairMovingFrames (frameUnit firstEmbedding secondEmbedding)
open ProjectivePairSLFixedField (SL3 slActionHom)
open M9.FrameFieldElimination (firstFrame secondFrame pairActionHom
  pairAction_firstFrame pairAction_secondFrame)

abbrev B := ConicPairMovingFrames.B
abbrev PF := PairProjectiveRatios.PF
abbrev GL3B := Matrix.GeneralLinearGroup (Fin 3) B

def rawInclusion : B →ₐ[ℂ] PF where
  __ := B.subtype
  commutes' _ := rfl

def constantSL (g : SL3) : GL3B :=
  Matrix.GeneralLinearGroup.map (algebraMap ℂ B) (Matrix.SpecialLinearGroup.toGL g)

def constantTransposeSL (g : SL3) : GL3B :=
  Matrix.GeneralLinearGroup.map (algebraMap ℂ B) (Matrix.SpecialLinearGroup.toGL g.transpose)

theorem constantTransposeSL_val (g : SL3) :
    (constantTransposeSL g).val = (constantSL g).val.transpose := rfl

theorem slAction_coe (g : SL3) (z : B) :
    rawInclusion (slActionHom g z) =
      pairActionHom ℂ (Matrix.SpecialLinearGroup.toGL g) (rawInclusion z) := rfl

theorem frameUnit0_coe :
    (frameUnit 0).val.map rawInclusion.toRingHom =
      (firstFrame ℂ 0 0)⁻¹ • firstFrame ℂ := by
  change ConicFrameRationalGamma.genericFrame.map
    (rawInclusion.toRingHom.comp firstEmbedding.toRingHom) = _
  exact PairProjectiveEquivariance.genericFrame_map PairProjectiveEquivariance.firstBlock
    (firstFrame ℂ) (PairProjectiveRatios.firstFrame_ne_zero (0,0))
    PairProjectiveEquivariance.firstBlock_variable

theorem frameUnit1_coe :
    (frameUnit 1).val.map rawInclusion.toRingHom =
      (secondFrame ℂ 0 0)⁻¹ • secondFrame ℂ := by
  change ConicFrameRationalGamma.genericFrame.map
    (rawInclusion.toRingHom.comp secondEmbedding.toRingHom) = _
  exact PairProjectiveEquivariance.genericFrame_map PairProjectiveEquivariance.secondBlock
    (secondFrame ℂ) (PairProjectiveRatios.secondFrame_ne_zero (0,0))
    PairProjectiveEquivariance.secondBlock_variable

theorem constantSL_inverse_coe (g : SL3) :
    ((constantSL g)⁻¹).val.map rawInclusion.toRingHom =
      ((Matrix.SpecialLinearGroup.toGL g)⁻¹).val.map (algebraMap ℂ PF) := by
  rw [constantSL, ← map_inv]
  ext i j
  exact rawInclusion.commutes _

theorem constantTransposeSL_coe (g : SL3) :
    (constantTransposeSL g).val.map rawInclusion.toRingHom =
      (Matrix.SpecialLinearGroup.toGL g).val.transpose.map (algebraMap ℂ PF) := by
  ext i j
  exact rawInclusion.commutes _

def rawFirstMatrix (g : SL3) : Matrix (Fin 3) (Fin 3) PF :=
  ((Matrix.SpecialLinearGroup.toGL g)⁻¹).val.map (algebraMap ℂ PF) * firstFrame ℂ

def rawSecondMatrix (g : SL3) : Matrix (Fin 3) (Fin 3) PF :=
  (Matrix.SpecialLinearGroup.toGL g).val.transpose.map (algebraMap ℂ PF) * secondFrame ℂ

theorem rawFirstMatrix_action (g : SL3) :
    (firstFrame ℂ).map (pairActionHom ℂ (Matrix.SpecialLinearGroup.toGL g)).toRingHom =
      rawFirstMatrix g :=
  pairAction_firstFrame ℂ (Matrix.SpecialLinearGroup.toGL g)

theorem rawSecondMatrix_action (g : SL3) :
    (secondFrame ℂ).map (pairActionHom ℂ (Matrix.SpecialLinearGroup.toGL g)).toRingHom =
      rawSecondMatrix g :=
  pairAction_secondFrame ℂ (Matrix.SpecialLinearGroup.toGL g)

def firstLinear (g : SL3) : GL3B := (constantSL g)⁻¹ * frameUnit 0
def secondLinear (g : SL3) : GL3B := constantTransposeSL g * frameUnit 1

theorem firstLinear_coe (g : SL3) :
    (firstLinear g).val.map rawInclusion.toRingHom =
      (firstFrame ℂ 0 0)⁻¹ • rawFirstMatrix g := by
  change (((constantSL g)⁻¹).val * (frameUnit 0).val).map rawInclusion.toRingHom = _
  rw [Matrix.map_mul, constantSL_inverse_coe, frameUnit0_coe, Matrix.mul_smul]
  rfl

theorem secondLinear_coe (g : SL3) :
    (secondLinear g).val.map rawInclusion.toRingHom =
      (secondFrame ℂ 0 0)⁻¹ • rawSecondMatrix g := by
  change ((constantTransposeSL g).val * (frameUnit 1).val).map rawInclusion.toRingHom = _
  rw [Matrix.map_mul, constantTransposeSL_coe, frameUnit1_coe, Matrix.mul_smul]
  rfl

def firstDenominator (g : SL3) : B := (firstLinear g).val 0 0
def secondDenominator (g : SL3) : B := (secondLinear g).val 0 0

theorem rawFirstMatrix_pivot_ne_zero (g : SL3) : rawFirstMatrix g 0 0 ≠ 0 := by
  have h := congrFun (congrFun (rawFirstMatrix_action g) 0) 0
  change pairActionHom ℂ (Matrix.SpecialLinearGroup.toGL g) (firstFrame ℂ 0 0) = _ at h
  rw [← h]
  simpa only [map_zero] using
    (pairActionHom ℂ (Matrix.SpecialLinearGroup.toGL g)).injective.ne
      (PairProjectiveRatios.firstFrame_ne_zero (0,0))

theorem rawSecondMatrix_pivot_ne_zero (g : SL3) : rawSecondMatrix g 0 0 ≠ 0 := by
  have h := congrFun (congrFun (rawSecondMatrix_action g) 0) 0
  change pairActionHom ℂ (Matrix.SpecialLinearGroup.toGL g) (secondFrame ℂ 0 0) = _ at h
  rw [← h]
  simpa only [map_zero] using
    (pairActionHom ℂ (Matrix.SpecialLinearGroup.toGL g)).injective.ne
      (PairProjectiveRatios.secondFrame_ne_zero (0,0))

theorem firstDenominator_ne_zero (g : SL3) : firstDenominator g ≠ 0 := by
  have h := congrFun (congrFun (firstLinear_coe g) 0) 0
  change rawInclusion (firstDenominator g) =
    (firstFrame ℂ 0 0)⁻¹ * rawFirstMatrix g 0 0 at h
  intro hz
  exact (mul_ne_zero (inv_ne_zero (PairProjectiveRatios.firstFrame_ne_zero (0,0)))
    (rawFirstMatrix_pivot_ne_zero g)) (h.symm.trans (by rw [hz, map_zero]))

theorem secondDenominator_ne_zero (g : SL3) : secondDenominator g ≠ 0 := by
  have h := congrFun (congrFun (secondLinear_coe g) 0) 0
  change rawInclusion (secondDenominator g) =
    (secondFrame ℂ 0 0)⁻¹ * rawSecondMatrix g 0 0 at h
  intro hz
  exact (mul_ne_zero (inv_ne_zero (PairProjectiveRatios.secondFrame_ne_zero (0,0)))
    (rawSecondMatrix_pivot_ne_zero g)) (h.symm.trans (by rw [hz, map_zero]))

def normalizationUnit0 (g : SL3) : Bˣ := (Units.mk0 (firstDenominator g) (firstDenominator_ne_zero g))⁻¹
def normalizationUnit1 (g : SL3) : Bˣ := (Units.mk0 (secondDenominator g) (secondDenominator_ne_zero g))⁻¹

theorem normalizationUnit0_val (g : SL3) :
    (normalizationUnit0 g : B) = (firstDenominator g)⁻¹ := rfl

theorem normalizationUnit1_val (g : SL3) :
    (normalizationUnit1 g : B) = (secondDenominator g)⁻¹ := rfl

theorem firstFrame_action_entry (g : SL3) (i j : Fin 3) :
    rawInclusion (slActionHom g ((frameUnit 0).val i j)) =
      rawFirstMatrix g i j / rawFirstMatrix g 0 0 := by
  have hF := congrFun (congrFun frameUnit0_coe i) j
  change rawInclusion ((frameUnit 0).val i j) =
    (firstFrame ℂ 0 0)⁻¹ * firstFrame ℂ i j at hF
  have hA := congrFun (congrFun (rawFirstMatrix_action g) i) j
  have hP := congrFun (congrFun (rawFirstMatrix_action g) 0) 0
  change pairActionHom ℂ (Matrix.SpecialLinearGroup.toGL g) (firstFrame ℂ i j) = _ at hA
  change pairActionHom ℂ (Matrix.SpecialLinearGroup.toGL g) (firstFrame ℂ 0 0) = _ at hP
  rw [slAction_coe, hF, map_mul, map_inv₀, hA, hP]
  exact (div_eq_inv_mul _ _).symm

theorem secondFrame_action_entry (g : SL3) (i j : Fin 3) :
    rawInclusion (slActionHom g ((frameUnit 1).val i j)) =
      rawSecondMatrix g i j / rawSecondMatrix g 0 0 := by
  have hF := congrFun (congrFun frameUnit1_coe i) j
  change rawInclusion ((frameUnit 1).val i j) =
    (secondFrame ℂ 0 0)⁻¹ * secondFrame ℂ i j at hF
  have hA := congrFun (congrFun (rawSecondMatrix_action g) i) j
  have hP := congrFun (congrFun (rawSecondMatrix_action g) 0) 0
  change pairActionHom ℂ (Matrix.SpecialLinearGroup.toGL g) (secondFrame ℂ i j) = _ at hA
  change pairActionHom ℂ (Matrix.SpecialLinearGroup.toGL g) (secondFrame ℂ 0 0) = _ at hP
  rw [slAction_coe, hF, map_mul, map_inv₀, hA, hP]
  exact (div_eq_inv_mul _ _).symm

theorem scalarUnit_mul_val (u : Bˣ) (A : GL3B) :
    (Matrix.GeneralLinearGroup.scalar (Fin 3) u * A).val = (u : B) • A.val := by
  change Matrix.diagonal (fun _ : Fin 3 => (u : B)) * A.val = _
  apply Matrix.ext
  intro i j
  exact Matrix.diagonal_mul (fun _ : Fin 3 => (u : B)) A.val i j

theorem normalization_ratio {K : Type*} [Field K] (p d n : K) (hp : p ≠ 0) :
    (p⁻¹ * d)⁻¹ * (p⁻¹ * n) = n / d := by
  rw [mul_inv_rev, inv_inv]
  calc
    _ = d⁻¹ * (p * p⁻¹) * n := by ring
    _ = n / d := by rw [mul_inv_cancel₀ hp]; simp only [mul_one]; exact (div_eq_inv_mul _ _).symm

theorem firstFrame_image (g : SL3) :
    Matrix.GeneralLinearGroup.map (slActionHom g).toRingHom (frameUnit 0) =
      Matrix.GeneralLinearGroup.scalar (Fin 3) (normalizationUnit0 g) *
        (constantSL g)⁻¹ * frameUnit 0 := by
  rw [mul_assoc]
  change Matrix.GeneralLinearGroup.map (slActionHom g).toRingHom (frameUnit 0) =
    Matrix.GeneralLinearGroup.scalar (Fin 3) (normalizationUnit0 g) * firstLinear g
  apply Units.ext
  change (frameUnit 0).val.map (slActionHom g).toRingHom = _
  rw [scalarUnit_mul_val]
  apply Matrix.ext
  intro i j
  apply rawInclusion.injective
  change rawInclusion (slActionHom g ((frameUnit 0).val i j)) =
    rawInclusion ((normalizationUnit0 g : B) * (firstLinear g).val i j)
  rw [firstFrame_action_entry, map_mul, normalizationUnit0_val, map_inv₀]
  have hD := congrFun (congrFun (firstLinear_coe g) 0) 0
  have hT := congrFun (congrFun (firstLinear_coe g) i) j
  change rawInclusion (firstDenominator g) =
    (firstFrame ℂ 0 0)⁻¹ * rawFirstMatrix g 0 0 at hD
  change rawInclusion ((firstLinear g).val i j) =
    (firstFrame ℂ 0 0)⁻¹ * rawFirstMatrix g i j at hT
  rw [hD, hT]
  exact (normalization_ratio _ _ _ (PairProjectiveRatios.firstFrame_ne_zero (0,0))).symm

theorem secondFrame_image (g : SL3) :
    Matrix.GeneralLinearGroup.map (slActionHom g).toRingHom (frameUnit 1) =
      Matrix.GeneralLinearGroup.scalar (Fin 3) (normalizationUnit1 g) *
        constantTransposeSL g * frameUnit 1 := by
  rw [mul_assoc]
  change Matrix.GeneralLinearGroup.map (slActionHom g).toRingHom (frameUnit 1) =
    Matrix.GeneralLinearGroup.scalar (Fin 3) (normalizationUnit1 g) * secondLinear g
  apply Units.ext
  change (frameUnit 1).val.map (slActionHom g).toRingHom = _
  rw [scalarUnit_mul_val]
  apply Matrix.ext
  intro i j
  apply rawInclusion.injective
  change rawInclusion (slActionHom g ((frameUnit 1).val i j)) =
    rawInclusion ((normalizationUnit1 g : B) * (secondLinear g).val i j)
  rw [secondFrame_action_entry, map_mul, normalizationUnit1_val, map_inv₀]
  have hD := congrFun (congrFun (secondLinear_coe g) 0) 0
  have hT := congrFun (congrFun (secondLinear_coe g) i) j
  change rawInclusion (secondDenominator g) =
    (secondFrame ℂ 0 0)⁻¹ * rawSecondMatrix g 0 0 at hD
  change rawInclusion ((secondLinear g).val i j) =
    (secondFrame ℂ 0 0)⁻¹ * rawSecondMatrix g i j at hT
  rw [hD, hT]
  exact (normalization_ratio _ _ _ (PairProjectiveRatios.secondFrame_ne_zero (0,0))).symm

theorem constantSL_det (g : SL3) : Matrix.GeneralLinearGroup.det (constantSL g) = 1 := by
  rw [constantSL, Matrix.GeneralLinearGroup.map_det]
  have h : Matrix.GeneralLinearGroup.det (Matrix.SpecialLinearGroup.toGL g) = 1 := by
    apply Units.ext
    change g.val.det = 1
    exact g.property
  rw [h, map_one]

theorem constantTransposeSL_det (g : SL3) :
    Matrix.GeneralLinearGroup.det (constantTransposeSL g) = 1 :=
  constantSL_det g.transpose

theorem firstFrame_det_image (g : SL3) :
    slActionHom g (frameUnit 0).val.det =
      (normalizationUnit0 g : B)^3 * (frameUnit 0).val.det := by
  have h := congrArg Matrix.GeneralLinearGroup.det (firstFrame_image g)
  simp only [Matrix.GeneralLinearGroup.map_det, map_mul,
    Matrix.GeneralLinearGroup.det_scalar, Fintype.card_fin, map_inv,
    constantSL_det, inv_one, mul_one] at h
  exact congrArg Units.val h

theorem secondFrame_det_image (g : SL3) :
    slActionHom g (frameUnit 1).val.det =
      (normalizationUnit1 g : B)^3 * (frameUnit 1).val.det := by
  have h := congrArg Matrix.GeneralLinearGroup.det (secondFrame_image g)
  simp only [Matrix.GeneralLinearGroup.map_det, map_mul,
    Matrix.GeneralLinearGroup.det_scalar, Fintype.card_fin,
    constantTransposeSL_det, mul_one] at h
  exact congrArg Units.val h

end M9Native.ConicPairFrameSLAction
end
