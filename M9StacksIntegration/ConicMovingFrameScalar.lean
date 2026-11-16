module

public import M9StacksIntegration.ConicCellFrameNaturality

/-! Exact scalar behaviour of the actual moving head. This transfers the
proved generic head invertibility to the actual unnormalised deck frame. -/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000

open Matrix
open scoped Classical

namespace M9Native.ConicMovingFrameScalar

open M9.MovingDeterminantFrames GenericConicHead ConicFrameHeadMatrices

section Polynomial
variable {R : Type*} [CommRing R] [Algebra ℂ R]

theorem literalHead_smul (c : R) (F : Matrix (Fin 3) (Fin 3) R) :
    literalHead (c • F) = c^2 • literalHead F := by
  apply Matrix.ext
  intro i j
  change ConicFrame.symCoordinates ((c • F) * _ * (c • F).transpose) (Fin.natAdd 2 i) =
    c^2 * ConicFrame.symCoordinates (F * _ * F.transpose) (Fin.natAdd 2 i)
  simp only [Matrix.transpose_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul]
  rw [← pow_two, ConicFrame.symCoordinates_smul]
  rfl

end Polynomial

variable (K : Type*) [Field K] [Algebra ℂ K]

omit [Algebra ℂ K] in
theorem scalar_frame_value (a : Kˣ) (F : GL3 K) :
    (Matrix.GeneralLinearGroup.scalar (Fin 3) a * F).val = a.val • F.val := by
  change Matrix.scalar (Fin 3) a.val * F.val = _
  rw [Matrix.scalar_apply, ← Matrix.smul_one_eq_diagonal, Matrix.smul_mul, Matrix.one_mul]

theorem headMatrix_scalar (a : Kˣ) (F : GL3 K) :
    headMatrix K (Matrix.GeneralLinearGroup.scalar (Fin 3) a * F) =
      ((a^2 : Kˣ).val) • headMatrix K F := by
  calc
    headMatrix K (Matrix.GeneralLinearGroup.scalar (Fin 3) a * F) =
        literalHead (Matrix.GeneralLinearGroup.scalar (Fin 3) a * F).val :=
      headMatrix_eq_coefficients K (Matrix.GeneralLinearGroup.scalar (Fin 3) a * F)
    _ = literalHead (a.val • F.val) := congrArg literalHead (scalar_frame_value K a F)
    _ = a.val^2 • literalHead F.val := literalHead_smul a.val F.val
    _ = _ := (congrArg (fun M => ((a^2 : Kˣ).val) • M) (headMatrix_eq_coefficients K F)).symm

theorem headCondition_scalar_iff (a : Kˣ) (F : GL3 K) :
    IsUnit (headMatrix K (Matrix.GeneralLinearGroup.scalar (Fin 3) a * F)).det ↔
      IsUnit (headMatrix K F).det := by
  rw [headMatrix_scalar, Matrix.det_smul]
  have ha : (((a^2 : Kˣ).val)^4) ≠ 0 := pow_ne_zero 4 (Units.ne_zero (a^2))
  simp only [Fintype.card_fin, isUnit_iff_ne_zero, mul_ne_zero_iff]
  exact ⟨And.right, fun h => ⟨ha,h⟩⟩

end M9Native.ConicMovingFrameScalar
