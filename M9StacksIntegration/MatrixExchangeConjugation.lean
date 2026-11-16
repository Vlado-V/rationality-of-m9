module

public import M9StacksIntegration.FrameHomRawOddCoordinates

/-! The matrix identity used for genuine paired-basis exchange. -/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false

namespace M9Native.MatrixExchangeConjugation

variable {n : Type*} [Fintype n] [DecidableEq n]
variable {F : Type*} [Field F]

/-- Exchange-paired changes of bases transport literal matrix inversion to
literal matrix inversion. The matrices are actual units. -/
theorem inverse_in_paired_bases (τ : F →+* F)
    (L R : Matrix.GeneralLinearGroup n F) (X : Matrix n n F)
    (hL : L.val.map τ = R.val) (hR : R.val.map τ = L.val)
    (hX : X.map τ = X⁻¹) (hdet : IsUnit X.det) :
    ((R⁻¹).val * X * L.val).map τ = ((R⁻¹).val * X * L.val)⁻¹ := by
  let μ : Matrix n n F →+* Matrix n n F := τ.mapMatrix
  have hU : Units.map μ.toMonoidHom R = L := Units.ext hR
  have hRI : ((R⁻¹).val).map τ = (L⁻¹).val := by
    change (Units.map μ.toMonoidHom R⁻¹).val = (L⁻¹).val
    rw [map_inv,hU]
  have hm : ((R⁻¹).val * X * L.val).map τ = (L⁻¹).val * X⁻¹ * R.val := by
    change μ ((R⁻¹).val * X * L.val) = _
    rw [map_mul,map_mul]
    change ((R⁻¹).val).map τ * X.map τ * L.val.map τ = _
    rw [hRI,hX,hL]
  rw [hm]
  symm
  apply Matrix.inv_eq_left_inv
  calc
    ((L⁻¹).val * X⁻¹ * R.val) * ((R⁻¹).val * X * L.val) =
        (L⁻¹).val * X⁻¹ * (R.val * (R⁻¹).val) * X * L.val := by noncomm_ring
    _ = (L⁻¹).val * (X⁻¹ * X) * L.val := by
      rw [R.mul_inv]
      noncomm_ring
    _ = 1 := by
      rw [Matrix.nonsing_inv_mul X hdet]
      simpa only [mul_one] using L.inv_mul

end M9Native.MatrixExchangeConjugation
