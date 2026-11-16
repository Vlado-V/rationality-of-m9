module

public import M9StacksIntegration.MukaiQuarticCubic

/-!
# Exact first variation of the genuine exterior quartic

The trace polarization is the literal linear term of the quartic along
every affine line. All four coefficients are computed here, so calling
the diagonal cubic the gradient does not assume a derivative identity.
-/

@[expose] public noncomputable section
set_option maxHeartbeats 2400000
set_option maxRecDepth 4096

open Module

namespace M9Native.MukaiQuarticVariation

open MukaiQuarticHitchin MukaiQuarticCubic

variable (K : Type*) [Field K]

theorem polarOperator_symm (u v : Three K) : polarOperator K u v = polarOperator K v u := by
  simp only [polarOperator_apply]
  exact add_comm _ _

theorem hitchinOperator_add_smul (w t : Three K) (c : K) :
    hitchinOperator K (w + c • t) =
      hitchinOperator K w + c • polarOperator K w t + c^2 • hitchinOperator K t := by
  simp only [← mixedOperator_diagonal, map_add, LinearMap.add_apply,
    map_smul, LinearMap.smul_apply, polarOperator_apply, smul_add, smul_smul]
  module

theorem trace_square_pencil (A B C : Module.End K (DualSix K)) (c : K) :
    LinearMap.trace K (DualSix K)
      ((A + c • B + c^2 • C) * (A + c • B + c^2 • C)) =
      LinearMap.trace K (DualSix K) (A*A) +
      2*c*LinearMap.trace K (DualSix K) (A*B) +
      c^2*(LinearMap.trace K (DualSix K) (B*B) +
        2*LinearMap.trace K (DualSix K) (A*C)) +
      2*c^3*LinearMap.trace K (DualSix K) (B*C) +
      c^4*LinearMap.trace K (DualSix K) (C*C) := by
  simp only [add_mul, mul_add, smul_mul_assoc, mul_smul_comm,
    map_add, map_smul]
  rw [LinearMap.trace_mul_comm K B A, LinearMap.trace_mul_comm K C A,
    LinearMap.trace_mul_comm K C B]
  simp only [smul_eq_mul]
  ring

variable [CharZero K]

theorem cubic_diagonal (w t : Three K) :
    cubic K w w w t = (3 : K)⁻¹ * LinearMap.trace K (DualSix K)
      (hitchinOperator K w * polarOperator K w t) := by
  rw [cubic_apply, polarOperator_diagonal, smul_mul_assoc, map_smul]
  simp only [smul_eq_mul]
  field_simp
  ring

def mixedCoefficient (w t : Three K) : K :=
  (6 : K)⁻¹ * (LinearMap.trace K (DualSix K) (polarOperator K w t * polarOperator K w t) +
    2 * LinearMap.trace K (DualSix K) (hitchinOperator K w * hitchinOperator K t))

theorem quartic_line_expansion (w t : Three K) (c : K) :
    quartic K (w + c • t) = quartic K w + c * cubic K w w w t +
      c^2 * mixedCoefficient K w t + c^3 * cubic K t t t w + c^4 * quartic K t := by
  rw [quartic, hitchinOperator_add_smul, trace_square_pencil,
    cubic_diagonal, cubic_diagonal, polarOperator_symm K t w]
  rw [LinearMap.trace_mul_comm K (hitchinOperator K t) (polarOperator K w t)]
  unfold quartic mixedCoefficient
  field_simp
  ring

end M9Native.MukaiQuarticVariation
