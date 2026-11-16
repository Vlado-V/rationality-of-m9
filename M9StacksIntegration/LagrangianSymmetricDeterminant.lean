module
public import M9StacksIntegration.LagrangianSymmetricCongruence

/-! The determinant of the actual rank-six symmetric congruence map. -/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 40000000
set_option maxRecDepth 16384

open Matrix
open scoped BigOperators

namespace M9Native.LagrangianSymmetricCongruence

variable (R : Type*) [CommRing R]

/-- The determinant character of the actual symmetric congruence map. -/
theorem det_representation (P : Matrix (Fin 3) (Fin 3) R) :
    (representation R P).det=P.det^4 := by
  simp (maxSteps := 1000000) only [Matrix.det_succ_row_zero,Fin.sum_univ_succ,
    Matrix.det_unique,Matrix.submatrix_apply,representation,upperPair]
  norm_num [Fin.succAbove]
  ring

end M9Native.LagrangianSymmetricCongruence
