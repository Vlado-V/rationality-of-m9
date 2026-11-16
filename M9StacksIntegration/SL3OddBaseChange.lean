module

public import M9StacksIntegration.PrimitiveMixedScalarExtension

@[expose] public section

/-! The actual odd stabilizer matrix is the coefficient extension of its
original complex matrix.  The proof uses the frozen actual trace-dual
normalization and its literal scalar-extension comparison.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096

open Matrix Module

namespace M9Native.SL3OddBaseChange

open PrimitiveMixedScalarExtension

variable (K : Type) [Field K] [Algebra ℂ K]

local instance : CharZero K := PrimitiveExtensionFieldBridge.charZero_extension K

abbrev odd : ReducedGraphAction.Stabilizer K := SemidirectProduct.inr M9.CentralSignQuotient.epsilon

theorem odd_mulVec_mixed (z : M9.PrimitiveBlockCoordinates.Mixed K) :
    (ReducedGraphAction.matrixRepresentation K (odd K)).val *ᵥ mixedCoordinates K z =
      mixedCoordinates K (z.2, z.1) := by
  rw [mixedCoordinates_eq_actualCoordinates, ReducedGraphAction.matrixRepresentation_actual,
    M9.PrimitiveTwistedReduced.dualSemidirectRepresentation_apply,
    LinearEquiv.symm_apply_apply, M9.PrimitiveTwistedReduced.mixedSemidirectRepresentation_inr_epsilon]
  rfl

/-- The same odd element is genuinely constant over every complex extension,
including the actual off-diagonal trace weights and original coordinate order. -/
theorem odd_matrix_map :
    (ReducedGraphAction.matrixRepresentation ℂ (odd ℂ)).val.map (algebraMap ℂ K) =
      (ReducedGraphAction.matrixRepresentation K (odd K)).val := by
  ext i j
  let z := (mixedCoordinates ℂ).symm (Pi.single j 1)
  have hzC : mixedCoordinates ℂ z = Pi.single j 1 :=
    (mixedCoordinates ℂ).apply_symm_apply _
  have hzK : mixedCoordinates K (symmetricMap K z.1, symmetricMap K z.2) = Pi.single j 1 := by
    rw [mixedCoordinates_map, hzC]
    funext a
    by_cases h : a = j <;> simp [h]
  have hC := odd_mulVec_mixed ℂ z
  rw [hzC, Matrix.mulVec_single_one] at hC
  have hK := odd_mulVec_mixed K (symmetricMap K z.1, symmetricMap K z.2)
  rw [hzK, Matrix.mulVec_single_one] at hK
  calc
    algebraMap ℂ K ((ReducedGraphAction.matrixRepresentation ℂ (odd ℂ)).val i j) =
        algebraMap ℂ K (mixedCoordinates ℂ (z.2,z.1) i) :=
      congrArg (algebraMap ℂ K) (congrFun hC i)
    _ = mixedCoordinates K (symmetricMap K z.2,symmetricMap K z.1) i :=
      (congrFun (mixedCoordinates_map K z.2 z.1) i).symm
    _ = (ReducedGraphAction.matrixRepresentation K (odd K)).val i j := (congrFun hK i).symm

end M9Native.SL3OddBaseChange
