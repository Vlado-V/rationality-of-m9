module

public import M9StacksIntegration.MukaiConormalOrigin
public import M9StacksIntegration.MukaiThreeDimensionalBivectors
public import M9StacksIntegration.MukaiSingularConic

/-!
# Actual exterior coordinates of the Schubert cone

The forms below use the literal exterior coefficient pairing and the
actual primitive quotient. In particular the mixed quadratic block is
not supplied by a chosen identification with a symmetric matrix.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096

open Module Matrix
open scoped BigOperators

namespace M9Native.MukaiSchubertExpansion

open LagrangianField MukaiPrimitiveDuality MukaiConormalPrimitive

variable (K : Type*) [Field K]

theorem coefficientDuality_symm (u v : Third K) :
    coefficientDuality K u v = coefficientDuality K v u := by
  have h : (coefficientDuality K).toLinearMap.flip =
      (coefficientDuality K).toLinearMap := by
    apply (thirdBasis20 K).ext
    intro i
    apply (thirdBasis20 K).ext
    intro j
    simp [coefficientDuality, Basis.toDual_apply, eq_comm]
  exact LinearMap.congr_fun (LinearMap.congr_fun h v) u

def aIndices : Fin 3 ↪ Fin 6 where
  toFun := ![eIndex 0, eIndex 1, eIndex 2]
  inj' := by decide

def pIndices (i j : Fin 3) : Fin 3 ↪ Fin 6 where
  toFun := ![fIndex i, eIndex (nextOne j), eIndex (nextTwo j)]
  inj' := by fin_cases i <;> fin_cases j <;> decide

theorem coefficientDuality_a (w : Third K) :
    coefficientDuality K w (a K) = aCoordinate K w := by
  rw [coefficientDuality_symm]
  have h := congrArg (coefficientDuality K) (coefficientSharp_coordinate K aIndices)
  change coefficientDuality K ((coefficientDuality K).symm
    (coordinate3 K aIndices)) = coefficientDuality K (a K) at h
  rw [LinearEquiv.apply_symm_apply] at h
  rw [← h]
  rfl

theorem coefficientDuality_b (w : Third K) :
    coefficientDuality K w (b K) = bCoordinate K w := by
  rw [coefficientDuality_symm]
  have h := congrArg (coefficientDuality K) (coefficientSharp_coordinate K bIndices)
  change coefficientDuality K ((coefficientDuality K).symm
    (coordinate3 K bIndices)) = coefficientDuality K (b K) at h
  rw [LinearEquiv.apply_symm_apply] at h
  rw [← h]
  rfl

theorem coefficientDuality_q (w : Third K) (i j : Fin 3) :
    coefficientDuality K w (q K i j) = qCoordinate K i j w := by
  rw [coefficientDuality_symm]
  have h := congrArg (coefficientDuality K) (coefficientSharp_coordinate K (qIndices i j))
  change coefficientDuality K ((coefficientDuality K).symm
    (coordinate3 K (qIndices i j))) = coefficientDuality K (q K i j) at h
  rw [LinearEquiv.apply_symm_apply] at h
  rw [← h]
  rfl

theorem coefficientDuality_p (w : Third K) (i j : Fin 3) :
    coefficientDuality K w (p K i j) = pCoordinate K i j w := by
  rw [coefficientDuality_symm]
  have h := congrArg (coefficientDuality K) (coefficientSharp_coordinate K (pIndices i j))
  change coefficientDuality K ((coefficientDuality K).symm
    (coordinate3 K (pIndices i j))) = coefficientDuality K (p K i j) at h
  rw [LinearEquiv.apply_symm_apply] at h
  rw [← h]
  rfl

section
variable [CharZero K]

theorem primitiveClass_coordinates (w : Third K) (r : Coordinates K) :
    primitiveClass K w (primitiveEquiv K r) =
      r.1 * aCoordinate K w +
      (∑ i : Fin 3, ∑ j : Fin 3, r.2.1.val i j * qCoordinate K i j w) +
      (∑ i : Fin 3, ∑ j : Fin 3, r.2.2.1.val i j * pCoordinate K i j w) +
      r.2.2.2 * bCoordinate K w := by
  change coefficientDuality K w (coordinateEmbedding K r) = _
  simp [coordinateEmbedding, mixedQ, mixedP, coefficientDuality_a,
    coefficientDuality_b, coefficientDuality_q, coefficientDuality_p]

end

def blockVector (a z : Fin 3 → K) : V K := Fin.append a z

def cross (u v : Fin 3 → K) : Fin 3 → K :=
  ![u 1 * v 2 - u 2 * v 1,
    u 2 * v 0 - u 0 * v 2,
    u 0 * v 1 - u 1 * v 0]

theorem mixed_wedge_a (a z u v : Fin 3 → K) :
    aCoordinate K (wedge3 K (blockVector K a z)
      (blockVector K 0 u) (blockVector K 0 v)) = 0 := by
  simp [aCoordinate, coordinate_wedge3, blockVector, Fin.append, Fin.addCases]

theorem mixed_wedge_p (a z u v : Fin 3 → K) (i j : Fin 3) :
    pCoordinate K i j (wedge3 K (blockVector K a z)
      (blockVector K 0 u) (blockVector K 0 v)) = 0 := by
  fin_cases i <;> fin_cases j <;>
    simp [pCoordinate, coordinate_wedge3, blockVector, nextOne, nextTwo, eIndex, fIndex,
      Fin.append, Fin.addCases]

theorem mixed_wedge_q (a z u v : Fin 3 → K) (i j : Fin 3) :
    qCoordinate K i j (wedge3 K (blockVector K a z)
      (blockVector K 0 u) (blockVector K 0 v)) = a i * cross K u v j := by
  fin_cases i <;> fin_cases j <;>
    simp [qCoordinate, coordinate_wedge3, blockVector, nextOne, nextTwo, eIndex, fIndex,
      cross, Fin.append, Fin.addCases] <;> ring

theorem mixed_wedge_b (a z u v : Fin 3 → K) :
    bCoordinate K (wedge3 K (blockVector K a z)
      (blockVector K 0 u) (blockVector K 0 v)) =
      ∑ j : Fin 3, z j * cross K u v j := by
  simp [bCoordinate, coordinate_wedge3, blockVector, cross, Fin.sum_univ_three,
    Fin.append, Fin.addCases]
  ring

end M9Native.MukaiSchubertExpansion
