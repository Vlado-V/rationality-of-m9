module

public import M9StacksIntegration.MukaiPrimitiveDuality
public import M9StacksIntegration.MukaiConormalPencil

/-!
# Actual primitive-quotient coordinates for the conormal at the origin

The degree-one forms of the native primitive projective space are the
dual of the actual primitive third exterior power. The maps below use
that literal module, the actual exterior coefficient pairing, and the
actual quotient by sigma-wedges. They pin the quadratic mixed block `q`
and cubic block `b` without exchanging the two mixed blocks.
-/

@[expose] public noncomputable section

set_option maxHeartbeats 1400000
set_option maxRecDepth 4096

open Module Matrix exteriorPower
open scoped BigOperators

namespace M9Native.MukaiConormalPrimitive

open LagrangianField MukaiPrimitiveDuality

variable (K : Type*) [Field K]

/-- The genuine primitive quotient, in the native projective-form model. -/
def primitiveClass : Third K →ₗ[K] Module.Dual K (Primitive K) :=
  (restriction K).comp (coefficientDuality K).toLinearMap

theorem primitiveClass_wedgeSigma (v : V K) : primitiveClass K (wedgeSigma K v) = 0 := by
  ext w
  change coefficientDuality K (wedgeSigma K v) w.val = 0
  rw [contraction_dual_wedgeSigma]
  change vectorDuality K v (contraction K w.val) = 0
  rw [show contraction K w.val = 0 from w.property, map_zero]

/-- The actual ordered exterior indices of the quadratic mixed block. -/
def qIndices (i j : Fin 3) : Fin 3 ↪ Fin 6 where
  toFun := ![eIndex i, fIndex (nextOne j), fIndex (nextTwo j)]
  inj' := by
    fin_cases i <;> fin_cases j <;> decide

theorem primitiveClass_q_apply (i j : Fin 3) (w : Primitive K) :
    primitiveClass K (q K i j) w = qCoordinate K i j w.val := by
  have h := coefficientSharp_coordinate K (qIndices i j)
  change (coefficientDuality K).symm (coordinate3 K (qIndices i j)) = q K i j at h
  have hh := congrArg (coefficientDuality K) h
  rw [LinearEquiv.apply_symm_apply] at hh
  change coefficientDuality K (q K i j) w.val = _
  rw [← hh]
  rfl

variable [CharZero K]

theorem primitiveClass_q_coordinates (i j : Fin 3) (r : Coordinates K) :
    primitiveClass K (q K i j) (primitiveEquiv K r) = r.2.1.val i j := by
  rw [primitiveClass_q_apply, primitiveEquiv_val, qCoordinate_embedding]

/-- The two ordered mixed wedges become equal in the ACTUAL quotient
by sigma-wedges, not in a declared symmetric-coordinate surrogate. -/
theorem primitiveClass_q_swap (i j : Fin 3) :
    primitiveClass K (q K i j) = primitiveClass K (q K j i) := by
  ext w
  obtain ⟨r, rfl⟩ := (primitiveEquiv K).surjective w
  rw [primitiveClass_q_coordinates, primitiveClass_q_coordinates]
  exact congrFun (congrFun r.2.1.property j) i

def bIndices : Fin 3 ↪ Fin 6 where
  toFun := ![fIndex 0, fIndex 1, fIndex 2]
  inj' := by decide

theorem primitiveClass_b_coordinates (r : Coordinates K) :
    primitiveClass K (b K) (primitiveEquiv K r) = r.2.2.2 := by
  have h := coefficientSharp_coordinate K bIndices
  change (coefficientDuality K).symm (coordinate3 K bIndices) = b K at h
  have hh := congrArg (coefficientDuality K) h
  rw [LinearEquiv.apply_symm_apply] at hh
  change coefficientDuality K (b K) (primitiveEquiv K r).val = _
  rw [← hh, primitiveEquiv_val]
  exact bCoordinate_embedding K r

/-- The conormal-coordinate map is an actual linear map into the
degree-one forms of native primitive P13. -/
def conormalForm : MukaiConormalPencil.ConormalCoordinates K →ₗ[K]
    Module.Dual K (Primitive K) where
  toFun v := v.1 • primitiveClass K (b K) +
    ∑ i : Fin 3, ∑ j : Fin 3, v.2.val i j • primitiveClass K (q K i j)
  map_add' v w := by simp [add_smul, Finset.sum_add_distrib]; module
  map_smul' c v := by simp [Finset.smul_sum, smul_smul, smul_add]

theorem conormalForm_coordinates (v : MukaiConormalPencil.ConormalCoordinates K)
    (r : Coordinates K) :
    conormalForm K v (primitiveEquiv K r) =
      v.1 * r.2.2.2 + ∑ i : Fin 3, ∑ j : Fin 3, v.2.val i j * r.2.1.val i j := by
  simp [conormalForm, primitiveClass_b_coordinates, primitiveClass_q_coordinates]

end M9Native.MukaiConormalPrimitive
