module

public import M9StacksIntegration.LagrangianPluckerFirstJet
public import Mathlib.LinearAlgebra.Matrix.Adjugate

/-! The actual maximal-minor block identities over every commutative
ring.  The cyclic order is the original `(a,q,p,b)` Plucker convention. -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096

open Matrix Module
open scoped BigOperators

universe u

namespace M9Native.LagrangianBlockMinorQuadrics

open LagrangianPluckerFirstJet

variable (R : Type u) [CommRing R]

def leftBlock (M : Matrix (Fin 3) (Fin 6) R) : Matrix (Fin 3) (Fin 3) R :=
  fun i j => M i (j.castAdd 3)
def rightBlock (M : Matrix (Fin 3) (Fin 6) R) : Matrix (Fin 3) (Fin 3) R :=
  fun i j => M i (Fin.natAdd 3 j)

def aMinor (M : Matrix (Fin 3) (Fin 6) R) : R :=
  aCoordinate R (LagrangianRing.rowPlucker R M)
def bMinor (M : Matrix (Fin 3) (Fin 6) R) : R :=
  bCoordinate R (LagrangianRing.rowPlucker R M)
def pMinors (M : Matrix (Fin 3) (Fin 6) R) : Matrix (Fin 3) (Fin 3) R :=
  fun i j => pCoordinate R i j (LagrangianRing.rowPlucker R M)
def qMinors (M : Matrix (Fin 3) (Fin 6) R) : Matrix (Fin 3) (Fin 3) R :=
  fun i j => qCoordinate R i j (LagrangianRing.rowPlucker R M)

theorem aMinor_eq (M : Matrix (Fin 3) (Fin 6) R) : aMinor R M = (leftBlock R M).det := by
  simp [aMinor, aCoordinate, coordinate_rowPlucker, leftBlock, Matrix.det_fin_three]
  ring

theorem bMinor_eq (M : Matrix (Fin 3) (Fin 6) R) : bMinor R M = (rightBlock R M).det := by
  simp [bMinor, bCoordinate, coordinate_rowPlucker, rightBlock, Matrix.det_fin_three]
  ring

/-- Original cyclic single-f minors, with their genuine transpose. -/
theorem pMinors_eq (M : Matrix (Fin 3) (Fin 6) R) :
    pMinors R M = ((leftBlock R M).adjugate * rightBlock R M).transpose := by
  funext i j
  fin_cases i <;> fin_cases j <;>
    simp [pMinors, pCoordinate, coordinate_rowPlucker, nextOne, nextTwo,
      leftBlock, rightBlock, Matrix.adjugate_fin_three, Matrix.vecMul, dotProduct,
      Matrix.mul_apply, Fin.sum_univ_succ] <;> ring

/-- Original cyclic double-f minors, with their genuine transpose. -/
theorem qMinors_eq (M : Matrix (Fin 3) (Fin 6) R) :
    qMinors R M = ((rightBlock R M).adjugate * leftBlock R M).transpose := by
  funext i j
  fin_cases i <;> fin_cases j <;>
    simp [qMinors, qCoordinate, coordinate_rowPlucker, nextOne, nextTwo,
      leftBlock, rightBlock, Matrix.adjugate_fin_three, Matrix.vecMul, dotProduct,
      Matrix.mul_apply, Fin.sum_univ_succ] <;> ring

theorem adjugate_adjugate_three (A : Matrix (Fin 3) (Fin 3) R) :
    A.adjugate.adjugate = A.det • A := by
  simpa using Matrix.adjugate_adjugate A (by decide : Fintype.card (Fin 3) ≠ 1)

/-- The first actual homogeneous quadratic block identity. No isotropy,
field, invertibility, or rank hypothesis is needed for the minors. -/
theorem adjugate_pMinors (M : Matrix (Fin 3) (Fin 6) R) :
    (pMinors R M).adjugate = aMinor R M • qMinors R M := by
  rw [pMinors_eq, qMinors_eq, aMinor_eq, ← Matrix.adjugate_transpose,
    Matrix.adjugate_mul_distrib, adjugate_adjugate_three, Matrix.mul_smul, Matrix.transpose_smul]

theorem adjugate_qMinors (M : Matrix (Fin 3) (Fin 6) R) :
    (qMinors R M).adjugate = bMinor R M • pMinors R M := by
  rw [pMinors_eq, qMinors_eq, bMinor_eq, ← Matrix.adjugate_transpose,
    Matrix.adjugate_mul_distrib, adjugate_adjugate_three, Matrix.mul_smul, Matrix.transpose_smul]

theorem product_pMinors_qMinors (M : Matrix (Fin 3) (Fin 6) R) :
    pMinors R M * qMinors R M =
      (aMinor R M * bMinor R M) • (1 : Matrix (Fin 3) (Fin 3) R) := by
  have h : ((rightBlock R M).adjugate * leftBlock R M) *
      ((leftBlock R M).adjugate * rightBlock R M) =
      ((leftBlock R M).det * (rightBlock R M).det) • (1 : Matrix (Fin 3) (Fin 3) R) := by
    calc
      _ = (rightBlock R M).adjugate *
          ((leftBlock R M * (leftBlock R M).adjugate) * rightBlock R M) := by
        simp only [Matrix.mul_assoc]
      _ = _ := by
        rw [Matrix.mul_adjugate, Matrix.smul_mul, Matrix.one_mul,
          Matrix.mul_smul, Matrix.adjugate_mul, smul_smul]
  rw [pMinors_eq, qMinors_eq, ← Matrix.transpose_mul, h,
    Matrix.transpose_smul, Matrix.transpose_one, aMinor_eq, bMinor_eq]

end M9Native.LagrangianBlockMinorQuadrics
