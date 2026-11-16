module

public import M9StacksIntegration.LagrangianInfinitesimal
public import M9StacksIntegration.LagrangianRingCoordinates

/-!
# Literal Plücker coordinates and their first jets on the LG chart

The matrix is the actual quotient `[I | A]`. All coordinates below are
actual exterior-dual evaluations, with the cyclic `q` and `p` ordering
of the frozen primitive representation. In this ordering the graph is
`(1, adj(A)ᵀ, Aᵀ, det(A))`; no exchange of the two mixed blocks is hidden.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
set_option maxRecDepth 4096

open Matrix Module
open scoped BigOperators

universe u

namespace M9Native.LagrangianPluckerFirstJet

open LagrangianMatrixChart LagrangianInfinitesimal

variable (R : Type u) [CommRing R]

/-- The original quotient matrix whose first block is the identity. -/
def standard (A : Matrix (Fin 3) (Fin 3) R) : Matrix (Fin 3) (Fin 6) R :=
  !![1,0,0,A 0 0,A 0 1,A 0 2;
     0,1,0,A 1 0,A 1 1,A 1 2;
     0,0,1,A 2 0,A 2 1,A 2 2]

@[simp] theorem standard_e (A : Matrix (Fin 3) (Fin 3) R) (i j : Fin 3) :
    standard R A i (j.castAdd 3)=(if i=j then 1 else 0) := by
  fin_cases i <;> fin_cases j <;> simp [standard]

@[simp] theorem standard_f (A : Matrix (Fin 3) (Fin 3) R) (i j : Fin 3) :
    standard R A i (Fin.natAdd 3 j)=A i j := by
  fin_cases i <;> fin_cases j <;> simp [standard]

/-- The actual alternating exterior-coordinate functional on a third wedge. -/
def coordinate (i j k : Fin 6) : LagrangianRing.Third R →ₗ[R] R :=
  exteriorPower.pairingDual R (LagrangianRing.V R) 3
    (exteriorPower.ιMulti R 3 ![LinearMap.proj i,LinearMap.proj j,LinearMap.proj k])

theorem coordinate_rowPlucker (M : Matrix (Fin 3) (Fin 6) R) (i j k : Fin 6) :
    coordinate R i j k (LagrangianRing.rowPlucker R M)=
      M 0 i*M 1 j*M 2 k + M 0 j*M 1 k*M 2 i + M 0 k*M 1 i*M 2 j-
      M 0 i*M 1 k*M 2 j-M 0 j*M 1 i*M 2 k-M 0 k*M 1 j*M 2 i := by
  simp [coordinate,LagrangianRing.rowPlucker,Matrix.det_fin_three]
  ring

def nextOne : Fin 3 → Fin 3 := ![1,2,0]
def nextTwo : Fin 3 → Fin 3 := ![2,0,1]

def aCoordinate : LagrangianRing.Third R →ₗ[R] R := coordinate R 0 1 2
def bCoordinate : LagrangianRing.Third R →ₗ[R] R := coordinate R 3 4 5
def qCoordinate (i j : Fin 3) : LagrangianRing.Third R →ₗ[R] R :=
  coordinate R (i.castAdd 3) (Fin.natAdd 3 (nextOne j)) (Fin.natAdd 3 (nextTwo j))
def pCoordinate (i j : Fin 3) : LagrangianRing.Third R →ₗ[R] R :=
  coordinate R (Fin.natAdd 3 i) ((nextOne j).castAdd 3) ((nextTwo j).castAdd 3)

@[simp] theorem aCoordinate_standard (A : Matrix (Fin 3) (Fin 3) R) :
    aCoordinate R (LagrangianRing.rowPlucker R (standard R A))=1 := by
  simp [aCoordinate,coordinate_rowPlucker,standard]

@[simp] theorem bCoordinate_standard (A : Matrix (Fin 3) (Fin 3) R) :
    bCoordinate R (LagrangianRing.rowPlucker R (standard R A))=A.det := by
  simp [bCoordinate,coordinate_rowPlucker,standard,Matrix.det_fin_three]
  ring

@[simp] theorem pCoordinate_standard (A : Matrix (Fin 3) (Fin 3) R) (i j : Fin 3) :
    pCoordinate R i j (LagrangianRing.rowPlucker R (standard R A))=A j i := by
  fin_cases i <;> fin_cases j <;>
    simp [pCoordinate,coordinate_rowPlucker,standard,nextOne,nextTwo]

@[simp] theorem qCoordinate_standard (A : Matrix (Fin 3) (Fin 3) R) (i j : Fin 3) :
    qCoordinate R i j (LagrangianRing.rowPlucker R (standard R A))=A.adjugate j i := by
  fin_cases i <;> fin_cases j <;>
    simp [qCoordinate,coordinate_rowPlucker,standard,nextOne,nextTwo,Matrix.adjugate_fin_three] <;>
    ring

/-- The constant coordinate of the actual dual-number Plücker map. -/
@[simp] theorem firstJet_a (A B : Matrix (Fin 3) (Fin 3) R) :
    (aCoordinate (DualNumber R) (LagrangianRing.rowPlucker (DualNumber R)
      (standard (DualNumber R) (firstOrderMatrix R A B)))).snd=0 := by
  rw [aCoordinate_standard]
  rfl

/-- The actual first jet of the linear mixed block. -/
@[simp] theorem firstJet_p (A B : Matrix (Fin 3) (Fin 3) R) (i j : Fin 3) :
    (pCoordinate (DualNumber R) i j (LagrangianRing.rowPlucker (DualNumber R)
      (standard (DualNumber R) (firstOrderMatrix R A B)))).snd=B j i := by
  rw [pCoordinate_standard]
  rfl

/-- At the origin the quadratic mixed block has zero first jet. -/
@[simp] theorem firstJet_q_zero (B : Matrix (Fin 3) (Fin 3) R) (i j : Fin 3) :
    (qCoordinate (DualNumber R) i j (LagrangianRing.rowPlucker (DualNumber R)
      (standard (DualNumber R) (firstOrderMatrix R 0 B)))).snd=0 := by
  fin_cases i <;> fin_cases j <;>
    simp [qCoordinate_standard,Matrix.adjugate_fin_three,firstOrderMatrix]

/-- At the origin the cubic coordinate has zero first jet. -/
@[simp] theorem firstJet_b_zero (B : Matrix (Fin 3) (Fin 3) R) :
    (bCoordinate (DualNumber R) (LagrangianRing.rowPlucker (DualNumber R)
      (standard (DualNumber R) (firstOrderMatrix R 0 B)))).snd=0 := by
  simp [bCoordinate_standard,Matrix.det_fin_three,firstOrderMatrix]

section FieldModel

variable (K : Type u) [Field K]

theorem adjugate_symmetric (A : symmetricMatrices K) : A.val.adjugate.transpose=A.val.adjugate := by
  rw [Matrix.adjugate_transpose,A.property]

/-- The precise graph in the frozen primitive coordinate order. The
linear mixed block is `p`, and the quadratic block is `q`. -/
def graphPoint (A : symmetricMatrices K) : LagrangianField.Coordinates K :=
  (1,⟨A.val.adjugate,adjugate_symmetric K A⟩,⟨A.val,A.property⟩,A.val.det)

/-- Literal compatibility with the frozen fourteen-dimensional exterior
coordinate projection, rather than a newly assumed graph model. -/
theorem coordinateProjection_standard (A : symmetricMatrices K) :
    LagrangianField.coordinateProjection K
      (LagrangianRing.rowPlucker K (standard K A.val))=graphPoint K A := by
  apply Prod.ext
  · exact aCoordinate_standard K A.val
  apply Prod.ext
  · apply (LagrangianField.symmetric3Coordinates K).injective
    funext p
    change (LagrangianField.symmetric3Coordinates K)
      ((LagrangianField.symmetric3Coordinates K).symm _ ) p= _
    rw [LinearEquiv.apply_symm_apply]
    change qCoordinate K p.val.1 p.val.2
      (LagrangianRing.rowPlucker K (standard K A.val))=A.val.adjugate p.val.1 p.val.2
    rw [qCoordinate_standard]
    exact congrFun (congrFun (adjugate_symmetric K A) p.val.1) p.val.2
  apply Prod.ext
  · apply (LagrangianField.symmetric3Coordinates K).injective
    funext p
    change (LagrangianField.symmetric3Coordinates K)
      ((LagrangianField.symmetric3Coordinates K).symm _ ) p= _
    rw [LinearEquiv.apply_symm_apply]
    change pCoordinate K p.val.1 p.val.2
      (LagrangianRing.rowPlucker K (standard K A.val))=A.val p.val.1 p.val.2
    rw [pCoordinate_standard]
    exact congrFun (congrFun A.property p.val.1) p.val.2
  · exact bCoordinate_standard K A.val

end FieldModel

end M9Native.LagrangianPluckerFirstJet
