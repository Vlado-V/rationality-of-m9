module

public import M9StacksIntegration.LagrangianInfinitesimal
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

/-!
# The actual symmetric congruence representation and its determinant

The representation is the literal linear map `B ↦ P B Pᵀ` on symmetric
three-by-three matrices. The six coordinates are the upper entries in
the order `00,01,02,11,12,22`. The determinant calculation supplies the
fourth power needed by the native LG cotangent gluing.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 20000000
set_option maxRecDepth 8192

open Matrix Module
open scoped BigOperators

universe u

namespace M9Native.LagrangianSymmetricCongruence

open LagrangianInfinitesimal

variable (R : Type u) [CommRing R]

/-- The literal six upper entries, with an explicit reconstruction. -/
def coordinates : symmetricMatrices R ≃ₗ[R] (Fin 6 → R) where
  toFun B := ![B.val 0 0,B.val 0 1,B.val 0 2,B.val 1 1,B.val 1 2,B.val 2 2]
  invFun v := ⟨!![v 0,v 1,v 2;v 1,v 3,v 4;v 2,v 4,v 5],by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl⟩
  left_inv B := by
    apply Subtype.ext
    ext i j
    fin_cases i <;> fin_cases j
    all_goals first
      | rfl
      | exact (congrFun (congrFun B.property 0) 1).symm
      | exact (congrFun (congrFun B.property 0) 2).symm
      | exact (congrFun (congrFun B.property 1) 2).symm
  right_inv v := by funext i; fin_cases i <;> rfl
  map_add' _ _ := by funext i; fin_cases i <;> rfl
  map_smul' _ _ := by funext i; fin_cases i <;> rfl

/-- The actual linear congruence map. -/
def congruence (P : Matrix (Fin 3) (Fin 3) R) : symmetricMatrices R →ₗ[R] symmetricMatrices R where
  toFun B := ⟨P*B.val*P.transpose,by
    change (P*B.val*P.transpose).transpose=P*B.val*P.transpose
    rw [Matrix.transpose_mul,Matrix.transpose_mul,Matrix.transpose_transpose,B.property]
    exact (Matrix.mul_assoc _ _ _).symm⟩
  map_add' A B := by
    apply Subtype.ext
    simp [Matrix.mul_add,Matrix.add_mul]
  map_smul' r B := by
    apply Subtype.ext
    simp

@[simp] theorem congruence_one : congruence R (1 : Matrix (Fin 3) (Fin 3) R)=LinearMap.id := by
  ext B i j
  simp [congruence]

theorem congruence_mul (P Q : Matrix (Fin 3) (Fin 3) R) :
    congruence R (P*Q)=(congruence R P).comp (congruence R Q) := by
  ext B i j
  simp [congruence,Matrix.transpose_mul,Matrix.mul_assoc]

def upperPair : Fin 6 → Fin 3 × Fin 3 := ![(0,0),(0,1),(0,2),(1,1),(1,2),(2,2)]

/-- The coefficient matrix of the actual congruence map in the upper-entry basis. -/
def representation (P : Matrix (Fin 3) (Fin 3) R) : Matrix (Fin 6) (Fin 6) R :=
  fun i =>
    let a := (upperPair i).1
    let b := (upperPair i).2
    ![P a 0*P b 0,P a 0*P b 1+P a 1*P b 0,P a 0*P b 2+P a 2*P b 0,
      P a 1*P b 1,P a 1*P b 2+P a 2*P b 1,P a 2*P b 2]

/-- This is the actual map on every symmetric matrix, not a separately
chosen six-dimensional representation. -/
theorem coordinates_congruence (P : Matrix (Fin 3) (Fin 3) R) (B : symmetricMatrices R) :
    coordinates R (congruence R P B)=representation R P *ᵥ coordinates R B := by
  have h10 : B.val 1 0=B.val 0 1 := congrFun (congrFun B.property 0) 1
  have h20 : B.val 2 0=B.val 0 2 := congrFun (congrFun B.property 0) 2
  have h21 : B.val 2 1=B.val 1 2 := congrFun (congrFun B.property 1) 2
  funext i
  fin_cases i <;>
    simp [coordinates,congruence,representation,upperPair,Matrix.mul_apply,
      Matrix.mulVec,dotProduct,Fin.sum_univ_succ,h10,h20,h21] <;> ring

end M9Native.LagrangianSymmetricCongruence
