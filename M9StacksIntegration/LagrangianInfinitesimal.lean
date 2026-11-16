module

public import M9StacksIntegration.LagrangianMatrixChart
public import Mathlib.Algebra.DualNumber
public import Mathlib.Algebra.MvPolynomial.Derivation
public import Mathlib.RingTheory.Kaehler.Polynomial

/-!
# Actual first-order deformations on the native LG matrix chart

The frozen native open chart is the quotient matrix `[I | A]` and its
actual exterior-square equation is `matrixSigma A = 0`. This file uses
the genuine dual-number ring and the actual chart coordinate algebra.
It identifies all lifts over a fixed chart point with symmetric
first-order matrices. The later global comparison must use these maps;
no tangent-bundle or canonical-line identity is assumed here.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
set_option maxRecDepth 4096

open Matrix Module
open scoped BigOperators

universe u

namespace M9Native.LagrangianInfinitesimal

open LagrangianMatrixChart

variable (R : Type u) [CommRing R]

/-- Symmetric matrices over an arbitrary commutative test ring. -/
def symmetricMatrices : Submodule R (Matrix (Fin 3) (Fin 3) R) where
  carrier := {A | A.transpose = A}
  zero_mem' := rfl
  add_mem' := by
    intro A B hA hB
    change (A+B).transpose=A+B
    rw [Matrix.transpose_add,hA,hB]
  smul_mem' := by
    intro r A hA
    change (r • A).transpose=r • A
    rw [Matrix.transpose_smul,hA]

/-- Recover a symmetric matrix from its six actual upper entries. -/
def upper (v : SymmetricEntry → R) : Matrix (Fin 3) (Fin 3) R :=
  fun i j => v (symmetricIndex (i,j))

omit [CommRing R] in
theorem upper_symmetric (v : SymmetricEntry → R) : (upper R v).transpose=upper R v := by
  ext i j
  exact congrArg v (symmetricIndex_swap j i)

/-- The actual six-entry linear coordinate equivalence. -/
def symmetricCoordinates : symmetricMatrices R ≃ₗ[R] (SymmetricEntry → R) where
  toFun A p := A.val p.val.1 p.val.2
  invFun v := ⟨upper R v,upper_symmetric R v⟩
  left_inv A := by
    apply Subtype.ext
    ext i j
    change A.val (symmetricIndex (i,j)).val.1 (symmetricIndex (i,j)).val.2=A.val i j
    by_cases h : i≤j
    · simp [symmetricIndex,h]
    · simpa [symmetricIndex,h] using congrFun (congrFun A.property i) j
  right_inv v := by
    funext p
    exact congrArg v (symmetricIndex_of_le p)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- A genuine matrix over the dual numbers, with value `A` and first
coefficient `B`. -/
def firstOrderMatrix (A B : Matrix (Fin 3) (Fin 3) R) :
    Matrix (Fin 3) (Fin 3) (DualNumber R) := fun i j => (A i j,B i j)

omit [CommRing R] in
@[simp] theorem firstOrderMatrix_fst (A B : Matrix (Fin 3) (Fin 3) R) (i j : Fin 3) :
    (firstOrderMatrix R A B i j).fst=A i j := rfl

omit [CommRing R] in
@[simp] theorem firstOrderMatrix_snd (A B : Matrix (Fin 3) (Fin 3) R) (i j : Fin 3) :
    (firstOrderMatrix R A B i j).snd=B i j := rfl

/-- The actual isotropy equation over `R[ε]`, including its constant and
first-order coefficients; there is no discarded higher-order term. -/
theorem firstOrderMatrix_isotropic_iff (A B : Matrix (Fin 3) (Fin 3) R) :
    matrixSigma (DualNumber R) (firstOrderMatrix R A B)=0 ↔
      A.transpose=A ∧ B.transpose=B := by
  rw [matrixSigma_eq_zero_iff]
  constructor
  · intro h
    constructor
    · ext i j
      exact congrArg TrivSqZeroExt.fst (congrFun (congrFun h i) j)
    · ext i j
      exact congrArg TrivSqZeroExt.snd (congrFun (congrFun h i) j)
  · rintro ⟨hA,hB⟩
    funext i j
    exact TrivSqZeroExt.ext (congrFun (congrFun hA i) j)
      (congrFun (congrFun hB i) j)

/-- All actual dual-number isotropic matrices reducing to the fixed
matrix `A`. -/
def IsotropicLift (A : symmetricMatrices R) :=
  {L : Matrix (Fin 3) (Fin 3) (DualNumber R) //
    (∀ i j,(L i j).fst=A.val i j) ∧ matrixSigma (DualNumber R) L=0}

/-- All lifts of an actual chart point are exactly symmetric tangent
matrices. This classifies every lift, rather than only constructing some. -/
def isotropicLiftEquiv (A : symmetricMatrices R) : IsotropicLift R A ≃ symmetricMatrices R where
  toFun L := ⟨fun i j => (L.val i j).snd,by
    have h := (matrixSigma_eq_zero_iff (DualNumber R) L.val).mp L.property.2
    ext i j
    exact congrArg TrivSqZeroExt.snd (congrFun (congrFun h i) j)⟩
  invFun B := ⟨firstOrderMatrix R A.val B.val,by
    constructor
    · intro i j; rfl
    · exact (firstOrderMatrix_isotropic_iff R A.val B.val).mpr ⟨A.property,B.property⟩⟩
  left_inv L := by
    apply Subtype.ext
    funext i j
    exact TrivSqZeroExt.ext (L.property.1 i j).symm rfl
  right_inv B := rfl

/-- The actual algebra map from the six-variable chart to the dual
numbers attached to a value and a first-order matrix. -/
def chartLiftHom (A B : symmetricMatrices R) : SymmetricRing R →ₐ[R] DualNumber R :=
  MvPolynomial.aeval (fun p =>
    (A.val p.down.val.1 p.down.val.2,B.val p.down.val.1 p.down.val.2))

@[simp] theorem chartLiftHom_X (A B : symmetricMatrices R) (p : ULift.{u} SymmetricEntry) :
    chartLiftHom R A B (MvPolynomial.X p)=
      (A.val p.down.val.1 p.down.val.2,B.val p.down.val.1 p.down.val.2) :=
  MvPolynomial.aeval_X _ _

/-- Its reduction is literally the original chart evaluation. -/
theorem chartLiftHom_reduction (A B : symmetricMatrices R) :
    (TrivSqZeroExt.fstHom R R R).comp (chartLiftHom R A B)=
      MvPolynomial.aeval (fun p : ULift.{u} SymmetricEntry =>
        A.val p.down.val.1 p.down.val.2) := by
  apply MvPolynomial.algHom_ext
  intro p
  simp

/-- Actual algebra lifts of the original chart evaluation. -/
def ChartLift (A : symmetricMatrices R) :=
  {φ : SymmetricRing R →ₐ[R] DualNumber R //
    (TrivSqZeroExt.fstHom R R R).comp φ=
      MvPolynomial.aeval (fun p : ULift.{u} SymmetricEntry =>
        A.val p.down.val.1 p.down.val.2)}

/-- The actual coordinate algebra represents every first-order chart
lift. This is the affine tangent functor in the native chart. -/
def chartLiftEquiv (A : symmetricMatrices R) : ChartLift R A ≃ symmetricMatrices R where
  toFun φ := (symmetricCoordinates R).symm
    (fun p => (φ.val (MvPolynomial.X (ULift.up p))).snd)
  invFun B := ⟨chartLiftHom R A B,chartLiftHom_reduction R A B⟩
  left_inv φ := by
    apply Subtype.ext
    apply MvPolynomial.algHom_ext
    intro p
    apply TrivSqZeroExt.ext
    · have h := congrArg (fun ψ : SymmetricRing R →ₐ[R] R => ψ (MvPolynomial.X p)) φ.property
      simpa using h.symm
    · simp [chartLiftHom,symmetricCoordinates,upper]
  right_inv B := by
    apply (symmetricCoordinates R).injective
    funext p
    simp [symmetricCoordinates,chartLiftHom,upper]

end M9Native.LagrangianInfinitesimal
