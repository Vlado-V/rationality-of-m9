module

public import M9StacksIntegration.LagrangianUniversalTriples
public import M9StacksIntegration.TupleEvaluationFiberRank
public import M9StacksIntegration.FieldBaseChangeRank
public import Mathlib.RingTheory.TensorProduct.Free
public import Mathlib.LinearAlgebra.Matrix.Rank

/-!
# Literal free-sheaf matrices on the actual residue fibres

The actual free-fibre bases are the residue classes of the actual
original generators. The matrix of every original free-sheaf map in
these bases is the original global matrix evaluated by the actual
local-to-residue ring map. Genuine field extension preserves its rank.
No fibre-comparison or rank-identification premise is used.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 2200000
set_option maxRecDepth 4096
set_option linter.style.haveILetI false

open AlgebraicGeometry CategoryTheory Module Opposite
open scoped BigOperators TensorProduct

universe u v

attribute [local implicit_reducible] TopCat.Sheaf CategoryTheory.sheafCompose
  AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme.Modules.Hom

namespace M9Native.FreeSheafMatrixFiberRank

open LagrangianMatrixChart TupleEvaluationFiber

variable {X : Scheme.{u}}

/-- Actual evaluation of global functions in the original residue field. -/
abbrev residueScalar (x : X) : Γ(X,⊤) →+* X.residueField x :=
  (X.residue x).hom.comp (X.presheaf.germ ⊤ x (by simp)).hom

/-- The original section value in the actual residue fibre, with its actual scalar map. -/
def globalValue (E : X.Modules) (x : X) :
    Γ(E,⊤) →ₛₗ[residueScalar x] Fiber E x := by
  letI := residueAlgebra x
  letI : RingHomCompTriple (X.presheaf.germ ⊤ x (by simp)).hom
      (algebraMap (X.presheaf.stalk x) (X.residueField x)) (residueScalar x) := ⟨rfl⟩
  exact (ExteriorEvaluation.stalkToFiber x (X.residueField x) E).comp
    (PresheafOfModules.germₛₗ (R := X.presheaf) E.val x ⊤ (by simp))

/-- Original free generators evaluate to the original genuine fibre basis. -/
theorem globalValue_freeBasis (n : ℕ) (x : X) (i : Fin n) :
    globalValue (freeOn X n) x (freeBasisSection X n i) = freeFiberBasis n x i :=
  (freeFiberBasis_apply n x i).symm

/-- The literal original global matrix, evaluated by the true residue map. -/
def matrixAt {m n : ℕ} (a : freeOn X m ⟶ freeOn X n) (x : X) :
    Matrix (Fin n) (Fin m) (X.residueField x) :=
  (Stacks.FreeSheafMatrix.toMatrix a).map (residueScalar x)

/-- The actual fibre-map values of the original generators have the literal matrix coefficients. -/
theorem fiberMap_basis {m n : ℕ} (a : freeOn X m ⟶ freeOn X n) (x : X) (j : Fin m) :
    inducedFiberMap a x (freeFiberBasis m x j) =
      ∑ i : Fin n, matrixAt a x i j • freeFiberBasis n x i := by
  letI := residueAlgebra x
  rw [freeFiberBasis_apply, inducedFiberMap_tmul_germ]
  change globalValue (freeOn X n) x (a.app ⊤ (freeBasisSection X m j)) = _
  rw [SplitMatrixGrassmannianNaturality.freeMap_column_eq_sum, map_sum]
  simp only [map_smulₛₗ, matrixAt, Matrix.map_apply]
  apply Finset.sum_congr rfl
  intro i _
  exact congrArg (fun v => residueScalar x (Stacks.FreeSheafMatrix.toMatrix a i j) • v)
    (globalValue_freeBasis n x i)

/-- The actual sheaf map has exactly its literal evaluated global matrix in the actual fibre bases. -/
theorem toMatrix_fiberMap {m n : ℕ} (a : freeOn X m ⟶ freeOn X n) (x : X) :
    LinearMap.toMatrix (freeFiberBasis m x) (freeFiberBasis n x) (inducedFiberMap a x) =
      matrixAt a x := by
  classical
  ext i j
  rw [LinearMap.toMatrix_apply, fiberMap_basis]
  simp [Finsupp.single_apply]

/-- The native original residue rank equals the literal evaluated matrix rank. -/
theorem mapRankAt_eq_rank_matrixAt {m n : ℕ} (a : freeOn X m ⟶ freeOn X n) (x : X) :
    MukaiSemiIrreducible.mapRankAt a x = (matrixAt a x).rank := by
  rw [← toMatrix_fiberMap a x,
    Matrix.rank_eq_finrank_range_toLin _ (freeFiberBasis n x) (freeFiberBasis m x),
    Matrix.toLin_toMatrix]
  rfl

/-- Genuine scalar extension of a field matrix preserves its actual rank. -/
theorem rank_map_field (K : Type u) (L : Type v) [Field K] [Field L] [Algebra K L]
    {m n : ℕ} (A : Matrix (Fin n) (Fin m) K) :
    (A.map (algebraMap K L)).rank = A.rank := by
  let b := Pi.basisFun K (Fin m)
  let c := Pi.basisFun K (Fin n)
  let g := Matrix.toLin b c A
  have hg : LinearMap.toMatrix (Algebra.TensorProduct.basis L b)
      (Algebra.TensorProduct.basis L c) (g.baseChange L) = A.map (algebraMap K L) := by
    rw [LinearMap.toMatrix_baseChange, LinearMap.toMatrix_toLin]
  rw [← hg, Matrix.rank_eq_finrank_range_toLin _
      (Algebra.TensorProduct.basis L c) (Algebra.TensorProduct.basis L b),
    Matrix.toLin_toMatrix]
  exact (FieldBaseChangeRank.finrank_range_baseChange K L g).trans
    (Matrix.rank_eq_finrank_range_toLin A c b).symm

/-- In particular every actual constant field matrix has its genuine original field rank. -/
theorem mapRankAt_ofMatrix_map (K : Type u) [Field K] (kappa : K →+* Γ(X,⊤))
    {m n : ℕ} (A : Matrix (Fin n) (Fin m) K) (x : X) :
    MukaiSemiIrreducible.mapRankAt (Stacks.FreeSheafMatrix.ofMatrix (X := X) (A.map kappa)) x =
      A.rank := by
  rw [mapRankAt_eq_rank_matrixAt, matrixAt, Stacks.FreeSheafMatrix.toMatrix_ofMatrix,
    Matrix.map_map]
  letI : Algebra K (X.residueField x) := ((residueScalar x).comp kappa).toAlgebra
  exact rank_map_field K (X.residueField x) A

end M9Native.FreeSheafMatrixFiberRank
