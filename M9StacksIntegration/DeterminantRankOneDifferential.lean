module

public import Mathlib.Algebra.DualNumber
public import Mathlib.Algebra.Algebra.Tower
public import Mathlib.LinearAlgebra.Matrix.Adjugate
public import Mathlib.LinearAlgebra.Matrix.Rank
public import Mathlib.RingTheory.Derivation.Basic
public import Mathlib.Tactic

/-!
# The genuine determinant differential vanishes at rank at most one

These are identities for the actual determinant over the genuine dual
numbers and for every algebraic derivation. The field-rank obstruction
is derived from actual two-by-two minors. This supplies the algebraic
singular-locus calculation used in Mukai, Curves and symmetric spaces II,
Section 4 immediately before Proposition 4.5. No geometric transversality
or semi-irreducibility premise is encoded here.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option maxRecDepth 4096

open Matrix
open scoped BigOperators

universe u v w

namespace M9Native.DeterminantRankOneDifferential

section Ring

variable {R : Type u} [CommRing R]

/-- The literal matrix with constant term A and first coefficient B. -/
def firstOrder (A B : Matrix (Fin 3) (Fin 3) R) :
    Matrix (Fin 3) (Fin 3) (DualNumber R) := fun i j => (A i j, B i j)

/-- The actual first coefficient of the determinant is its cofactor contraction. -/
theorem det_firstOrder_snd (A B : Matrix (Fin 3) (Fin 3) R) :
    ((firstOrder A B).det).snd =
      ∑ i : Fin 3, ∑ j : Fin 3, A.adjugate j i * B i j := by
  simp [firstOrder, Matrix.det_fin_three, Matrix.adjugate_fin_three,
    Fin.sum_univ_succ]
  ring

end Ring

section Field

variable {K : Type u} [Field K]

/-- Rank at most one forces every genuine cofactor to vanish. -/
theorem adjugate_eq_zero_of_rank_le_one (A : Matrix (Fin 3) (Fin 3) K)
    (hr : A.rank ≤ 1) : A.adjugate = 0 := by
  ext i j
  have hd : (A.submatrix j.succAbove i.succAbove).det = 0 := by
    by_contra hn
    have he := Matrix.rank_of_det_ne_zero hn
    have hl := Matrix.rank_submatrix_le A j.succAbove i.succAbove
    rw [he] at hl
    norm_num only [Fintype.card_fin] at hl
    omega
  rw [Matrix.adjugate_fin_succ_eq_det_submatrix, hd, mul_zero]
  rfl

/-- Every actual dual-number tangent direction has zero determinant first coefficient. -/
theorem det_firstOrder_snd_eq_zero_of_rank_le_one
    (A B : Matrix (Fin 3) (Fin 3) K) (hr : A.rank ≤ 1) :
    ((firstOrder A B).det).snd = 0 := by
  rw [det_firstOrder_snd, adjugate_eq_zero_of_rank_le_one A hr]
  simp

/-- A singular three-by-three determinant has fibre rank at most two. -/
theorem rank_le_two_of_det_eq_zero (A : Matrix (Fin 3) (Fin 3) K)
    (hd : A.det = 0) : A.rank ≤ 2 := by
  have hle := A.rank_le_card_width
  norm_num only [Fintype.card_fin] at hle
  have hne : A.rank ≠ 3 := by
    intro h
    have hs : Function.Surjective A.mulVec :=
      Matrix.mulVec_surjective_iff_rank_eq_card.mpr (by simpa using h)
    have hu : IsUnit A.det := (Matrix.isUnit_iff_isUnit_det A).mp
      (Matrix.mulVec_surjective_iff_isUnit.mp hs)
    exact hu.ne_zero hd
  omega

/-- Nonzero actual determinant first jet together with determinant zero gives rank exactly two. -/
theorem rank_eq_two_of_det_eq_zero_of_firstJet_ne_zero
    (A B : Matrix (Fin 3) (Fin 3) K) (hd : A.det = 0)
    (hj : ((firstOrder A B).det).snd ≠ 0) : A.rank = 2 := by
  have hle := rank_le_two_of_det_eq_zero A hd
  have hgt : ¬ A.rank ≤ 1 := fun h =>
    hj (det_firstOrder_snd_eq_zero_of_rank_le_one A B h)
  omega

end Field

section Derivation

variable {B : Type u} {R : Type v} {M : Type w}
  [CommRing B] [CommRing R] [AddCommGroup M]
  [Algebra B R] [Module R M] [Module B M]

/-- The genuine algebraic determinant differential, with arbitrary module coefficients. -/
theorem derivation_det (D : Derivation B R M) (A : Matrix (Fin 3) (Fin 3) R) :
    D A.det = ∑ i : Fin 3, ∑ j : Fin 3, A.adjugate j i • D (A i j) := by
  simp [Matrix.det_fin_three, Matrix.adjugate_fin_three, Fin.sum_univ_succ,
    Derivation.leibniz, smul_add, add_smul, sub_smul, mul_smul]
  module

variable {K : Type*} [Field K] [Algebra R K]

/-- After actual residue-field evaluation, all original cofactors vanish at rank at most one. -/
theorem mapped_adjugate_eq_zero_of_rank_map_le_one
    (A : Matrix (Fin 3) (Fin 3) R)
    (hr : (A.map (algebraMap R K)).rank ≤ 1) :
    A.adjugate.map (algebraMap R K) = 0 :=
  ((algebraMap R K).map_adjugate A).trans
    (adjugate_eq_zero_of_rank_le_one (A.map (algebraMap R K)) hr)

variable [Module K M] [IsScalarTower R K M]

/-- Every actual derivation with residue-field module coefficients kills the determinant
at a point where the original matrix has rank at most one. -/
theorem derivation_det_eq_zero_of_rank_map_le_one
    (D : Derivation B R M) (A : Matrix (Fin 3) (Fin 3) R)
    (hr : (A.map (algebraMap R K)).rank ≤ 1) : D A.det = 0 := by
  rw [derivation_det]
  apply Finset.sum_eq_zero
  intro i _
  apply Finset.sum_eq_zero
  intro j _
  have hc : algebraMap R K (A.adjugate j i) = 0 :=
    congrArg (fun C : Matrix (Fin 3) (Fin 3) K => C j i)
      (mapped_adjugate_eq_zero_of_rank_map_le_one (K := K) A hr)
  calc
    A.adjugate j i • D (A i j) =
        algebraMap R K (A.adjugate j i) • D (A i j) :=
      (IsScalarTower.algebraMap_smul K _ _).symm
    _ = 0 := by rw [hc, zero_smul]

/-- A nonzero genuine determinant differential rules out rank at most one. -/
theorem two_le_rank_map_of_derivation_det_ne_zero
    (D : Derivation B R M) (A : Matrix (Fin 3) (Fin 3) R) (hd : D A.det ≠ 0) :
    2 ≤ (A.map (algebraMap R K)).rank := by
  by_contra h
  have hr : (A.map (algebraMap R K)).rank ≤ 1 := by omega
  exact hd (derivation_det_eq_zero_of_rank_map_le_one (K := K) D A hr)

end Derivation

end M9Native.DeterminantRankOneDifferential
