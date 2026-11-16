module

public import M9StacksIntegration.LagrangianQuadricChartAlgebra
public import Mathlib.RingTheory.MvPolynomial.Homogeneous
public import Mathlib.RingTheory.Ideal.Prime

/-! Literal homogeneous equations in the native `(a,q,p,b)` block order.
The six-by-six adjugate blocks and the nine product entries give twenty-one
quadrics.  This file records polynomial identities, not a global LG ideal claim. -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096

open MvPolynomial Matrix
open scoped BigOperators

universe u

namespace M9Native.LagrangianHomogeneousQuadrics

open LagrangianMatrixChart
open LagrangianQuadricChartAlgebra (SymIndex)

abbrev CoordinateIndex := Unit ⊕ (SymIndex.{u} ⊕ (SymIndex.{u} ⊕ Unit))
abbrev QuadricIndex := SymIndex.{u} ⊕ (SymIndex.{u} ⊕ (Fin 3 × Fin 3))
abbrev AdmissibleIndex := Unit ⊕ (Unit ⊕ (Fin 3 ⊕ Fin 3))

variable (R : Type u) [CommRing R]
abbrev Ring := MvPolynomial CoordinateIndex.{u} R

def aVariable : Ring R := X (Sum.inl ())
def bVariable : Ring R := X (Sum.inr (Sum.inr (Sum.inr ())))
def qMatrix : Matrix (Fin 3) (Fin 3) (Ring R) :=
  fun i j => X (Sum.inr (Sum.inl (ULift.up (symmetricIndex (i,j)))))
def pMatrix : Matrix (Fin 3) (Fin 3) (Ring R) :=
  fun i j => X (Sum.inr (Sum.inr (Sum.inl (ULift.up (symmetricIndex (i,j))))))

def adjP (i j : Fin 3) : Ring R := (pMatrix R).adjugate i j - aVariable R * qMatrix R i j
def adjQ (i j : Fin 3) : Ring R := (qMatrix R).adjugate i j - bVariable R * pMatrix R i j
def product (i j : Fin 3) : Ring R :=
  (pMatrix R * qMatrix R) i j - aVariable R * bVariable R *
    (1 : Matrix (Fin 3) (Fin 3) (Ring R)) i j

def quadric : QuadricIndex.{u} → Ring R :=
  Sum.elim (fun ij => adjP R ij.down.val.1 ij.down.val.2)
    (Sum.elim (fun ij => adjQ R ij.down.val.1 ij.down.val.2)
      (fun ij => product R ij.1 ij.2))

theorem card_quadricIndex : Fintype.card QuadricIndex.{u} = 21 := by
  simp [QuadricIndex, SymIndex]

private theorem adjugate_entry_homogeneous (M : Matrix (Fin 3) (Fin 3) (Ring R))
    (hM : ∀ i j, (M i j).IsHomogeneous 1) (i j : Fin 3) :
    (M.adjugate i j).IsHomogeneous 2 := by
  fin_cases i <;> fin_cases j <;>
    simp only [Matrix.adjugate_fin_three, Matrix.of_apply]
  all_goals first
    | exact ((hM _ _).mul (hM _ _)).sub ((hM _ _).mul (hM _ _))
    | exact (((hM _ _).mul (hM _ _)).neg).add ((hM _ _).mul (hM _ _))

theorem adjP_homogeneous (i j : Fin 3) : (adjP R i j).IsHomogeneous 2 := by
  exact (adjugate_entry_homogeneous R (pMatrix R)
    (fun _ _ => MvPolynomial.isHomogeneous_X R _) i j).sub
      ((MvPolynomial.isHomogeneous_X R _).mul (MvPolynomial.isHomogeneous_X R _))

theorem adjQ_homogeneous (i j : Fin 3) : (adjQ R i j).IsHomogeneous 2 := by
  exact (adjugate_entry_homogeneous R (qMatrix R)
    (fun _ _ => MvPolynomial.isHomogeneous_X R _) i j).sub
      ((MvPolynomial.isHomogeneous_X R _).mul (MvPolynomial.isHomogeneous_X R _))

theorem product_homogeneous (i j : Fin 3) : (product R i j).IsHomogeneous 2 := by
  have hmul : ((pMatrix R * qMatrix R) i j).IsHomogeneous 2 := by
    change (∑ k : Fin 3, pMatrix R i k * qMatrix R k j) ∈
      MvPolynomial.homogeneousSubmodule CoordinateIndex.{u} R 2
    exact Submodule.sum_mem _ (fun k _ =>
      (MvPolynomial.isHomogeneous_X R _).mul (MvPolynomial.isHomogeneous_X R _))
  apply hmul.sub
  by_cases hij : i = j
  · simpa only [Matrix.one_apply, ite_eq_left hij, mul_one, aVariable, bVariable] using
      ((MvPolynomial.isHomogeneous_X R (Sum.inl ())).mul
        (MvPolynomial.isHomogeneous_X R (Sum.inr (Sum.inr (Sum.inr ())))))
  · simpa only [Matrix.one_apply, ite_eq_right hij, mul_zero] using
      (MvPolynomial.isHomogeneous_zero CoordinateIndex.{u} R 2)

theorem quadric_homogeneous (i : QuadricIndex.{u}) : (quadric R i).IsHomogeneous 2 := by
  cases i with
  | inl ij => exact adjP_homogeneous R _ _
  | inr i =>
    cases i with
    | inl ij => exact adjQ_homogeneous R _ _
    | inr ij => exact product_homogeneous R _ _

def admissibleCoordinate : AdmissibleIndex → Ring R :=
  Sum.elim (fun _ => aVariable R)
    (Sum.elim (fun _ => bVariable R)
      (Sum.elim (fun i => pMatrix R i i) (fun i => qMatrix R i i)))

def offPair : Fin 3 → Fin 3 × Fin 3 := ![(0,1),(0,2),(1,2)]
def complementIndex : Fin 3 → Fin 3 := ![2,1,0]

/-- These identities give the actual nilpotent-cover argument; they do
not replace an ideal by its radical in a scheme comparison. -/
theorem p_off_square (s : Fin 3) :
    (pMatrix R (offPair s).1 (offPair s).2)^2 =
      pMatrix R (offPair s).1 (offPair s).1 * pMatrix R (offPair s).2 (offPair s).2 -
        aVariable R * qMatrix R (complementIndex s) (complementIndex s) -
          adjP R (complementIndex s) (complementIndex s) := by
  fin_cases s <;>
    simp [offPair, complementIndex, adjP, Matrix.adjugate_fin_three, pMatrix,
      qMatrix, symmetricIndex] <;> ring

theorem q_off_square (s : Fin 3) :
    (qMatrix R (offPair s).1 (offPair s).2)^2 =
      qMatrix R (offPair s).1 (offPair s).1 * qMatrix R (offPair s).2 (offPair s).2 -
        bVariable R * pMatrix R (complementIndex s) (complementIndex s) -
          adjQ R (complementIndex s) (complementIndex s) := by
  fin_cases s <;>
    simp [offPair, complementIndex, adjQ, Matrix.adjugate_fin_three, pMatrix,
      qMatrix, symmetricIndex] <;> ring

theorem p_off_mem_prime (I : Ideal (Ring R)) (hI : I.IsPrime)
    (hQ : ∀ i, quadric R i ∈ I) (hA : ∀ i, admissibleCoordinate R i ∈ I)
    (s : Fin 3) : pMatrix R (offPair s).1 (offPair s).2 ∈ I := by
  apply hI.mem_of_pow_mem 2
  rw [p_off_square]
  apply I.sub_mem
  · apply I.sub_mem
    · exact I.mul_mem_right _ (hA (Sum.inr (Sum.inr (Sum.inl (offPair s).1))))
    · exact I.mul_mem_right _ (hA (Sum.inl ()))
  · exact hQ (Sum.inl (ULift.up ⟨(complementIndex s, complementIndex s), le_rfl⟩))

theorem q_off_mem_prime (I : Ideal (Ring R)) (hI : I.IsPrime)
    (hQ : ∀ i, quadric R i ∈ I) (hA : ∀ i, admissibleCoordinate R i ∈ I)
    (s : Fin 3) : qMatrix R (offPair s).1 (offPair s).2 ∈ I := by
  apply hI.mem_of_pow_mem 2
  rw [q_off_square]
  apply I.sub_mem
  · apply I.sub_mem
    · exact I.mul_mem_right _ (hA (Sum.inr (Sum.inr (Sum.inr (offPair s).1))))
    · exact I.mul_mem_right _ (hA (Sum.inr (Sum.inl ())))
  · exact hQ (Sum.inr (Sum.inl (ULift.up ⟨(complementIndex s, complementIndex s), le_rfl⟩)))

end M9Native.LagrangianHomogeneousQuadrics
