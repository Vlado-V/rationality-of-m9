module

public import M9StacksIntegration.LagrangianBlockMinorQuadrics
public import M9StacksIntegration.LagrangianHomogeneousQuadrics

/-! The actual primitive row equation makes the cyclic maximal-minor
blocks symmetric over arbitrary coefficient rings. -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096

open Matrix Module

universe u

namespace M9Native.LagrangianBlockMinorSymmetry

open LagrangianBlockMinorQuadrics
open LagrangianHomogeneousQuadrics (offPair complementIndex)

variable (R : Type u) [CommRing R]

def rowContraction (M : Matrix (Fin 3) (Fin 6) R) : Fin 6 → R :=
  LagrangianRing.contraction R (LagrangianRing.rowPlucker R M)

def epsilon : Fin 3 → R := ![1,-1,1]

theorem p_off_skew (M : Matrix (Fin 3) (Fin 6) R) (s : Fin 3) :
    pMinors R M (offPair s).1 (offPair s).2 - pMinors R M (offPair s).2 (offPair s).1 =
      epsilon R s * rowContraction R M ((complementIndex s).castAdd 3) := by
  fin_cases s <;>
    simp only [pMinors, LagrangianPluckerFirstJet.pCoordinate,
      LagrangianPluckerFirstJet.coordinate_rowPlucker]
  all_goals
    simp [epsilon, offPair, complementIndex, LagrangianPluckerFirstJet.nextOne,
      LagrangianPluckerFirstJet.nextTwo, rowContraction, LagrangianRing.rowPlucker,
      LagrangianRing.contraction_ιMulti, LagrangianRing.contractionFormula,
      LagrangianRing.tripleContract, LagrangianRing.omega_apply, LagrangianRing.omegaValue,
      LagrangianRing.eIndex, LagrangianRing.fIndex, Fin.sum_univ_succ] <;> ring

theorem q_off_skew (M : Matrix (Fin 3) (Fin 6) R) (s : Fin 3) :
    qMinors R M (offPair s).1 (offPair s).2 - qMinors R M (offPair s).2 (offPair s).1 =
      -(epsilon R s) * rowContraction R M (Fin.natAdd 3 (complementIndex s)) := by
  fin_cases s <;>
    simp only [qMinors, LagrangianPluckerFirstJet.qCoordinate,
      LagrangianPluckerFirstJet.coordinate_rowPlucker]
  all_goals
    simp [epsilon, offPair, complementIndex, LagrangianPluckerFirstJet.nextOne,
      LagrangianPluckerFirstJet.nextTwo, rowContraction, LagrangianRing.rowPlucker,
      LagrangianRing.contraction_ιMulti, LagrangianRing.contractionFormula,
      LagrangianRing.tripleContract, LagrangianRing.omega_apply, LagrangianRing.omegaValue,
      LagrangianRing.eIndex, LagrangianRing.fIndex, Fin.sum_univ_succ] <;> ring

theorem rowContraction_eq_zero (M : Matrix (Fin 3) (Fin 6) R)
    (hM : ∀ i j, LagrangianRing.omega R (M i) (M j) = 0) : rowContraction R M = 0 := by
  rw [rowContraction, LagrangianRing.rowPlucker, LagrangianRing.contraction_ιMulti]
  simp only [LagrangianRing.contractionFormula, LagrangianRing.tripleContract,
    hM, zero_smul, sub_zero, add_zero]

theorem pMinors_symmetric (M : Matrix (Fin 3) (Fin 6) R)
    (hM : ∀ i j, LagrangianRing.omega R (M i) (M j) = 0) :
    (pMinors R M).transpose = pMinors R M := by
  have h (s : Fin 3) : pMinors R M (offPair s).1 (offPair s).2 =
      pMinors R M (offPair s).2 (offPair s).1 := by
    apply sub_eq_zero.mp
    rw [p_off_skew, rowContraction_eq_zero R M hM]
    simp
  funext i j
  fin_cases i <;> fin_cases j
  · rfl
  · exact (h 0).symm
  · exact (h 1).symm
  · exact h 0
  · rfl
  · exact (h 2).symm
  · exact h 1
  · exact h 2
  · rfl

theorem qMinors_symmetric (M : Matrix (Fin 3) (Fin 6) R)
    (hM : ∀ i j, LagrangianRing.omega R (M i) (M j) = 0) :
    (qMinors R M).transpose = qMinors R M := by
  have h (s : Fin 3) : qMinors R M (offPair s).1 (offPair s).2 =
      qMinors R M (offPair s).2 (offPair s).1 := by
    apply sub_eq_zero.mp
    rw [q_off_skew, rowContraction_eq_zero R M hM]
    simp
  funext i j
  fin_cases i <;> fin_cases j
  · rfl
  · exact (h 0).symm
  · exact (h 1).symm
  · exact h 0
  · rfl
  · exact (h 2).symm
  · exact h 1
  · exact h 2
  · rfl

end M9Native.LagrangianBlockMinorSymmetry
