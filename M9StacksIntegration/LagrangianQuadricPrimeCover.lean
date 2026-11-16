module

public import M9StacksIntegration.LagrangianHomogeneousQuadrics

/-! The twenty-one literal quadrics force an eight-coordinate cover.
This uses prime ideals only to describe open covers; subsequent local
ideal comparisons must still retain the full, possibly nonreduced rings. -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open MvPolynomial Matrix

universe u

namespace M9Native.LagrangianQuadricPrimeCover

open LagrangianMatrixChart LagrangianHomogeneousQuadrics

variable (R : Type u) [CommRing R]

theorem pMatrix_symmetric : (pMatrix R).transpose = pMatrix R := by
  funext i j
  change (X (Sum.inr (Sum.inr (Sum.inl (ULift.up (symmetricIndex (j,i)))))) : LagrangianHomogeneousQuadrics.Ring R) = _
  rw [symmetricIndex_swap]
  rfl

theorem qMatrix_symmetric : (qMatrix R).transpose = qMatrix R := by
  funext i j
  change (X (Sum.inr (Sum.inl (ULift.up (symmetricIndex (j,i))))) : LagrangianHomogeneousQuadrics.Ring R) = _
  rw [symmetricIndex_swap]
  rfl

private theorem entries_mem_of_diagonal_and_off (I : Ideal (LagrangianHomogeneousQuadrics.Ring R))
    (M : Matrix (Fin 3) (Fin 3) (LagrangianHomogeneousQuadrics.Ring R)) (hM : M.transpose = M)
    (hd : ∀ i, M i i ∈ I) (ho : ∀ s, M (offPair s).1 (offPair s).2 ∈ I)
    (i j : Fin 3) : M i j ∈ I := by
  fin_cases i <;> fin_cases j
  · exact hd 0
  · exact ho 0
  · exact ho 1
  · exact (congrFun (congrFun hM (1 : Fin 3)) (0 : Fin 3)) ▸ ho 0
  · exact hd 1
  · exact ho 2
  · exact (congrFun (congrFun hM (2 : Fin 3)) (0 : Fin 3)) ▸ ho 1
  · exact (congrFun (congrFun hM (2 : Fin 3)) (1 : Fin 3)) ▸ ho 2
  · exact hd 2

/-- An actual prime containing the quadrics and all eight admissible
coordinates contains every one of the original fourteen variables. -/
theorem all_variables_mem_prime (I : Ideal (LagrangianHomogeneousQuadrics.Ring R)) (hI : I.IsPrime)
    (hQ : ∀ i, quadric R i ∈ I) (hA : ∀ i, admissibleCoordinate R i ∈ I)
    (j : CoordinateIndex.{u}) : X j ∈ I := by
  cases j with
  | inl j => cases j; exact hA (Sum.inl ())
  | inr j =>
    cases j with
    | inl ij =>
      have h := entries_mem_of_diagonal_and_off R I (qMatrix R) (qMatrix_symmetric R)
        (fun i => hA (Sum.inr (Sum.inr (Sum.inr i)))) (q_off_mem_prime R I hI hQ hA)
        ij.down.val.1 ij.down.val.2
      have hi : symmetricIndex (ij.down.val.1, ij.down.val.2) = ij.down :=
        symmetricIndex_of_le ij.down
      simpa only [qMatrix, hi, ULift.up_down] using h
    | inr j =>
      cases j with
      | inl ij =>
        have h := entries_mem_of_diagonal_and_off R I (pMatrix R) (pMatrix_symmetric R)
          (fun i => hA (Sum.inr (Sum.inr (Sum.inl i)))) (p_off_mem_prime R I hI hQ hA)
          ij.down.val.1 ij.down.val.2
        have hi : symmetricIndex (ij.down.val.1, ij.down.val.2) = ij.down :=
          symmetricIndex_of_le ij.down
        simpa only [pMatrix, hi, ULift.up_down] using h
      | inr j => cases j; exact hA (Sum.inr (Sum.inl ()))

theorem exists_admissible_not_mem (I : Ideal (LagrangianHomogeneousQuadrics.Ring R)) (hI : I.IsPrime)
    (hQ : ∀ i, quadric R i ∈ I) (hX : ¬∀ j : CoordinateIndex.{u}, X j ∈ I) :
    ∃ i, admissibleCoordinate R i ∉ I := by
  by_contra h
  have hA : ∀ i, admissibleCoordinate R i ∈ I := by simpa only [not_exists, not_not] using h
  exact hX (all_variables_mem_prime R I hI hQ hA)

end M9Native.LagrangianQuadricPrimeCover
